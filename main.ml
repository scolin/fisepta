open Cil
open Pretty

let input_file = ref ""

let set_input_file s =
  input_file := s

let do_debug = ref false

let debug s = if !do_debug then print_endline ("[debug] " ^ s)
let info s = print_endline ("[info]  " ^ s)
let warn s = print_endline ("[warn]  " ^ s)
let error s = prerr_endline ("[error] " ^ s)
let fatal s = prerr_endline ("[fatal] " ^ s)



(**************************************************************************************************)


let (seenFunctions: (string, fundec) Hashtbl.t) = Hashtbl.create 1009


class findFunctionsClass =
object(self)
  inherit Cil.nopCilVisitor

  method vglob g =
    match g with
    | GFun(fundec,_) ->
       let () =
         try
           let found_vi = Hashtbl.find seenFunctions fundec.svar.vname in
           if found_vi.svar.vid <> fundec.svar.vid
           then
             error ("findFunctionClass, definition: function " ^ fundec.svar.vname ^ " exists under two UIDs."
                    ^ " This means either that there exists conflicting declarations of it"
                    ^ " (e.g. declared twice as an inline function, or the prototype"
                    ^ " has arguments of different types or numbers)."
                    ^ " Please check the merge errors in the log directory.")
         with Not_found -> Hashtbl.add seenFunctions fundec.svar.vname fundec
       in
       SkipChildren
    | _ -> SkipChildren

end


let update_seenFunctions file =
  let findFunctions = new findFunctionsClass in
  visitCilFile findFunctions file



type var_category =
  (* x, place of x among the formals, f (as a varinfo in case f is an extern function *)
  | FormalVar of string * int * varinfo
  | LocalVar of varinfo * fundec
  | GlobalVar of varinfo

type refinfo =
  | RealVariable of var_category
  | TempVariable of varinfo
  | ReturnVar of varinfo (* not a fundec, for functions that have no body *)


let type_of_refinfo r =
  match r with
  | RealVariable(FormalVar(s,i,f)) ->
     begin
       match unrollType f.vtype with
       | TFun(_,args_opt,_,_) ->
          begin
            try
              let args = argsToList args_opt in
              let (_,t,_) = List.nth args i in
              t
            with
              Failure _ ->
                invalid_arg ("type_of_refinfo: not enough arguments in " ^ f.vname)
            | Invalid_argument _ ->
               invalid_arg ("type_of_refinfo: negative argument in " ^ f.vname)
          end
       | _ -> invalid_arg ("type_of_refinfo: type of argument of " ^ f.vname)
     end
  | RealVariable(LocalVar(v,f)) -> v.vtype
  | RealVariable(GlobalVar(v)) -> v.vtype
  | TempVariable(v) -> v.vtype
  | ReturnVar(f) ->
     match unrollType f.vtype with
     | TFun(rtype,_,_,_) -> rtype
     | _ -> invalid_arg ("type_of_refinfo: ReturnVar: " ^ f.vname ^ " not a function")


type fieldable = refinfo * field
and field =
  | NoField
  | Field of string * field

let string_of_field f =
  let rec sub_field g =
    match g with
    | NoField -> assert false
    | Field(s,NoField) -> "." ^ s
    | Field(s,h) -> "." ^ s ^ (sub_field h)
  in
  match f with
  | NoField -> ""
  | _ -> sub_field f


let get_field_index ci f =
  let rec gfi i fis =
    match fis with
    | [] -> raise Not_found
    | fi::tl ->
       if fi.fname = f then i else gfi (i+1) tl
  in
  gfi 0 ci.cfields


let rec number_sub_fields t =
  match unrollType t with
  | TNamed(_) -> assert false
  | TVoid(_) | TInt(_) | TFloat(_) | TPtr(_) | TFun(_) | TEnum(_) | TBuiltin_va_list(_) -> 1
  | TArray(u,_,_) -> number_sub_fields u
  | TComp(ci,_) ->
     List.fold_left
       (fun sum fi ->
	 if fi.fname = missingFieldName then sum
	 else sum + (number_sub_fields fi.ftype))
       0
       ci.cfields

let rec get_offset_number typ offset =
  match offset with
  | NoOffset -> 0
  | Field(fi,ofs) ->
     begin
       match unrollType typ with
       | TComp(ci, _) ->
	  let rec loop acc rem_fields =
	    match rem_fields with
	    | [] -> raise Not_found
	    | hd::tl ->
	       if hd.fname = fi.fname
	       then acc + (get_offset_number hd.ftype ofs)
	       else loop (acc + (number_sub_fields hd.ftype)) tl
	  in
	  loop 0 ci.cfields
       | _ -> invalid_arg "get_offset_number: not a structure/union"
     end
  | Index(_,ofs) ->
     begin
       match unrollType typ with
       | TArray(t,_,_) -> get_offset_number t ofs
       | _ -> invalid_arg "get_offset_number: not an array"
     end


let rec get_field_number typ field =
  match field with
  | NoField -> 0
  | Field(s,sub_field) ->
     match unrollType typ with
     | TComp(ci, _) ->
	let rec loop acc rem_fields =
	  match rem_fields with
	  | [] -> raise Not_found
	  | hd::tl ->
	     if hd.fname = s
	     then acc + (get_field_number hd.ftype sub_field)
	     else loop (acc + (number_sub_fields hd.ftype)) tl
	in
	loop 0 ci.cfields
     | _ -> invalid_arg "get_offset_field: not a structure/union"


let rec flatten_type t =
  match unrollType t with
  | TComp(ci,_) -> flatten_fields ci
  | _ -> [ NoField ]
and flatten_fields ci =
  List.concat (List.map expand_field ci.cfields)
and expand_field fi = List.map (fun x -> Field(fi.fname, x)) (flatten_type fi.ftype)

let rec type_of_field typ field =
  match field with
  | NoField -> typ
  | Field(s, sub_field) ->
     match unrollType typ with
     | TComp(ci, _) ->
	let rec loop rem_fields =
	  match rem_fields with
	  | [] -> raise Not_found
	  | hd::tl ->
	     if hd.fname = s
	     then type_of_field hd.ftype sub_field
	     else loop  tl
	in
	loop ci.cfields
     | _ -> invalid_arg "type_of_field: not a structure/union"



let string_of_var_category v =
  match v with
  | FormalVar(s,i,v) -> s ^ "(arg " ^ (string_of_int i) ^ " of " ^ v.vname ^ ")"
  | LocalVar(v,f) -> v.vname ^ "(local of " ^ f.svar.vname ^ ")"
  | GlobalVar(v) -> v.vname

let string_of_refinfo r =
  match r with
  | RealVariable(v) -> string_of_var_category v
  | TempVariable(v) -> v.vname ^ "(temporary)"
  | ReturnVar(f) -> "return of " ^ f.vname

let string_of_fieldable (r,f) =
  (string_of_refinfo r) ^ (string_of_field f)


module RefinfoCompare =
struct
  type t = refinfo

  let pair_of r =
    match r with
    | RealVariable(v) ->
       begin
         match v with
         | FormalVar(_,i,f) -> (f.vid, i)
         | LocalVar(vi,_) -> (vi.vid, 0)
         | GlobalVar(vi) -> (vi.vid, 0)
       end
    | TempVariable(v) -> (v.vid, 0)
    | ReturnVar(v) -> (v.vid, -1)

  let compare r1 r2 =
    let (x1, y1) = pair_of r1
    and (x2, y2) = pair_of r2 in
    let cmp_x = compare x1 x2 in
    if cmp_x = 0 then compare y1 y2 else cmp_x

end
module RefinfoMap = Map.Make(RefinfoCompare)

module FieldableCompare =
  struct
    type t = fieldable
    let compare (r1,f1) (r2,f2) =
      let cmp_r = RefinfoCompare.compare r1 r2 in
      if cmp_r = 0 then compare f1 f2 else cmp_r
  end
module FieldableMap = Map.Make(FieldableCompare)

module PureIdCompare =
struct
  type t = int
  let compare = Pervasives.compare
end
module PureIdMap = Map.Make(PureIdCompare)
(* We start at 1, so that 0 or <0 can be considered an error *)
let uid = ref 1

let ids_of = ref FieldableMap.empty
let of_ids = ref PureIdMap.empty

let end_of = ref PureIdMap.empty


let get_fieldable (r, f) =
  try
    FieldableMap.find (r,f) !ids_of
  with
    Not_found ->
    let flattened_type = flatten_type (type_of_refinfo r) in
    let size = List.length flattened_type in
    (* Asking for a variable will be the same as asking for its first field, if any *)
    (* TODO: do it for all first fields... *)
    let () = ids_of := FieldableMap.add (r, NoField) !uid !ids_of in
    let last = !uid + size - 1 in
    let add_f field =
      let i = !uid and () = incr uid in
      let y = (r, field) in
      let () = info ("Found a referenceable: " ^ (string_of_fieldable y) ^ "[" ^ (string_of_int i) ^ "]"
		     ^ "(end: " ^ (string_of_int last) ^ ")") in
      begin
	ids_of := FieldableMap.add y i !ids_of;
	end_of := PureIdMap.add i last !end_of;
	of_ids := PureIdMap.add i y !of_ids
      end
    in
    let () = List.iter add_f flattened_type in
    FieldableMap.find (r,f) !ids_of

let get_temporary_field v f = get_fieldable (TempVariable(v), f)
let get_temporary v = get_temporary_field v NoField
let get_global_field vi f = get_fieldable (RealVariable(GlobalVar(vi)), f)
let get_global vi = get_global_field vi NoField
let get_local_field vi fundec f = get_fieldable (RealVariable(LocalVar(vi, fundec)), f)
let get_local vi fundec = get_local_field vi fundec NoField


let get_formals_prototype f =
  let formals =
    match unrollType f.vtype with
    | TFun(_,args_opt,_,_) ->
       List.map (fun (s,_,_) -> s) (argsToList args_opt)
    | _ -> invalid_arg ("get_formals_prototype: " ^ f.vname ^ " is not a function")
  in
  let total = List.length formals in
  let end_formals = !uid + total - 1 in
  let rec add_formals already_found n names acc =
    match names with
    | [] ->
       begin
         assert (total = n);
         (already_found, acc)
       end
    | name::tl ->
       let r = RealVariable(FormalVar(name, n, f)) in
       let x = (r, NoField) in
       try
         let i = FieldableMap.find x !ids_of in
         add_formals (already_found + 1) (n+1) tl (i :: acc)
       with
         Not_found ->
           let i = !uid and () = incr uid in
           begin
             ids_of := FieldableMap.add x i !ids_of;
	     end_of := PureIdMap.add i end_formals !end_of;
             info ("Found a referenceable: " ^ (string_of_refinfo r) ^ "[" ^ (string_of_int i) ^ "]" ^ "(end: " ^ (string_of_int end_formals) ^ ")");
             of_ids := PureIdMap.add i x !of_ids;
             add_formals already_found (n+1) tl (i :: acc)
           end
  in
  let (already_found, rev_ids) = add_formals 0 0 formals [] in
  let add_return already_found acc =
    let r = ReturnVar(f) in
    let x = (r, NoField) in
    try
      let i = FieldableMap.find x !ids_of in
      (already_found + 1, i :: acc)
    with
      Not_found ->
        let i = !uid and () = incr uid in
        let () = info ("Found a referenceable: " ^ (string_of_refinfo r) ^ "[" ^ (string_of_int i) ^ "]") in
        begin
          ids_of := FieldableMap.add x i !ids_of;
	  end_of := PureIdMap.add i i !end_of;
          of_ids := PureIdMap.add i x !of_ids;
          (already_found, i :: acc)
        end
  in
  let (already_present, rev_list_of_ids) = add_return already_found rev_ids in
  if already_present = 0 || already_present = total + 1
  then List.rev rev_list_of_ids
  else failwith ("get_formals_prototype: partial presence for function " ^ f.vname)


let get_formal f i =
  let all_formals_plus_return = get_formals_prototype f in
  let n = List.length all_formals_plus_return in
  if i < n - 1
  then List.nth all_formals_plus_return i
  else invalid_arg ("get_formal: taking parameter " ^ (string_of_int i) ^ " out of " ^ (string_of_int n) ^ " (return included)")

let get_return f =
  let all_formals_plus_return = get_formals_prototype f in
  List.hd (List.rev all_formals_plus_return)



let id_of r =
  match r with
  | RealVariable(FormalVar(s,i,f)) -> get_formal f i
  | RealVariable(LocalVar(v,f)) -> get_local v f
  | RealVariable(GlobalVar(v)) -> get_global v
  | TempVariable(v) -> get_temporary v
  | ReturnVar(f) -> get_return f

let end_of i = PureIdMap.find i !end_of



let of_id i = PureIdMap.find i !of_ids

let string_of_varinfos vis =
  String.concat ", " (List.map (fun v -> v.vname) vis)

let string_of_expr e =
  Pretty.sprint ~width:70 (defaultCilPrinter#pExp () e)

let string_of_exprs exprs =
  String.concat ", "  (List.map string_of_expr exprs)

let pLoc l =
  text l.file
  ++ text ":"
  ++ text (string_of_int l.line)

let string_of_loc l = Pretty.sprint ~width:70 (pLoc l)

let args_of f =
  match unrollType f.vtype with
  | TFun(_,args,_,_) -> List.map (fun (s,_,_) -> s) (argsToList args)
  | _ -> invalid_arg ("args_of: " ^ f.vname)

let string_of_args f = String.concat "," (args_of f)

let get_formal_position vi f =
  let rec count i remaining_formals =
    match remaining_formals with
    | [] -> raise Not_found
    | formal::tl -> if formal.vid = vi.vid then i else count (i+1) tl
  in
  count 0 f.sformals


type constraint_origin =
  | CRefExpr of refinfo * (exp * fundec)
  | CLvalExpr of (lval * fundec) * (exp * fundec)
  | CLvalRef of (lval * fundec) * refinfo
  | CFunPtrCall of lval option * exp * exp list * fundec

class constraintVisitorClass seenFunctions =
  object(self)
  inherit Cil.nopCilVisitor

  val relationships = ref []


  method vstmt s =
    match s.skind with
    | Instr(_) -> DoChildren
    | Return(exp_opt, loc) ->
       begin
         match exp_opt with
         | None -> SkipChildren
         | Some(expr) ->
            let current_fundec =
              match !currentGlobal with
              | GFun(f,_) -> f
              | _ -> assert false
            in
            begin
              relationships := ( CRefExpr(ReturnVar(current_fundec.svar), (expr, current_fundec)) ) :: !relationships;
              SkipChildren
            end
       end
    | Goto(_) -> DoChildren
    | ComputedGoto(_) -> DoChildren
    | Break(_) -> DoChildren
    | Continue(_) -> DoChildren
    | If(_) -> DoChildren
    | Switch(_) -> DoChildren
    | Loop(_) -> DoChildren
    | Block(_) -> DoChildren
    | TryFinally(_) -> DoChildren
    | TryExcept(_) -> DoChildren


  method vinst i =
    match i with
    | Set(lval, exp, loc) ->
       let current_fundec =
         match !currentGlobal with
         | GFun(f,_) -> f
         | _ -> assert false
       in
       begin
         relationships := (CLvalExpr((lval, current_fundec),(exp, current_fundec))) :: !relationships;
         SkipChildren
       end
    | Call(lval_opt, exp, exprs, loc) ->
       let current_fundec =
         match !currentGlobal with
         | GFun(f,_) -> f
         | _ -> assert false
       in
       begin
         match exp with
         | Lval(Var(vi), NoOffset) -> (* direct call *)
            let () =
              match lval_opt with
              | None -> ()
              | Some(ret) ->
                 relationships := (CLvalRef((ret, current_fundec), ReturnVar(vi))) :: !relationships
            in
            let add_parameter called_f i (s, expr) =
              relationships := (CRefExpr( RealVariable(FormalVar(s, i, called_f)), (expr, current_fundec))) :: !relationships
            in
            let () =
              try
                let combined = List.combine (args_of vi) exprs in
                List.iteri (add_parameter vi) combined
              with
                Invalid_argument _ ->
                  fatal ("Not the same number of args for " ^ vi.vname ^ " at "
                         ^ (string_of_loc loc) ^ ": "
                         ^ (string_of_args vi) ^ " vs "
                         ^ (string_of_exprs exprs))
            in
            SkipChildren
	 | _ ->
	    begin
	      relationships := (CFunPtrCall(lval_opt, exp, exprs, current_fundec)) :: !relationships;
	      SkipChildren
	    end
       end
    | Asm(_) -> SkipChildren

  method return_relationships = !relationships

end


module Vertex = struct
  type t = int
  let compare n1 n2 = Pervasives.compare n1 n2
  let hash n = n
  let equal n1 n2  = n1 = n2
end

let s_of_vertex n =
  string_of_fieldable (of_id n) ^ "[" ^ (string_of_int n) ^ "]"

type edge_constraint =
  | Contains
  | Points_to
  | Contains_star
  | Star_contains
  | Contains_star_k of int
  | Star_k_contains of int
  | Contains_k of int

module Edge = struct
   type t = edge_constraint
   let compare = Pervasives.compare
   let equal = (=)
   let default = Contains
end

let s_of_edge (v1, l, v2) =
  let no_change s = s
  and set_of s = "{ " ^ s ^ " }"
  and star s = "*" ^ s in
  let star_k k s = "*(" ^ s ^ "+" ^ (string_of_int k) ^ ")" in
  let plus k s = s ^ "+" ^ (string_of_int k) in
  let (left_s, right_s) =
    match l with
    | Contains -> (no_change, no_change)
    | Points_to -> (no_change, set_of)
    | Contains_star -> (no_change, star)
    | Star_contains -> (star, no_change)
    | Contains_star_k(k) -> (no_change, star_k k)
    | Star_k_contains(k) -> (star_k k, no_change)
    | Contains_k(k) -> (no_change, plus k)
  in
  (left_s (s_of_vertex v1)) ^ " > " ^ (right_s (s_of_vertex v2))


module G = Graph.Imperative.Digraph.ConcreteLabeled(Vertex)(Edge)

let dump_graph g =
  G.iter_edges_e
    (fun e -> info (s_of_edge e))
    g



type dereferencing =
  | D_irrelevant of typ
  | D_i of int * typ (* Applicable to variables that are not related to structures *)
  | D_field of dereferencing * field (* Applicable to fields and variables of structure type *)
  | D_index of int * int * typ (* Applicable to function pointer calls *)
  | D_addr of dereferencing (* Applicable to any address taking *)
  | D_mem of dereferencing (* Applicable to any dereferencing *)


let rec type_of_dereferencing d =
  match d with
  | D_irrelevant(ty) -> ty
  | D_i(_,ty) -> ty
  | D_field(e,f) ->
     let ty = type_of_dereferencing e in
     type_of_field ty f
  | D_index(_,_,ty) -> ty
  | D_addr(d) -> TPtr(type_of_dereferencing d, [])
  | D_mem(d) ->
     let type_of_d = type_of_dereferencing d in
     match unrollType type_of_d with
     | TPtr(ty,_) -> ty
     | _ -> invalid_arg "type_of_dereferencing"


let rec string_of_dereferencing d =
  match d with
  | D_irrelevant(_) -> "_"
  | D_i(i,_) -> s_of_vertex i
  | D_field(e,f) -> (string_of_dereferencing e) ^ "{" ^ (string_of_field f) ^ "}"
  | D_index(p,k,_) -> (string_of_int p) ^ "+" ^ (string_of_int k)
  | D_addr(e) -> "&(" ^ (string_of_dereferencing e) ^ ")"
  | D_mem(e) -> "*(" ^ (string_of_dereferencing e) ^ ")"


let rec is_irrelevant = function
  | D_irrelevant(_) -> true
  | D_i(_) -> false
  | D_field(d,_) -> is_irrelevant d
  | D_index(_) -> false
  | D_addr(d) -> is_irrelevant d
  | D_mem(d) -> is_irrelevant d


let rec build_dereferencing_expr f expr =
  match expr with
  | Const(const) -> D_irrelevant(typeOf expr)
  | Lval(lval) -> build_dereferencing_lval f lval
  | SizeOf(_)
  | SizeOfE(_)
  | SizeOfStr(_)
  | AlignOf(_)
  | AlignOfE(_)
  | UnOp(_)
  | BinOp(_) -> D_irrelevant(typeOf expr) (*TODO *)
  | Question(_) -> (*TODO *) D_irrelevant(typeOf expr)
  | CastE(_,e) -> build_dereferencing_expr f e
  | AddrOfLabel(_) -> D_irrelevant(typeOf expr)
  | AddrOf(lval)
  | StartOf(lval) -> D_addr(build_dereferencing_lval f lval)
and build_dereferencing_lval f (lhost, offset) =
  let field = build_dereferencing_offset offset in
  let deref_lhost = build_dereferencing_lhost f lhost in
  let lhost_type = type_of_dereferencing deref_lhost in
  match field with
  | NoField -> deref_lhost
  | _ ->
     match unrollType lhost_type with
     | TComp(_) -> D_field(deref_lhost, field)
     | _ -> assert false
and build_dereferencing_offset offset =
  match offset with
  | NoOffset -> NoField
  | Field(fi, ofs)-> Field(fi.fname, build_dereferencing_offset ofs)
  | Index(_,ofs) -> build_dereferencing_offset ofs
and build_dereferencing_lhost f lhost =
  match lhost with
  | Var(vi) ->
     let refinfo =
       match unrollType vi.vtype with
       | TFun(_,tyargs_opt,_,_) ->
          begin
            match argsToList tyargs_opt with
            | [] -> RealVariable(FormalVar(vi.vname, 0, vi))
            | (name,_,_)::_ -> RealVariable(FormalVar(name, 0, vi))
          end
       | _ ->
          if vi.vglob then RealVariable(GlobalVar(vi))
          else
            try
              let i = get_formal_position vi f in
              RealVariable(FormalVar(vi.vname, i, f.svar))
            with
              Not_found -> RealVariable(LocalVar(vi, f))
     in
     D_i(id_of refinfo, vi.vtype)
  | Mem(expr) -> D_mem(build_dereferencing_expr f expr)


let build_dereferencing_refinfo r = D_i(id_of r, type_of_refinfo r)


let string_of_constraint (left, right) =
  (string_of_dereferencing left)
  ^ " = "
  ^ (string_of_dereferencing right)

(*
  p > q          provient de x = y
  p > {q}        provient de x = &y
  p > *q         provient de x = *y
  *p > q         provient de *x = y
  p > *(q+k)     provient de x = *p(...k-1 args)   ou x = y->k (soit x = ( *y).k)
  *(p+k) > q     provient de *p(...,y,...) avec y le k-ième arg   ou x->k = y (soit ( *x).k = y)
  p > q+k        provient de x = &y->k (soit x = &(( *y).k)
 *)

(* These functions transforms the dereferencing into their canonical forms (e.g. **x will become *y with y = *x) *)
let simplify_dereferencing d =
  match d with
  | D_irrelevant(_)
  | D_i(_)                            (* p *)
  | D_index(_)                        (* f(...,p,...) *)
  | D_field(D_i(_),_)                 (* p.f *)
  | D_field(D_mem(D_i(_)),_)          (* p->f *)
  | D_mem(D_i(_))                     (* *p *)
  | D_mem(D_field(D_i(_),_))          (* *(p.f) *)
  | D_addr(D_i(_))                    (* &p *)
  | D_addr(D_field(D_i(_),_))         (* &p.f *)
  | D_addr(D_field(D_mem(D_i(_)),_))  (* &p->f *)
    -> (d, None)
  | D_field(x,f) ->
     let type_of_x = type_of_dereferencing x in
     let tmp_var = makeVarinfo true "tmp_" type_of_x in
     let () = tmp_var.vname <- "tmp_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let i = D_i(idx, type_of_x) in
     let d' = D_field(i, f) in
     let ((d1, d2) as assign) = (i, x) in
     let () = info (
       "Transforming " ^ (string_of_dereferencing d)
       ^ " into " ^ (string_of_dereferencing d')
       ^ " with " ^ (string_of_constraint assign))
     in
     (d', Some(assign))
  | D_addr(x) -> assert false
  | D_mem(x) ->
     let type_of_x = type_of_dereferencing x in
     let tmp_var = makeVarinfo true "tmp_" type_of_x in
     let () = tmp_var.vname <- "tmp_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let i = D_i(idx, type_of_x) in
     let d' = D_mem(i) in
     let ((d1, d2) as assign) = (i, x) in
     let () = info (
       "Transforming " ^ (string_of_dereferencing d)
       ^ " into " ^ (string_of_dereferencing d')
       ^ " with " ^ (string_of_constraint assign))
     in
     (d', Some(assign))

let rec simplify_constraint (d1, d2) =
  let (d1', opt_c1) = simplify_dereferencing d1
  and (d2', opt_c2) = simplify_dereferencing d2 in
  match opt_c1, opt_c2 with
  | None, None -> [ (d1', d2') ]
  | Some(c1), None ->
     let res = simplify_constraint c1 in
     res @ [ (d1', d2') ]
  | None, Some(c2) ->
     let res = simplify_constraint c2 in
     res @ [ (d1', d2') ]
  |  Some(c1), Some(c2) ->
     let res1 = simplify_constraint c1 in
     let res2 = simplify_constraint c2 in
      res1 @ res2 @ [ (d1', d2') ]
and simplify_constraints ds =
  List.flatten (List.map simplify_constraint ds)


let canonical_dereferencing d =
  match d with
  | D_irrelevant(_)
  | D_i(_)                            (* p *)
  | D_index(_)                        (* f(...,p,...) *)
  | D_field(D_i(_),_)                 (* p.f *)
  | D_field(D_mem(D_i(_)),_)          (* p->f *)
  | D_mem(D_i(_))                     (* *p *)
  | D_mem(D_field(D_i(_),_))          (* *(p.f) *)
  | D_addr(D_i(_))                    (* &p *)
  | D_addr(D_field(D_i(_),_))         (* &p.f *)
  | D_addr(D_field(D_mem(D_i(_)),_))  (* &p->f *)
    -> true
  | _ -> false (* TODO: still not sure about D_field(D_field(...)) *)


let remove_irrelevant constraints =
  let rec aux_remove acc cs =
    match cs with
    | [] -> List.rev acc
    | ((d1, d2) as c)::tl ->
       match d1, d2 with
       | D_irrelevant(_), _
       | _, D_irrelevant(_) -> aux_remove acc tl
       | _, _ -> aux_remove (c::acc) tl
  in
  aux_remove [] constraints


let canonicalize_constraint ((d1, d2) as c) =
  assert ((canonical_dereferencing d1) && (canonical_dereferencing d2));
  match d1, d2 with
  | D_i(_), _ -> [c]
  | D_field(D_i(_),_), _ -> [c]
  | D_addr(_), _ -> assert false
  | D_mem(D_i(_) | D_field(D_i(_),_)), D_i(_)
  | D_mem(D_i(_) | D_field(D_i(_),_)), D_field(D_i(_),_)
  | D_index(_), (D_i(_) | D_field(D_i(_),_))
  | D_field(D_mem(D_i(_)),_), (D_i(_) | D_field(D_i(_),_)) -> [c]

  | D_mem(D_i(_) | D_field(D_i(_),_)), _
  | D_index(_), _
  | D_field(D_mem(D_i(_)),_), _ ->
     let type_of_d2 = type_of_dereferencing d2 in
     let tmp_var = makeVarinfo true "tmp_split_" type_of_d2 in
     let () = tmp_var.vname <- "tmp_split_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let i = D_i(idx, type_of_d2) in
     let c1 = (d1, i) in
     let c2 = (i, d2) in
     let () = info (
       "Transforming " ^ (string_of_constraint c)
       ^ " into " ^ (string_of_constraint c1)
       ^ " and " ^ (string_of_constraint c2))
     in
     [c2; c1]
  | _ -> assert false


let generate_constraints c =
  let simple_constraints = simplify_constraint c in
  let no_irrelevant = remove_irrelevant simple_constraints in
  List.flatten (List.map canonicalize_constraint no_irrelevant)

(* TODO: iterate over fields to have all the real constraints *)
let build_Contains d1 d2 =
  match d1, d2 with
  | D_i(i1, t1), D_i(i2, t2) -> (i1, Contains, i2)
  | D_i(i1, t1), D_field(D_i(i2, t2),f2) -> (i1, Contains, i2 + (get_field_number t2 f2))
  | D_field(D_i(i1, t1),f1), D_i(i2, t2) -> (i1 + (get_field_number t1 f1), Contains, i2)
  | D_field(D_i(i1, t1),f1), D_field(D_i(i2, t2),f2) -> (i1 + (get_field_number t1 f1), Contains, i2 + (get_field_number t2 f2))
  | _ -> assert false

let build_Points_to d1 d2 =
  match d1, d2 with
  | D_i(i1,t1), D_addr(D_i(i2,t2)) -> (i1, Points_to, i2)
  | D_field(D_i(i1,t1),f1), D_addr(D_i(i2,t2)) -> (i1 + (get_field_number t1 f1), Points_to, i2)
  | _ -> assert false

let build_Contains_star d1 d2 =
  match d1, d2 with
  | D_i(i1,t1), D_mem(D_i(i2,t2)) -> (i1, Contains_star, i2)
  | D_i(i1,t1), D_mem(D_field(D_i(i2,t2),f2)) -> (* TODO: is it really there ? *)
     (i1, Contains_star, i2 + (get_field_number t2 f2))
  | D_field(D_i(i1,t1),f1), D_mem(D_i(i2,t2)) -> (i1 + (get_field_number t1 f1), Contains_star, i2)
  | D_field(D_i(i1,t1),f1), D_mem(D_field(D_i(i2,t2),f2)) -> (* TODO: is it really there ? *)
     (i1 + (get_field_number t1 f1), Contains_star, i2 + (get_field_number t2 f2))
  | _ -> assert false


let unPtrType t =
  match unrollType t with
  | TPtr(u,_) -> u
  | _ -> assert false

let build_Contains_star_k d1 d2 =
  match d1, d2 with
  | D_i(i1,t1), D_field(D_mem(D_i(i2,t2)),f2) -> (i1, Contains_star_k(get_field_number (unPtrType t2) f2), i2)
  | D_i(i1,t1), D_index(i2,k,t2) -> (i1, Contains_star_k(k), i2)
  | D_field(D_i(i1,t1),f1), D_field(D_mem(D_i(i2,t2)),f2) -> (i1 + (get_field_number t1 f1), Contains_star_k(get_field_number (unPtrType t2) f2), i2)
  | D_field(D_i(i1,t1),f1), D_index(i2,k,t2) -> (i1 + (get_field_number t1 f1), Contains_star_k(k), i2)
  | _ -> assert false

let build_Contains_k d1 d2 =
  match d1, d2 with
  | D_i(i1,t1), D_addr(D_field(D_i(i2,t2),f2)) -> (i1, Contains_k(get_field_number t2 f2), i2)
  | D_i(i1,t1), D_addr(D_field(D_mem(D_i(i2,t2)),f2)) -> (i1, Contains_k(get_field_number (unPtrType t2) f2), i2)
  | D_field(D_i(i1,t1),f1), D_addr(D_field(D_i(i2,t2),f2)) -> (i1 + (get_field_number t1 f1), Contains_k(get_field_number t2 f2), i2)
  | D_field(D_i(i1,t1),f1), D_addr(D_field(D_mem(D_i(i2,t2)),f2)) -> (i1 + (get_field_number t1 f1), Contains_k(get_field_number (unPtrType t2) f2), i2)
  | _ -> assert false

let build_Star_contains d1 d2 =
  match d1, d2 with
  | D_mem(D_i(i1,t1)), D_i(i2,t2) -> (i1, Star_contains, i2)
  | D_mem(D_field(D_i(i1,t1),f1)), D_i(i2,t2) -> (i1 + (get_field_number t1 f1), Star_contains, i2)
  | D_mem(D_i(i1,t1)), D_field(D_i(i2,t2),f2) -> (i1, Star_contains, i2 + (get_field_number t2 f2))
  | D_mem(D_field(D_i(i1,t1),f1)), D_field(D_i(i2,t2),f2) -> (i1 + (get_field_number t1 f1), Star_contains, i2 + (get_field_number t2 f2))
  | _ -> assert false

let build_Star_k_contains d1 d2 =
  match d1, d2 with
  | D_index(i1,k,t1), D_i(i2,t2) -> (i1, Star_k_contains(k), i2)
  | D_index(i1,k,t1), D_field(D_i(i2,t2),f2) -> (i1, Star_k_contains(k), i2 + (get_field_number t2 f2))
  | D_field(D_mem(D_i(i1,t1)),f1), D_i(i2,t2) -> (i1, Star_k_contains(get_field_number (unPtrType t1) f1), i2)
  | D_field(D_mem(D_i(i1,t1)),f1), D_field(D_i(i2,t2),f2) -> (i1, Star_k_contains(get_field_number (unPtrType t1) f1), i2 + (get_field_number t2 f2))
  | _ -> assert false


let finalize_constraint (d1, d2) =
  match d1, d2 with
  | D_i(_), D_i(_)
  | D_i(_), D_field(D_i(_),_)
  | D_field(D_i(_),_), D_i(_)
  | D_field(D_i(_),_), D_field(D_i(_),_) -> build_Contains d1 d2

  | D_i(_), D_addr(D_i(_))
  | D_field(D_i(_),_), D_addr(D_i(_)) -> build_Points_to d1 d2

  | D_i(_), D_mem(D_i(_))
  | D_i(_), D_mem(D_field(D_i(_),_))
  | D_field(D_i(_),_), D_mem(D_i(_))
  | D_field(D_i(_),_), D_mem(D_field(D_i(_),_)) -> build_Contains_star d1 d2

  | D_i(_), D_field(D_mem(D_i(_)),_)
  | D_i(_), D_index(_)
  | D_field(D_i(_),_), D_field(D_mem(D_i(_)),_)
  | D_field(D_i(_),_), D_index(_) -> build_Contains_star_k d1 d2

  | D_i(_), D_addr(D_field(D_i(_),_))
  | D_i(_), D_addr(D_field(D_mem(D_i(_)),_))
  | D_field(D_i(_),_), D_addr(D_field(D_i(_),_))
  | D_field(D_i(_),_), D_addr(D_field(D_mem(D_i(_)),_)) -> build_Contains_k d1 d2

  | D_mem(D_i(_)), D_i(_)
  | D_mem(D_field(D_i(_),_)), D_i(_)
  | D_mem(D_i(_)), D_field(D_i(_),_)
  | D_mem(D_field(D_i(_),_)), D_field(D_i(_),_) ->  build_Star_contains d1 d2

  | D_index(_), D_i(_)
  | D_index(_), D_field(D_i(_),_)
  | D_field(D_mem(D_i(_)),_), D_i(_)
  | D_field(D_mem(D_i(_)),_), D_field(D_i(_),_) -> build_Star_k_contains d1 d2

  | _ -> assert false


let build_constraints c =
  let generated = generate_constraints c in
  List.map finalize_constraint generated


(*
  Les seules constructions possibles sont donc:
  D_i et D_f(D_i) pour p
  D_addr(D_i) pour {q}
  D_mem(D_i) et D_mem(D_f(D_i)) pour *q/*p
  D_index pour *(p+k) (cas appel de fonctions par pointeur)
  D_f(D_mem(D_i)) pour *(p+k) (cas champ de structure)
  D_addr(D_f(D_i)) et D_addr(D_f(D_mem(D_i))) pour p+k

Les constructions plus "profondes" doivent être simplifiées.
Une fois les constructions toutes à l'un de ces formats, il faut rattacher les contraintes aux
contraintes acceptables ci-dessus, donc il peut y avoir une étape supplémentaire de séparation.
*)


let get_constraints ct =
  match ct with
  | CRefExpr(r, (e,f)) ->
     let c_left = D_i(id_of r, type_of_refinfo r) in
     let c_right = build_dereferencing_expr f e in
     build_constraints (c_left, c_right)
  | CLvalExpr((l,f1), (e,f2)) ->
     let c_left = build_dereferencing_lval f1 l in
     let c_right = build_dereferencing_expr f2 e in
     build_constraints (c_left, c_right)
  | CLvalRef((l,f), r) ->
     let c_left = build_dereferencing_lval f l in
     let c_right = D_i(id_of r, type_of_refinfo r) in
     build_constraints (c_left, c_right)
  | CFunPtrCall(lval_opt, exp, exps, f) ->
     let (funptr_i, simplif_constraints) =
       match exp with
       | Lval(Mem(Lval(Var(vi), NoOffset)), NoOffset) ->
          let d_i =
            match build_dereferencing_lhost f (Var(vi)) with
            | D_i(i,_) -> i
            | _ -> assert false
          in
          (d_i, [])
       | Lval(Mem(complex), _) ->
          let type_of_complex = typeOf complex in
          let tmp_var = makeVarinfo false "tmp_funptr_" type_of_complex in
          let () = tmp_var.vname <- "tmp_funptr_" ^ (string_of_int tmp_var.vid) in
          let idx = get_temporary tmp_var in
          let c_left = D_i(idx, type_of_complex) in
          let c_right = build_dereferencing_expr f complex in
          let new_constraints = build_constraints (c_left, c_right) in
          (idx, new_constraints)
       | _ -> assert false (* All calls to function pointers should at least be of the Lval(Mem(...),...) shape *)
     in
     let build_constraint_param k expr =
       build_constraints ((D_index(funptr_i, k, typeOf expr)), (build_dereferencing_expr f expr))
     in
     let each_param_constraints = List.mapi build_constraint_param exps in
     let return_constraint =
       match lval_opt with
       | None -> []
       | Some(lval) ->
          build_constraints ((build_dereferencing_lval f lval), (D_index(funptr_i, List.length exps, typeOfLval lval)))
     in
    List.concat (return_constraint :: simplif_constraints :: each_param_constraints)


let graph_of_relationships relationships =
  let g = G.create () in
  let add_relationship ct =
    let constraints = get_constraints ct in
    List.iter
      (fun (i1, c, i2) ->
        G.add_edge_e g (i1, c, i2)
      )
      constraints
  in
  let () = List.iter add_relationship relationships in
  g


let rule_trans witness g p =
  let rule_prefix = "rule_trans " ^ (string_of_int p) in
  let all_preds = G.pred g p in
  let all_succs = G.succ g p in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (r, Contains, p)) all_preds in
  let all_qs = List.filter (fun q -> G.mem_edge_e g (p, Points_to, q)) all_succs in
  let add_r qs r =
    List.iter
      (fun q ->
        if not (G.mem_edge_e g (r, Points_to, q))
        then begin
          let hyp1 = s_of_edge (p, Points_to, q) in
          let hyp2 = s_of_edge (r, Contains, p) in
          let new_edge = (r, Points_to, q) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      qs
  in
  List.iter
    (add_r all_qs)
    all_rs


let rule_deref1 witness g q =
  let rule_prefix = "rule_deref1 " ^ (string_of_int q) in
  let all_preds = G.pred g q in
  let all_succs = G.succ g q in
  let all_ps = List.filter (fun p -> G.mem_edge_e g (p, Contains_star, q)) all_preds in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (q, Points_to, r)) all_succs in
  let add_r ps r =
    List.iter
      (fun p ->
        if not (G.mem_edge_e g (p, Contains, r))
        then begin
          let hyp1 = s_of_edge (p, Contains_star, q) in
          let hyp2 = s_of_edge (q, Points_to, r) in
          let new_edge = (p, Contains, r) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      ps
  in
  List.iter
    (add_r all_ps)
    all_rs


let rule_deref2 witness g p =
  let rule_prefix = "rule_deref2 " ^ (string_of_int p) in
  let all_succs = G.succ g p in
  let all_qs = List.filter (fun q -> G.mem_edge_e g (p, Star_contains, q)) all_succs in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (p, Points_to, r)) all_succs in
  let add_r qs r =
    List.iter
      (fun q ->
        if not (G.mem_edge_e g (r, Contains, q))
        then begin
          let hyp1 = s_of_edge (p, Star_contains, q) in
          let hyp2 = s_of_edge (p, Points_to, r) in
          let new_edge = (r, Contains, q) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      qs
  in
  List.iter
    (add_r all_qs)
    all_rs



let rule_deref4 witness g q =
  let rule_prefix = "rule_deref4 " ^ (string_of_int q) in
  let all_pred_edges = G.pred_e g q in
  let all_succs = G.succ g q in
  let all_ps =
    List.filter (fun e -> match e with (p, Contains_star_k(k), q) -> true | _ -> false) all_pred_edges
  in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (q, Points_to, r)) all_succs in
  let add_p_r p k r =
    let s = r + k in
    let end_of_r = end_of r in
    if s <= end_of_r then (* FIXME: beware of the Not_found (which should not happen) *)
      if not (G.mem_edge_e g (p, Contains, s))
      then begin
        let hyp1 = s_of_edge (p, Contains_star_k(k), q) in
        let hyp2 = s_of_edge (q, Points_to, r) in
        let hyp3 = "idx(" ^ (string_of_int s) ^ ") = idx(" ^ (string_of_int r) ^ ")+" ^ (string_of_int k) in
        let hyp4 = "idx(" ^ (string_of_int s) ^ ") <= end(" ^ (string_of_int end_of_r) ^ ")" in
        let new_edge = (p, Contains, s) in
        let res = s_of_edge new_edge in
        let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "] + [" ^ hyp3 ^ "] + [" ^ hyp4 ^ "]  =  [" ^ res ^ "]" in
        G.add_edge_e g new_edge;
        info addition;
        witness := true
      end
  in
  let add_edge_pk_r e r =
    match e with
    | (p, Contains_star_k(k), q) -> add_p_r p k r
    | _ -> assert false
  in
  let add_r ps r = List.iter (fun e -> add_edge_pk_r e r) ps in
  List.iter
    (add_r all_ps)
    all_rs


let rule_deref5 witness g p =
  let rule_prefix = "rule_deref5 " ^ (string_of_int p) in
  let all_succs = G.succ g p in
  let all_succ_edges = G.succ_e g p in
  let all_qs =
    List.filter (fun e -> match e with (p, Star_k_contains(k), q) -> true | _ -> false) all_succ_edges
  in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (p, Points_to, r)) all_succs in
  let add_q_r k q r =
    let s = r + k in
    let end_of_r = end_of r in
    if s <= end_of_r then (* FIXME: beware of the Not_found (which should not happen) *)
      if not (G.mem_edge_e g (s, Contains, q))
      then begin
        let hyp1 = s_of_edge (p, Star_k_contains(k), q) in
        let hyp2 = s_of_edge (p, Points_to, r) in
        let hyp3 = "idx(" ^ (string_of_int s) ^ ") = idx(" ^ (string_of_int r) ^ ")+" ^ (string_of_int k) in
        let hyp4 = "idx(" ^ (string_of_int s) ^ ") <= end(" ^ (string_of_int end_of_r) ^ ")" in
        let new_edge = (s, Contains, q) in
        let res = s_of_edge new_edge in
        let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "] + [" ^ hyp3 ^ "] + [" ^ hyp4 ^ "]  =  [" ^ res ^ "]" in
        G.add_edge_e g new_edge;
        info addition;
        witness := true
      end
  in
  let add_edge_kq_r e r =
    match e with
    | (p, Star_k_contains(k), q) -> add_q_r k q r
    | _ -> assert false
  in
  let add_r qs r = List.iter (fun e -> add_edge_kq_r e r) qs in
  List.iter
    (add_r all_qs)
    all_rs


let rule_add witness g q =
  let rule_prefix = "rule_add " ^ (string_of_int q) in
  let all_pred_edges = G.pred_e g q in
  let all_succs = G.succ g q in
  let all_ps =
    List.filter (fun e -> match e with (p, Contains_k(k), q) -> true | _ -> false) all_pred_edges
  in
  let all_rs = List.filter (fun r -> G.mem_edge_e g (q, Points_to, r)) all_succs in
  let add_p_r p k r =
    let s = r + k in
    let end_of_r = end_of r in
    if s <= end_of_r then (* FIXME: beware of the Not_found (which should not happen) *)
      if not (G.mem_edge_e g (p, Points_to, s))
      then begin
        let hyp1 = s_of_edge (p, Contains_k(k), q) in
        let hyp2 = s_of_edge (q, Points_to, r) in
        let hyp3 = "idx(" ^ (string_of_int s) ^ ") = idx(" ^ (string_of_int r) ^ ")+" ^ (string_of_int k) in
        let hyp4 = "idx(" ^ (string_of_int s) ^ ") <= end(" ^ (string_of_int end_of_r) ^ ")" in
        let new_edge = (p, Points_to, s) in
        let res = s_of_edge new_edge in
        let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "] + [" ^ hyp3 ^ "] + [" ^ hyp4 ^ "]  =  [" ^ res ^ "]" in
        G.add_edge_e g new_edge;
        info addition;
        witness := true
      end
  in
  let add_edge_pk_r e r =
    match e with
    | (p, Contains_k(k), q) -> add_p_r p k r
    | _ -> assert false
  in
  let add_r ps r = List.iter (fun e -> add_edge_pk_r e r) ps in
  List.iter
    (add_r all_ps)
    all_rs



let compute_constraints g =
  let has_changed = ref false in
  let i = ref 1 in
  let rec steps () =
    begin
      let () = info ("Pass " ^ (string_of_int !i)) in
      G.iter_vertex (fun v -> rule_trans has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref1 has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref2 has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref4 has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref5 has_changed g v) g;
      G.iter_vertex (fun v -> rule_add has_changed g v) g;
      if !has_changed then (has_changed := false; incr i; steps ())
    end
  in
  steps ()


let usage_msg =
  ( "usage : " ^ (Filename.basename Sys.executable_name) ^ " file.cil\n" )

let spec_args = [
    "-debug", Arg.Set do_debug, "Print more detailed information" ]


let _ =
  let () =
    try
      Cil.initCIL ()
    with
    | e ->
       begin
	 fatal ("Unknown error while configuring the C parsing library");
	 raise e
       end
  in
  let () = Arg.parse spec_args set_input_file usage_msg in
  let maincil =
    if !input_file <> "" then loadBinaryFile !input_file
    else (Arg.usage spec_args usage_msg; exit 1)
  in
  let () = update_seenFunctions maincil in
  let constraintVisitor = new constraintVisitorClass seenFunctions in
  let () = visitCilFile (constraintVisitor:>cilVisitor) maincil in
  let relationships = constraintVisitor#return_relationships in
  let g = graph_of_relationships relationships in
  let () = dump_graph g in
  let () = info "***** BEGIN: computing constraints *****" in
  let () = compute_constraints g in
  let () = info "***** END: computing constraints *****" in
  let () = dump_graph g in
  ()
