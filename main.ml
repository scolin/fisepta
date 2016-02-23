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

type fieldable = var_category * field
and field =
  | NoField
  | Field of string * field

type refinfo =
  | RealVariable of var_category
  | TempVariable of varinfo
  | ReturnVar of varinfo (* not a fundec, for functions that have no body *)


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
module PureIdCompare =
struct
  type t = int
  let compare = Pervasives.compare
end
module PureIdMap = Map.Make(PureIdCompare)
(* We start at 1, so that 0 or <0 can be considered an error *)
let uid = ref 1

let ids_of = ref RefinfoMap.empty
let of_ids = ref PureIdMap.empty

let get_return f =
  try
    RefinfoMap.find (ReturnVar(f)) !ids_of
  with
    Not_found ->
      let i = !uid and () = incr uid in
      begin
        ids_of := RefinfoMap.add (ReturnVar(f)) i !ids_of;
        of_ids := PureIdMap.add i (ReturnVar(f)) !of_ids;
        i
      end

let get_temporary v =
  try
    RefinfoMap.find (TempVariable(v)) !ids_of
  with
    Not_found ->
      let i = !uid and () = incr uid in
      begin
        ids_of := RefinfoMap.add (TempVariable(v)) i !ids_of;
        of_ids := PureIdMap.add i (TempVariable(v)) !of_ids;
        i
      end

let get_global vi =
  try
    RefinfoMap.find (RealVariable(GlobalVar(vi))) !ids_of
  with
    Not_found ->
      let i = !uid and () = incr uid in
      begin
        ids_of := RefinfoMap.add (RealVariable(GlobalVar(vi))) i !ids_of;
        of_ids := PureIdMap.add i (RealVariable(GlobalVar(vi))) !of_ids;
        i
      end

let get_local vi fundec =
  try
    RefinfoMap.find (RealVariable(LocalVar(vi, fundec))) !ids_of
  with
    Not_found ->
      let i = !uid and () = incr uid in
      begin
        ids_of := RefinfoMap.add (RealVariable(LocalVar(vi, fundec))) i !ids_of;
        of_ids := PureIdMap.add i (RealVariable(LocalVar(vi, fundec))) !of_ids;
        i
      end

let get_formals_prototype f =
  let formals =
    match unrollType f.vtype with
    | TFun(_,args_opt,_,_) ->
       List.map (fun (s,_,_) -> s) (argsToList args_opt)
    | _ -> invalid_arg ("get_formals_prototype: " ^ f.vname ^ " is not a function")
  in
  let total = List.length formals in
  let rec add_formals already_found n names acc =
    match names with
    | [] ->
       begin
         assert (total = (n-1));
         (already_found, List.rev acc)
       end
    | name::tl ->
       try
         let i = RefinfoMap.find (RealVariable(FormalVar(name, n, f))) !ids_of in
         add_formals (already_found + 1) (n+1) tl (i :: acc)
       with
         Not_found ->
           let i = !uid and () = incr uid in
           begin
             ids_of := RefinfoMap.add (RealVariable(FormalVar(name, n, f))) i !ids_of;
             of_ids := PureIdMap.add i (RealVariable(FormalVar(name, n, f))) !of_ids;
             add_formals already_found (n+1) tl (i :: acc)
           end
  in
  let (already_present, list_of_ids) = add_formals 0 1 formals [] in
  if already_present = 0 || already_present = total
  then list_of_ids
  else failwith ("get_formals_prototype: partial presence for function " ^ f.vname)


let get_formal f i =
  let all_formals = get_formals_prototype f in
  List.nth all_formals i


let id_of r =
  match r with
  | RealVariable(FormalVar(s,i,f)) -> get_formal f i
  | RealVariable(LocalVar(v,f)) -> get_local v f
  | RealVariable(GlobalVar(v)) -> get_global v
  | TempVariable(v) -> get_temporary v
  | ReturnVar(f) -> get_return f


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
     | _ -> invalid_arg ("type_of_refinfo: type of " ^ f.vname)


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


type constraint_term =
  | CExpr of exp * fundec
  | CLvalue of lval * fundec
  | CRefinfo of refinfo

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
              relationships :=
                ( CRefinfo(ReturnVar(current_fundec.svar)),
                  CExpr(expr, current_fundec) ) :: !relationships;
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
         relationships :=
           (CLvalue(lval, current_fundec),
            CExpr(exp, current_fundec))
         :: !relationships;
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
                 relationships :=
                   (CLvalue(ret, current_fundec),
                    CRefinfo(ReturnVar(vi)) )
                 :: !relationships
            in
            let add_parameter called_f i (s, expr) =
              relationships :=
                (CRefinfo(RealVariable(FormalVar(s, i, called_f))),
                 CExpr(expr, current_fundec))
              :: !relationships
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
         | _ -> SkipChildren
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
  string_of_refinfo (of_id n) ^ "[" ^ (string_of_int n) ^ "]"

type edge_constraint =
  | Contains
  | Points_to
  | Contains_star
  | Star_contains

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
  let (left_s, right_s) =
    match l with
    | Contains -> (no_change, no_change)
    | Points_to -> (no_change, set_of)
    | Contains_star -> (no_change, star)
    | Star_contains -> (star, no_change)
  in
  (left_s (s_of_vertex v1)) ^ " > " ^ (right_s (s_of_vertex v2))


module G = Graph.Imperative.Digraph.ConcreteLabeled(Vertex)(Edge)

let dump_graph g =
  G.iter_edges_e
    (fun e -> info (s_of_edge e))
    g


let rec get_varinfo_exp expr =
  match expr with
  | Const(c) -> invalid_arg "get_varinfo_exp: constant"
  | Lval(lval) -> get_varinfo_lval lval
  | SizeOf(_)
  | SizeOfE(_)
  | SizeOfStr(_)
  | AlignOf(_)
  | AlignOfE(_) -> invalid_arg "get_varinfo_exp: sizeof/alignof"
  | UnOp(_,exp,_) -> get_varinfo_exp exp
  | BinOp(_,e1,e2,_) -> get_varinfo_exp e1
  | Question(e,e1,e2,_) -> invalid_arg "get_varinfo_exp"
  | CastE(_,exp) -> get_varinfo_exp exp
  | AddrOf(lval) -> get_varinfo_lval lval
  (* Used for ComputedGoto, analysis not needed because we will go
     through the label (it must be in the same function *)
  | AddrOfLabel(_) -> invalid_arg "get_varinfo_exp"
  | StartOf(lval) -> get_varinfo_lval lval
and get_varinfo_lval (lhost, offset) =
  get_varinfo_lhost lhost
and get_varinfo_lhost lhost =
  match lhost with
  | Var(vi) -> vi
  | Mem(exp) -> get_varinfo_exp exp

type dereferencing =
  | D_irrelevant
  | D_i of int * typ
  | D_addr of dereferencing
  | D_mem of dereferencing


let rec string_of_dereferencing d =
  match d with
  | D_irrelevant -> "_"
  | D_i(i,_) -> s_of_vertex i
  | D_addr(e) -> "&" ^ (string_of_dereferencing e)
  | D_mem(e) -> "*" ^ (string_of_dereferencing e)


let rec is_irrelevant = function
  | D_irrelevant -> true
  | D_i(_) -> false
  | D_addr(d) -> is_irrelevant(d)
  | D_mem(d) -> is_irrelevant(d)


let rec build_dereferencing_expr f expr =
  match expr with
  | Const(const) -> D_irrelevant
  | Lval(lval) -> build_dereferencing_lval f lval
  | SizeOf(_)
  | SizeOfE(_)
  | SizeOfStr(_)
  | AlignOf(_)
  | AlignOfE(_)
  | UnOp(_)
  | BinOp(_) -> D_irrelevant
  | Question(_) -> (*TODO *) D_irrelevant
  | CastE(_,e) -> build_dereferencing_expr f e
  | AddrOfLabel(_) -> D_irrelevant
  | AddrOf(lval)
  | StartOf(lval) -> D_addr(build_dereferencing_lval f lval)
and build_dereferencing_lval f (lhost, offset) =
  build_dereferencing_lhost f lhost
and build_dereferencing_lhost f lhost =
  match lhost with
  | Var(vi) ->
     let refinfo =
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


let rec type_of_dereferencing d =
  match d with
  | D_irrelevant -> assert false
  | D_i(_, ty) -> ty
  | D_addr(d) -> TPtr(type_of_dereferencing d, [])
  | D_mem(d) ->
     let type_of_d = type_of_dereferencing d in
     match unrollType type_of_d with
     | TPtr(ty,_) -> ty
     | _ -> invalid_arg "type_of_dereferencing"


let string_of_constraint left right =
  (string_of_dereferencing left)
  ^ " = "
  ^ (string_of_dereferencing right)

let rec build_constraints left right =
  match (left, right) with
  | D_irrelevant, _ -> assert false
  | _, D_irrelevant -> []
  | D_i(i1,_), D_i(i2,_) -> [ (i1, Contains, i2) ]
  | D_i(i1,_), D_addr(D_i(i2,_)) -> [ (i1, Points_to, i2) ]
  | D_i(i1,_), D_mem(D_i(i2,_)) -> [ (i1, Contains_star, i2) ]
  | D_i(i1, ty), _ ->
     build_constraints_right i1 ty right
  | D_mem(D_i(i1,_)), D_i(i2,_) -> [ (i1, Star_contains, i2) ]
  | D_mem(_), D_i(i2,ty) ->
     build_constraints_left left i2 ty
  | D_addr(_), _ -> assert false
  | _, _ ->
     let type_of_d = type_of_dereferencing right in
     let tmp_var = makeVarinfo true "tmp_" type_of_d in
     let () = tmp_var.vname <- "tmp_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let () = info (
       "Transforming " ^ (string_of_constraint left right)
       ^ " into " ^ (string_of_constraint left (D_i(idx,type_of_d)))
       ^ " and " ^ (string_of_constraint (D_i(idx,type_of_d)) right))
     in
     let sub_constraints_left = build_constraints left (D_i(idx, type_of_d)) in
     let sub_constraints_right = build_constraints (D_i(idx, type_of_d)) right in
     sub_constraints_left @ sub_constraints_right
and build_constraints_right i ityp right =
  match right with
  | D_irrelevant
  | D_i(_)
  | D_mem(D_i(_))
  | D_addr(D_i(_)) -> assert false
  | D_mem(x) ->
     let type_of_x = type_of_dereferencing x in
     let tmp_var = makeVarinfo true "tmp_" type_of_x in
     let () = tmp_var.vname <- "tmp_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let () = info (
       "Transforming " ^ (string_of_constraint (D_i(i, ityp)) right)
       ^ " into " ^ (string_of_constraint (D_i(i, ityp)) (D_mem(D_i(idx, type_of_x))))
       ^ " and " ^ (string_of_constraint (D_i(idx, type_of_x)) x))
     in
     let sub_constraints_left = build_constraints (D_i(i, ityp)) (D_mem(D_i(idx, type_of_x))) in
     let sub_constraints_right = build_constraints (D_i(idx, type_of_x)) x in
     sub_constraints_left @ sub_constraints_right
  | D_addr(x) -> assert false
and build_constraints_left left i ityp =
  match left with
  | D_irrelevant
  | D_i(_)
  | D_addr(_)
  | D_mem(D_i(_)) -> assert false
  | D_mem(x) ->
     let type_of_x = type_of_dereferencing x in
     let tmp_var = makeVarinfo false "tmp_" type_of_x in
     let () = tmp_var.vname <- "tmp_" ^ (string_of_int tmp_var.vid) in
     let idx = get_temporary tmp_var in
     let () = info (
       "Transforming " ^ (string_of_constraint left (D_i(i,ityp)))
       ^ " into " ^ (string_of_constraint (D_mem(D_i(idx,type_of_x))) (D_i(i,ityp)))
       ^ " and " ^ (string_of_constraint (D_i(idx,type_of_x)) x))
     in
     let sub_constraints_left = build_constraints (D_mem(D_i(idx,type_of_x))) (D_i(i,ityp)) in
     let sub_constraints_right = build_constraints (D_i(idx,type_of_x)) x in
     sub_constraints_left @ sub_constraints_right


let get_constraints (ct1, ct2) =
  match ct1, ct2 with
  | CRefinfo(r), CExpr(e,f) ->
     let c_left = D_i(id_of r, type_of_refinfo r) in
     let c_right = build_dereferencing_expr f e in
     build_constraints c_left c_right
  | CLvalue(l,f1), CExpr(e,f2) ->
     let c_left = build_dereferencing_lval f1 l in
     let c_right = build_dereferencing_expr f2 e in
     build_constraints c_left c_right
  | CLvalue(l,f), CRefinfo(r) ->
     let c_left = build_dereferencing_lval f l in
     let c_right = D_i(id_of r, type_of_refinfo r) in
     build_constraints c_left c_right
  | _ -> assert false


let graph_of_relationships relationships =
  let g = G.create () in
  let add_relationship (ct1, ct2) =
    let constraints = get_constraints (ct1, ct2) in
    List.iter
      (fun (i1, c, i2) ->
        G.add_edge_e g (i1, c, i2)
      )
      constraints
  in
  let () = List.iter add_relationship relationships in
  g


let rule_trans witness g t1 =
  let rule_prefix = "rule_trans " ^ (string_of_int t1) in
  let all_preds = G.pred g t1 in
  let all_succs = G.succ g t1 in
  let all_t3s = List.filter (fun t3 -> G.mem_edge_e g (t3, Contains, t1)) all_preds in
  let all_t2s = List.filter (fun t2 -> G.mem_edge_e g (t1, Points_to, t2)) all_succs in
  let add_t3 t2s t3 =
    List.iter
      (fun t2 ->
        if not (G.mem_edge_e g (t3, Points_to, t2))
        then begin
          let hyp1 = s_of_edge (t3, Contains, t1) in
          let hyp2 = s_of_edge (t1, Points_to, t2) in
          let new_edge = (t3, Points_to, t2) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      t2s
  in
  List.iter
    (add_t3 all_t2s)
    all_t3s


let rule_deref1 witness g t2 =
  let rule_prefix = "rule_deref1 " ^ (string_of_int t2) in
  let all_preds = G.pred g t2 in
  let all_succs = G.succ g t2 in
  let all_t1s = List.filter (fun t1 -> G.mem_edge_e g (t1, Contains_star, t2)) all_preds in
  let all_t3s = List.filter (fun t3 -> G.mem_edge_e g (t2, Points_to, t3)) all_succs in
  let add_t3 t1s t3 =
    List.iter
      (fun t1 ->
        if not (G.mem_edge_e g (t1, Contains, t3))
        then begin
          let hyp1 = s_of_edge (t1, Contains_star, t2) in
          let hyp2 = s_of_edge (t2, Points_to, t3) in
          let new_edge = (t1, Contains, t3) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      t1s
  in
  List.iter
    (add_t3 all_t1s)
    all_t3s


let rule_deref2 witness g t1 =
  let rule_prefix = "rule_deref2 " ^ (string_of_int t1) in
  let all_succs = G.succ g t1 in
  let all_t2s = List.filter (fun t2 -> G.mem_edge_e g (t1, Star_contains, t2)) all_succs in
  let all_t3s = List.filter (fun t3 -> G.mem_edge_e g (t1, Points_to, t3)) all_succs in
  let add_t3 t2s t3 =
    List.iter
      (fun t2 ->
        if not (G.mem_edge_e g (t3, Contains, t2))
        then begin
          let hyp1 = s_of_edge (t1, Star_contains, t2) in
          let hyp2 = s_of_edge (t1, Points_to, t3) in
          let new_edge = (t3, Contains, t2) in
          let res = s_of_edge new_edge in
          let addition = rule_prefix ^ ": [" ^ hyp1 ^ "]  +  [" ^ hyp2 ^ "]  =  [" ^ res ^ "]" in
          G.add_edge_e g new_edge;
          info addition;
          witness := true
        end)
      t2s
  in
  List.iter
    (add_t3 all_t2s)
    all_t3s



let compute_constraints g =
  let has_changed = ref false in
  let i = ref 1 in
  let rec steps () =
    begin
      let () = info ("Pass " ^ (string_of_int !i)) in
      G.iter_vertex (fun v -> rule_trans has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref1 has_changed g v) g;
      G.iter_vertex (fun v -> rule_deref2 has_changed g v) g;
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
