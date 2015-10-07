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


let function_returns = Hashtbl.create 223

let find_return f_svar =
  try
    Hashtbl.find function_returns f_svar.vid
  with
    Not_found ->
      let return_type =
        match unrollType f_svar.vtype with
        | TFun(r,_,_,_) -> r
        | _ -> invalid_arg "find_return: not a function type"
      in
      let new_var = makeGlobalVar ("return_" ^ f_svar.vname) return_type in
      let () = Hashtbl.add function_returns f_svar.vid new_var in
      new_var


type vertex = {
  name: string;
  vid: int;
  is_return: bool }


let vertex_of_varinfo ?(is_return=false) vi =
  { name = vi.vname;
    vid = vi.vid;
    is_return = is_return }

module Vertex = struct
  type t = vertex
  let compare n1 n2 = Pervasives.compare n1.vid n2.vid
  let hash = Hashtbl.hash
  let equal n1 n2  = n1.vid = n2.vid
end

let s_of_vertex v =
  v.name ^ "[" ^ (string_of_int v.vid) ^ "]"

type edge_constraint =
  | Contains
  | Points_to
  | Contains_star
  | Star_contains
  | Star_points_to

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
    | Star_points_to -> (star, set_of)
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
  | D_vi of varinfo
  | D_addr of dereferencing
  | D_mem of dereferencing


let rec is_irrelevant = function
  | D_irrelevant -> true
  | D_vi(_) -> false
  | D_addr(d) -> is_irrelevant(d)
  | D_mem(d) -> is_irrelevant(d)


let rec build_dereferencing_expr expr =
  match expr with
  | Const(const) -> D_irrelevant
  | Lval(lval) -> build_dereferencing_lval lval
  | SizeOf(_)
  | SizeOfE(_)
  | SizeOfStr(_)
  | AlignOf(_)
  | AlignOfE(_)
  | UnOp(_)
  | BinOp(_) -> D_irrelevant
  | Question(_) -> (*TODO *) D_irrelevant
  | CastE(_,e) -> build_dereferencing_expr e
  | AddrOfLabel(_) -> D_irrelevant
  | AddrOf(lval)
  | StartOf(lval) -> D_addr(build_dereferencing_lval lval)
and build_dereferencing_lval (lhost, offset) =
  build_dereferencing_lhost lhost
and build_dereferencing_lhost lhost =
  match lhost with
  | Var(vi) -> D_vi(vi)
  | Mem(expr) -> D_mem(build_dereferencing_expr expr)


let rec type_of_dereferencing d =
  match d with
  | D_irrelevant -> assert false
  | D_vi(vi) -> vi.vtype
  | D_addr(d) -> TPtr(type_of_dereferencing d, [])
  | D_mem(d) ->
     let type_of_d = type_of_dereferencing d in
     match unrollType type_of_d with
     | TPtr(ty,_) -> ty
     | _ -> invalid_arg "type_of_dereferencing"


let rec build_constraints vi dereferencing =
  match dereferencing with
  | D_irrelevant -> []
  | D_vi(vi2) -> [ (vi, Contains, vi2) ]
  | D_addr(d) ->
     begin
       match d with
       | D_irrelevant -> assert false
       | D_vi(vi2) -> [ (vi, Points_to, vi2) ]
       | _ -> (* more complex, we have to introduce a temporary variable *)
          let type_of_d = type_of_dereferencing d in
          let tmp_var = makeVarinfo false vi.vname type_of_d in
          let () = tmp_var.vname <- vi.vname ^ "_" ^ (string_of_int tmp_var.vid) in
          let sub_constraints = build_constraints tmp_var d in
          (vi, Points_to, tmp_var) :: sub_constraints
     end
  | D_mem(d) ->
     begin
       match d with
       | D_irrelevant -> assert false
       | D_vi(vi2) -> [ (vi, Contains_star, vi2) ]
       | _ -> (* more complex, we have to introduce a temporary variable *)
          let type_of_d = type_of_dereferencing d in
          let tmp_var = makeVarinfo false vi.vname type_of_d in
          let () = tmp_var.vname <- vi.vname ^ "_" ^ (string_of_int tmp_var.vid) in
          let sub_constraints = build_constraints tmp_var d in
          (vi, Contains_star, tmp_var) :: sub_constraints
     end


let get_constraints vi expr =
  let d = build_dereferencing_expr expr in
  build_constraints vi d


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


class ptrVisitorClass seenFunctions =
  object(self)
  inherit Cil.nopCilVisitor

  val g = G.create ()


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
            let ret_current = find_return current_fundec.svar in
            let constraints = get_constraints ret_current expr in
            let () =
              List.iter
                (fun (v1, c, v2) ->
                  G.add_edge_e g ((vertex_of_varinfo v1), c, (vertex_of_varinfo v2))
                )
                constraints
            in
            SkipChildren
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
       let vi = get_varinfo_lval lval in
       let constraints = get_constraints vi exp in
       let () =
         List.iter
           (fun (v1, c, v2) ->
             G.add_edge_e g ((vertex_of_varinfo v1), c, (vertex_of_varinfo v2))
           )
           constraints
       in
       SkipChildren
    | Call(lval_opt, exp, exprs, loc) ->
       begin
         match exp with
         | Lval(Var(vi), NoOffset) -> (* direct call *)
            let () =
              match lval_opt with
              | None -> ()
              | Some(ret) ->
                 let ret_vi = get_varinfo_lval ret in
                 let ret_function = find_return vi in
                 G.add_edge_e g
                   ((vertex_of_varinfo ret_vi),
                    Contains,
                    (vertex_of_varinfo ret_function ~is_return:true))
            in
            let called_fundec =
              try
                Hashtbl.find seenFunctions vi.vname
              with
                Not_found -> (fatal ("Can not find a definition for " ^ vi.vname); exit 1)
            in
            let add_parameter vi expr =
              let constraints = get_constraints vi expr in
              List.iter
                (fun (v1, c, v2) ->
                  G.add_edge_e g ((vertex_of_varinfo v1), c, (vertex_of_varinfo v2))
                )
                constraints
            in
            let () =
              try
                List.iter2 add_parameter called_fundec.sformals exprs
              with
                Invalid_argument _ ->
                  fatal ("Not the same number of args for " ^ vi.vname ^ " at "
                         ^ (string_of_loc loc) ^ ": "
                         ^ (string_of_varinfos called_fundec.sformals) ^ " vs "
                         ^ (string_of_exprs exprs))
            in
            SkipChildren
         | _ -> SkipChildren
       end
    | Asm(_) -> SkipChildren

  method return_graph = g

end


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
  let ptrVisitor = new ptrVisitorClass seenFunctions in
  let () = visitCilFile (ptrVisitor:>cilVisitor) maincil in
  let g = ptrVisitor#return_graph in
  let () = dump_graph g in
  ()
