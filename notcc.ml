open Cil
open Pretty

let path_to_exe = Filename.dirname (Sys.executable_name)
let path_to_cwd = Sys.getcwd ()
let output = ref None
let pp_files = ref []

let set_output s =
  output := Some(s)

let add_pp_file s =
  let name = Filename.chop_extension (Filename.basename s) in
  let () = if !output = None then output := Some(name ^ ".cil") in
  pp_files := s :: !pp_files

let parse_preprocessed file =
  try
    Frontc.parse file ()
  with e ->
    let () = prerr_endline ("Error while parsing file " ^ file) in
    raise e

let merge files =
  Mergecil.merge files "notcc"


let force_option o =
  match o with
  | None -> assert false
  | Some(x) -> x

let usage_msg =
  ( "usage : " ^ (Filename.basename Sys.executable_name) ^ " <list of  preprocessed files>\n" )

let spec_args = [
    ("-o", Arg.String set_output, "Set the name of the output file (default: first_file.cil if the input files start with first_file)")
  ]


let _ =
  let () =
    try
      Cil.initCIL ()
    with
    | e ->
       begin
	 prerr_endline ("Unknown error while configuring the C parsing library");
	 raise e
       end
  in
  begin
    Arg.parse spec_args add_pp_file usage_msg;
    let files = List.map parse_preprocessed !pp_files in
    let cil = merge files in
    saveBinaryFile cil (force_option !output)
  end
