(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)



(*s Output options *)

type target_language = LaTeX | HTML | TeXmacs | Raw

let target_language = ref HTML

type output_t =
  | StdOut
  | MultFiles
  | File of string

let output_dir = ref ""

let out_to = ref MultFiles

let out_channel = ref stdout

let coqdoc_out f =
  if !output_dir <> "" && Filename.is_relative f then
    if not (Sys.file_exists !output_dir) then
      (Printf.eprintf "No such directory: %s\n" !output_dir; exit 1)
    else
      Filename.concat !output_dir f
  else
    f

let open_out_file f =
  out_channel :=
    try open_out (coqdoc_out f)
    with Sys_error s -> Printf.eprintf "%s\n" s; exit 1

let close_out_file () = close_out !out_channel


type glob_source_t =
    | NoGlob
    | DotGlob
    | GlobFile of string

let glob_source = ref DotGlob

(*s Manipulations of paths and path aliases *)

let normalize_path p =
  (* We use the Unix subsystem to normalize a physical path (relative
     or absolute) and get rid of symbolic links, relative links (like
     ./ or ../ in the middle of the path; it's tricky but it
     works... *)
  (* Rq: Sys.getcwd () returns paths without '/' at the end *)
  let orig = Sys.getcwd () in
  Sys.chdir p;
  let res = Sys.getcwd () in
  Sys.chdir orig;
  res

let normalize_filename f =
  let basename = Filename.basename f in
  let dirname = Filename.dirname f in
  normalize_path dirname, basename

(** A weaker analog of the function in Envars *)

let guess_coqlib () =
  let file = "states/initial.coq" in
  match Coq_config.coqlib with
    | Some coqlib when Sys.file_exists (Filename.concat coqlib file) ->
      coqlib
    | Some _ | None ->
      let coqbin = normalize_path (Filename.dirname Sys.executable_name) in
      let prefix = Filename.dirname coqbin in
      let rpath = if Coq_config.local then [] else
	  (if Coq_config.arch = "win32" then ["lib"] else ["lib";"coq"]) in
      let coqlib = List.fold_left Filename.concat prefix rpath in
      if Sys.file_exists (Filename.concat coqlib file) then coqlib
      else prefix

let header_trailer = ref true
let header_file = ref ""
let header_file_spec = ref false
let footer_file = ref ""
let footer_file_spec = ref false
let quiet = ref true
let light = ref false
let gallina = ref false
let short = ref false
let index = ref true
let multi_index = ref false
let index_name = ref "index"
let toc = ref false
let page_title = ref ""
let title = ref ""
let externals = ref true
let coqlib = ref Coq_config.wwwstdlib
let coqlib_path = ref (guess_coqlib ())
let raw_comments = ref false
let parse_comments = ref false
let plain_comments = ref false
let toc_depth = (ref None : int option ref)
let lib_name = ref "Library"
let lib_subtitles = ref false
let interpolate = ref false
let inline_notmono = ref false

let charset = ref "iso-8859-1"
let inputenc = ref ""
let latin1 = ref false
let utf8 = ref false

let set_latin1 () =
  charset := "iso-8859-1";
  inputenc := "latin1";
  latin1 := true

let set_utf8 () =
  charset := "utf-8";
  inputenc := "utf8x";
  utf8 := true

(* Parsing options *)

type coq_module = string

type file =
  | Vernac_file of string * coq_module
  | Latex_file of string
