(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Tacmach
open Names
open Tacexpr
open Locus

val instantiate : int -> Tacinterp.interp_sign * Glob_term.glob_constr ->
  (Id.t * hyp_location_flag, unit) location -> tactic

val let_evar : Name.t -> Term.types -> unit Proofview.tactic
