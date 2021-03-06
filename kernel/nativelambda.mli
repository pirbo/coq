(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Pre_env
open Nativevalues

(** This file defines the lambda code generation phase of the native compiler *)

type lambda =
  | Lrel          of name * int 
  | Lvar          of identifier
  | Lmeta         of metavariable * lambda (* type *)
  | Levar         of existential * lambda (* type *)
  | Lprod         of lambda * lambda 
  | Llam          of name array * lambda  
  | Llet          of name * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of string * constant (* prefix, constant name *)
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
                  (* annotations, term being matched, accu, branches *)
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
  | Lmakeblock    of string * constructor * int * lambda array
                  (* prefix, constructor name, constructor tag, arguments *)
	(* A fully applied constructor *)
  | Lconstruct    of string * constructor (* prefix, constructor name *)
	(* A partially applied constructor *)
  | Lval          of Nativevalues.t
  | Lsort         of sorts
  | Lind          of string * inductive (* prefix, inductive name *)
  | Llazy
  | Lforce

and lam_branches = (constructor * name array * lambda) array 

and fix_decl =  name array * lambda array * lambda array

type evars =
    { evars_val : existential -> constr option;
      evars_typ : existential -> types;
      evars_metas : metavariable -> types }

val empty_evars : evars

val decompose_Llam : lambda -> Names.name array * lambda
val decompose_Llam_Llet : lambda -> (Names.name * lambda option) array * lambda

val is_lazy : constr -> bool
val mk_lazy : lambda -> lambda

val get_allias : env -> constant -> constant

val lambda_of_constr : env -> evars -> Constr.constr -> lambda
