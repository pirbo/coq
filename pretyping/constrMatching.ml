(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open Errors
open Util
open Names
open Globnames
open Nameops
open Termops
open Reductionops
open Term
open Vars
open Context
open Pattern
open Patternops
open Misctypes
(*i*)

(* Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using [SOAPP] to
   terms, this function will perform second-order, binding-preserving,
   matching, in the case where the pattern is a pattern in the sense
   of Dale Miller.

   ALGORITHM:

   Given a pattern, we decompose it, flattening Cast's and apply's,
   recursing on all operators, and pushing the name of the binder each
   time we descend a binder.

   When we reach a first-order variable, we ask that the corresponding
   term's free-rels all be higher than the depth of the current stack.

   When we reach a second-order application, we ask that the
   intersection of the free-rels of the term and the current stack be
   contained in the arguments of the application, and in that case, we
   construct a LAMBDA with the names on the stack.

 *)

type bound_ident_map = Id.t Id.Map.t

exception PatternMatchingFailure

let warn_bound_meta name =
  msg_warning (str "Collision between bound variable " ++ pr_id name ++
    str " and a metavariable of same name.")

let warn_bound_bound name =
  msg_warning (str "Collision between bound variables of name " ++ pr_id name)

let warn_bound_again name =
  msg_warning (str "Collision between bound variable " ++ pr_id name ++
    str " and another bound variable of same name.")

let constrain n (ids, m as x) (names, terms as subst) =
  try
    let (ids', m') = Id.Map.find n terms in
    if List.equal Id.equal ids ids' && eq_constr m m' then subst
    else raise PatternMatchingFailure
  with Not_found ->
    let () = if Id.Map.mem n names then warn_bound_meta n in
    (names, Id.Map.add n x terms)

let add_binders na1 na2 (names, terms as subst) = match na1, na2 with
| Name id1, Name id2 ->
  if Id.Map.mem id1 names then
    let () = warn_bound_bound id1 in
    (names, terms)
  else
    let names = Id.Map.add id1 id2 names in
    let () = if Id.Map.mem id1 terms then warn_bound_again id1 in
    (names, terms)
| _ -> subst

let build_lambda toabstract stk (m : constr) =
  let rec buildrec m k stk = match stk with
  | [] -> m
  | (_, na, t) :: tl ->
    if Int.Set.mem k toabstract then
      buildrec (mkLambda (na, t, m)) (k + 1) tl
    else
      buildrec (lift (-1) m) (k + 1) tl
  in
  buildrec m 1 stk

let rec extract_bound_aux k accu frels stk = match stk with
| [] -> accu
| (na1, na2, _) :: stk ->
  if Int.Set.mem k frels then
    begin match na1 with
    | Name id ->
      let () = assert (match na2 with Anonymous -> false | Name _ -> true) in
      let () = if Id.Set.mem id accu then raise PatternMatchingFailure in
      extract_bound_aux (k + 1) (Id.Set.add id accu) frels stk
    | Anonymous -> raise PatternMatchingFailure
    end
  else extract_bound_aux (k + 1) accu frels stk

let extract_bound_vars frels stk =
  extract_bound_aux 1 Id.Set.empty frels stk

let dummy_constr = mkProp

let make_renaming ids = function
| (Name id, Name _, _) ->
  begin
    try mkRel (List.index Id.equal id ids)
    with Not_found -> dummy_constr
  end
| _ -> dummy_constr

let merge_binding allow_bound_rels stk n cT subst =
  let c = match stk with
  | [] -> (* Optimization *)
    ([], cT)
  | _ ->
    let frels = free_rels cT in
    if allow_bound_rels then
      let vars = extract_bound_vars frels stk in
      let ordered_vars = Id.Set.elements vars in
      let rename binding = make_renaming ordered_vars binding in
      let renaming = List.map rename stk in
      (ordered_vars, substl renaming cT)
    else
      let depth = List.length stk in
      let min_elt = try Int.Set.min_elt frels with Not_found -> succ depth in
      if depth < min_elt then
        ([], lift (- depth) cT)
      else raise PatternMatchingFailure
  in
  constrain n c subst

let matches_core convert allow_partial_app allow_bound_rels pat c =
  let conv = match convert with
    | None -> eq_constr
    | Some (env,sigma) -> is_conv env sigma in
  let rec sorec stk subst p t =
    let cT = strip_outer_cast t in
    match p,kind_of_term cT with
      | PSoApp (n,args),m ->
        let fold accu = function
        | PRel n -> Int.Set.add n accu
        | _ -> error "Only bound indices allowed in second order pattern matching."
        in
        let relargs = List.fold_left fold Int.Set.empty args in
        let frels = free_rels cT in
        if Int.Set.subset frels relargs then
          constrain n ([], build_lambda relargs stk cT) subst
        else
          raise PatternMatchingFailure

      | PMeta (Some n), m -> merge_binding allow_bound_rels stk n cT subst

      | PMeta None, m -> subst

      | PRef (VarRef v1), Var v2 when Id.equal v1 v2 -> subst

      | PVar v1, Var v2 when Id.equal v1 v2 -> subst

      | PRef ref, _ when conv (constr_of_global ref) cT -> subst

      | PRel n1, Rel n2 when Int.equal n1 n2 -> subst

      | PSort GProp, Sort (Prop Null) -> subst

      | PSort GSet, Sort (Prop Pos) -> subst

      | PSort (GType _), Sort (Type _) -> subst

      | PApp (p, [||]), _ -> sorec stk subst p t

      | PApp (PApp (h, a1), a2), _ ->
          sorec stk subst (PApp(h,Array.append a1 a2)) t

      | PApp (PMeta meta,args1), App (c2,args2) when allow_partial_app ->
          let p = Array.length args2 - Array.length args1 in
          if p >= 0 then
            let args21, args22 = Array.chop p args2 in
	    let c = mkApp(c2,args21) in
            let subst =
              match meta with
              | None -> subst
              | Some n -> merge_binding allow_bound_rels stk n c subst in
            Array.fold_left2 (sorec stk) subst args1 args22
          else raise PatternMatchingFailure

      | PApp (c1,arg1), App (c2,arg2) ->
        (try Array.fold_left2 (sorec stk) (sorec stk subst c1 c2) arg1 arg2
         with Invalid_argument _ -> raise PatternMatchingFailure)

      | PExt (c1,arg1), Ext (c2,arg2) when Extensions.equal c1 c2 ->
        (try Array.fold_left2 (sorec stk) subst arg1 arg2
         with Invalid_argument _ -> raise PatternMatchingFailure)

      | PProd (na1,c1,d1), Prod(na2,c2,d2) ->
	  sorec ((na1,na2,c2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PLambda (na1,c1,d1), Lambda(na2,c2,d2) ->
	  sorec ((na1,na2,c2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PLetIn (na1,c1,d1), LetIn(na2,c2,t2,d2) ->
	  sorec ((na1,na2,t2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PIf (a1,b1,b1'), Case (ci,_,a2,[|b2;b2'|]) ->
	  let ctx,b2 = decompose_lam_n_assum ci.ci_cstr_ndecls.(0) b2 in
	  let ctx',b2' = decompose_lam_n_assum ci.ci_cstr_ndecls.(1) b2' in
	  let n = rel_context_length ctx in
          let n' = rel_context_length ctx' in
	  if noccur_between 1 n b2 && noccur_between 1 n' b2' then
	    let s =
	      List.fold_left (fun l (na,_,t) -> (Anonymous,na,t)::l) stk ctx in
	    let s' =
	      List.fold_left (fun l (na,_,t) -> (Anonymous,na,t)::l) stk ctx' in
	    let b1 = lift_pattern n b1 and b1' = lift_pattern n' b1' in
	    sorec s' (sorec s (sorec stk subst a1 a2) b1 b2) b1' b2'
          else
            raise PatternMatchingFailure

      | PCase (ci1,p1,a1,br1), Case (ci2,p2,a2,br2) ->
	  let n2 = Array.length br2 in
          let () = match ci1.cip_ind with
          | None -> ()
          | Some ind1 ->
            (** ppedrot: Something spooky going here. The comparison used to be
                the generic one, so I may have broken something. *)
            if not (eq_ind ind1 ci2.ci_ind) then raise PatternMatchingFailure
          in
          let () =
            if not ci1.cip_extensible && not (Int.equal (List.length br1) n2)
            then raise PatternMatchingFailure
          in
	  let chk_branch subst (j,n,c) =
	    (* (ind,j+1) is normally known to be a correct constructor
	       and br2 a correct match over the same inductive *)
	    assert (j < n2);
	    sorec stk subst c br2.(j)
	  in
	  let chk_head = sorec stk (sorec stk subst a1 a2) p1 p2 in
	  List.fold_left chk_branch chk_head br1

      |	PFix c1, Fix _ when eq_constr (mkFix c1) cT -> subst
      |	PCoFix c1, CoFix _ when eq_constr (mkCoFix c1) cT -> subst
      | _ -> raise PatternMatchingFailure

  in
  sorec [] (Id.Map.empty, Id.Map.empty) pat c

let matches_core_closed convert allow_partial_app pat c =
  let names, subst = matches_core convert allow_partial_app false pat c in
  (names, Id.Map.map snd subst)

let extended_matches = matches_core None true true

let matches pat c = snd (matches_core_closed None true pat c)

let special_meta = (-1)

type matching_result =
    { m_sub : bound_ident_map * patvar_map;
      m_ctx : constr; }

let mkresult s c n = IStream.Cons ( { m_sub=s; m_ctx=c; } , (IStream.thunk n) )

let isPMeta = function PMeta _ -> true | _ -> false

let matches_head pat c =
  let head =
    match pat, kind_of_term c with
    | PApp (c1,arg1), App (c2,arg2) ->
        if isPMeta c1 then c else
        let n1 = Array.length arg1 in
        if n1 < Array.length arg2 then mkApp (c2,Array.sub arg2 0 n1) else c
    | c1, App (c2,arg2) when not (isPMeta c1) -> c2
    | _ -> c in
  matches pat head

(* Tells if it is an authorized occurrence and if the instance is closed *)
let authorized_occ partial_app closed pat c mk_ctx next =
  try
    let sigma = matches_core_closed None partial_app pat c in
    if closed && Id.Map.exists (fun _ c -> not (closed0 c)) (snd sigma)
    then next ()
    else mkresult sigma (mk_ctx (mkMeta special_meta)) next
  with PatternMatchingFailure -> next ()

(* Tries to match a subterm of [c] with [pat] *)
let sub_match ?(partial_app=false) ?(closed=true) pat c =
  let rec aux c mk_ctx next =
  match kind_of_term c with
  | Cast (c1,k,c2) ->
      let next_mk_ctx lc = mk_ctx (mkCast (List.hd lc, k,c2)) in
      let next () = try_aux [c1] next_mk_ctx next in
      authorized_occ partial_app closed pat c mk_ctx next
  | Lambda (x,c1,c2) ->
      let next_mk_ctx lc = mk_ctx (mkLambda (x,List.hd lc,List.nth lc 1)) in
      let next () = try_aux [c1;c2] next_mk_ctx next in
      authorized_occ partial_app closed pat c mk_ctx next
  | Prod (x,c1,c2) ->
      let next_mk_ctx lc = mk_ctx (mkProd (x,List.hd lc,List.nth lc 1)) in
      let next () = try_aux [c1;c2] next_mk_ctx next in
      authorized_occ partial_app closed pat c mk_ctx next
  | LetIn (x,c1,t,c2) ->
      let next_mk_ctx = function
      | [c1;c2] -> mkLetIn (x,c1,t,c2)
      | _ -> assert false
      in
      let next () = try_aux [c1;c2] next_mk_ctx next in
      authorized_occ partial_app closed pat c mk_ctx next
  | App (c1,lc) ->
      let next () =
        let topdown = true in
        if partial_app then
          if topdown then
            let lc1 = Array.sub lc 0 (Array.length lc - 1) in
            let app = mkApp (c1,lc1) in
            let mk_ctx = function
              | [app';c] -> mk_ctx (mkApp (app',[|c|]))
              | _ -> assert false in
            try_aux [app;Array.last lc] mk_ctx next
          else
            let rec aux2 app args next =
              match args with
              | [] ->
                  let mk_ctx le =
                    mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
                  try_aux (c1::Array.to_list lc) mk_ctx next
              | arg :: args ->
                  let app = mkApp (app,[|arg|]) in
                  let next () = aux2 app args next in
                  let mk_ctx ce = mk_ctx (mkApp (ce, Array.of_list args)) in
                  aux app mk_ctx next in
            aux2 c1 (Array.to_list lc) next
        else
          let mk_ctx le =
            mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
          try_aux (c1::Array.to_list lc) mk_ctx next
      in
      authorized_occ partial_app closed pat c mk_ctx next
  | Case (ci,hd,c1,lc) ->
      let next_mk_ctx = function
      | [] -> assert false
      | c1 :: lc -> mk_ctx (mkCase (ci,hd,c1,Array.of_list lc))
      in
      let next () = try_aux (c1 :: Array.to_list lc) next_mk_ctx next in
      authorized_occ partial_app closed pat c mk_ctx next
  | Fix (indx,(names,types,bodies)) ->
    let nb_fix = Array.length types in
    let next_mk_ctx le =
      let (ntypes,nbodies) = CList.chop nb_fix le in
      mk_ctx (mkFix (indx,(names, Array.of_list ntypes, Array.of_list nbodies))) in
    let next () =
      try_aux
	((Array.to_list types)@(Array.to_list bodies)) next_mk_ctx next in
    authorized_occ partial_app closed pat c mk_ctx next
  | CoFix (i,(names,types,bodies)) ->
    let nb_fix = Array.length types in
    let next_mk_ctx le =
      let (ntypes,nbodies) = CList.chop nb_fix le in
      mk_ctx (mkCoFix (i,(names, Array.of_list ntypes, Array.of_list nbodies))) in
    let next () =
      try_aux ((Array.to_list types)@(Array.to_list bodies)) next_mk_ctx next in
    authorized_occ partial_app closed pat c mk_ctx next
  | Construct _ | Ind _|CoFix _ |Evar _|Const _
  | Rel _|Meta _|Var _|Sort _ | Ext _ ->
      authorized_occ partial_app closed pat c mk_ctx next

  (* Tries [sub_match] for all terms in the list *)
  and try_aux lc mk_ctx next =
    let rec try_sub_match_rec lacc = function
      | [] -> next ()
      | c::tl ->
          let mk_ctx ce = mk_ctx (List.rev_append lacc (ce::tl)) in
          let next () = try_sub_match_rec (c::lacc) tl in
          aux c mk_ctx next in
    try_sub_match_rec [] lc in
  let lempty () = IStream.Nil in
  let result () = aux c (fun x -> x) lempty in
  IStream.thunk result

let match_subterm pat c = sub_match pat c

let match_appsubterm pat c = sub_match ~partial_app:true pat c

let match_subterm_gen app pat c = sub_match ~partial_app:app pat c

let is_matching pat c =
  try let _ = matches pat c in true
  with PatternMatchingFailure -> false

let is_matching_head pat c =
  try let _ = matches_head pat c in true
  with PatternMatchingFailure -> false

let is_matching_appsubterm ?(closed=true) pat c =
  let results = sub_match ~partial_app:true ~closed pat c in
  not (IStream.is_empty results)

let matches_conv env sigma c p =
  snd (matches_core_closed (Some (env,sigma)) false c p)

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false
