open Environ
open Extensions

let retype e args =
  if equal e irr then (Constr.mkSort Sorts.type1)
  else if equal e iprf then (Constr.mkProp)
  else if equal e ijmeq then  (Constr.mkExt (irr,[||]))
  else if equal e isubst then
    (Term.mkApp (args.(3),[|args.(1)|]))
  else Errors.anomaly (Pp.str ("missing type for Ext#"^(to_string e)))

let make_irr_judge e args =
  let args_val = Array.map (fun x -> x.uj_val) args in
  make_judge (Term.mkExt (e,args_val)) (retype e args_val)

let execute_extension conv_leq env e args_j =
  if equal e irr then
    let ans = make_irr_judge e args_j in
    if CArray.is_empty args_j
    then (ans,Univ.empty_constraint)
    else Type_errors.error_cant_apply_not_functional env ans args_j
  else if equal e iprf then
    let ans = make_irr_judge e args_j in
    begin
      if Int.equal (CArray.length args_j) 1
      then
	try
	  let c = conv_leq args_j.(0).uj_type (Term.mkExt (irr,[||])) in
	  (ans, c)
	with Reduction.NotConvertible ->
	  Type_errors.error_cant_apply_bad_type env
	    (1,Term.mkExt (irr,[||]),args_j.(0).uj_type) ans args_j
      else Type_errors.error_not_type env ans
    end
  else if equal e ijmeq then
    let ans = make_irr_judge e args_j in
    if Int.equal (CArray.length args_j) 2
    then (ans,Univ.empty_constraint)
    else Type_errors.error_not_type env ans
  else if equal e isubst then (* subst a b eq P h *)
    if Int.equal (CArray.length args_j) 5
    then
      let ans = make_irr_judge e args_j in
      let conv_c a b =
	try conv_leq a b
	with  Reduction.NotConvertible ->
	  Type_errors.error_cant_apply_bad_type env (1,b,a) ans args_j in
      (* ty_a = ty_b *)
      let c = conv_c args_j.(0).uj_type args_j.(1).uj_type in
      (* eq : iJMEq a b *)
      let c' = conv_c args_j.(2).uj_type
	(Term.mkExt (iprf,[|Term.mkExt (ijmeq, [|args_j.(0).uj_val; args_j.(1).uj_val|])|])) in
      (* TODO : args_j.[3].type == forall x: args_j.[0].uj_type. Sort ? *)
      (* h : P a *)
      let c'' = conv_c args_j.(4).uj_type
	(Term.mkApp (args_j.(3).uj_val, [|args_j.(0).uj_val|])) in
      let c_o = Univ.union_constraints c (Univ.union_constraints c' c'') in
      (ans, c_o)
    else Errors.anomaly (Pp.str "not correctly applied isubst")
  else Errors.anomaly (Pp.str ("missing typechecking rule for"^(to_string e)))

let reduce_extension conv_test e args =
  if equal e isubst then
    if conv_test args.(2) args.(3) then Some args.(6) else None
  else None
