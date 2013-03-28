(** I cheat, unification is not able to do anything with the primitives
     but by using constants as synonym, it works :-) *)
Definition Irr := Irr_prim.
Definition iPrf (P: Irr) := iPrf_prim P.
Definition iJMeq {A B} (a : A) (b : B) := iJMeq_prim a b.
Definition isubst {A} (a b: A) (eq: iPrf (iJMeq a b)) (P: A -> Type)
  (p: P a) := isubst_prim a b eq P p.

Definition ireflTY A (a : A) : Irr := iJMeq a a.

Axiom irefl : forall {A} a, iPrf (ireflTY A a).
Axiom iAll : forall (S : Type) (P : S -> Irr), Irr.
Definition iK A a (p : iPrf (ireflTY A a)): iPrf (iJMeq p (irefl a)) := irefl _.

Definition compK {X} (x: X) (q: x = x): q = eq_refl.
Proof.
assert (forall (x': X) (q': x = x'), iPrf (iJMeq x x') -> iPrf (iJMeq q q') -> q = eq_refl).
{ destruct q'. intros ieq_x ieq_q. exact (isubst _ _ ieq_q _ eq_refl). }
apply (H x q); exact (irefl _).
Defined.

Eval lazy in (fun X (x: X) => compK x eq_refl).

Section test_suite.
Fail Definition silly := iPrf (True).
Fail Check (eq_refl:1 = 2).

Definition useless m n (f : Fin.t (S (n + m))) := isubst _ _ (irefl (S (n + m))) Fin.t f.

End test_suite.
