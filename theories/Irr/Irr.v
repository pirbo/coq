Definition ireflTY A (a : A) : Irr := iJMeq a a.

Axiom irefl : forall A a, iPrf (ireflTY A a).
Axiom iAll : forall (S : Type) (P : S -> Irr), Irr.

Definition casK A a (p : iPrf (ireflTY A a)): p = irefl A a :=
  eq_refl.

Section test_suite.
Fail Definition silly := iPrf (True).
Fail Check (eq_refl:1 = 2).

Require Fin.
Definition useless m n (f : Fin.t (S (n + m))) :=
  isubst (S (n + m)) (S n + m) (irefl nat (S (n + m))) Fin.t f.

End test_suite.