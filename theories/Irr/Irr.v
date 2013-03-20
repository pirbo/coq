Definition ireflTY A (a : A) : Irr := iJMeq a a.

Axiom irefl : forall A a, iPrf (ireflTY A a).
Axiom iAll : forall (S : Type) (P : S -> Irr), Irr.

Fail Definition silly := iPrf (True).


Require Fin.


Definition useless m n (f : Fin.t (S (n + m))) :=
  isubst (S (n + m)) (S n + m) (irefl nat (S (n + m))) Fin.t f.