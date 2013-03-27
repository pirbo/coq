Definition ireflTY A (a : A) : Irr := iJMeq a a.

Axiom irefl : forall A a, iPrf (ireflTY A a).
Axiom iAll : forall (S : Type) (P : S -> Irr), Irr.

Definition casK A a (p : iPrf (ireflTY A a)): p = irefl A a :=
  eq_refl.

Fixpoint iplus_n_Sm (m n : nat) : iPrf (iJMeq (m + S n) (S m + n)) :=
match m return iPrf (iJMeq (m + S n) (S m + n)) with
  | 0 => irefl _ (S n)
  | S m' => isubst (m' + S n) (S m' + n) (iplus_n_Sm m' n) (fun x : nat => iPrf (iJMeq (S m' + S n) (S x)))
    (irefl _ (S m' + S n))
end.

Require Plus.

Lemma iplus_tail_plus m : forall n, iPrf (iJMeq (Plus.tail_plus m n) (m + n)).
Proof.
induction m.
exact (fun n => irefl _ n).
intro n.
refine ((fun a => isubst (m + S n) (S m + n) (iplus_n_Sm m n)
  (fun x : nat => iPrf (iJMeq (Plus.tail_plus (S m) n) x)) a) _).
exact (IHm (S n)).
Qed.

Require Vector.
Import Vector.VectorNotations.
Print Vector.rev_append.

Definition irev_append {A : Type} {n p : nat} (v : Vector.t A n) (w : Vector.t A p) :=
isubst  (Plus.tail_plus n p) (n + p) (iplus_tail_plus n p) (Vector.t A) (Vector.rev_append_tail v w).

Section test_suite.
Fail Definition silly := iPrf (True).
Fail Check (eq_refl:1 = 2).

Variable xx : nat.
Variable v1 v2 : Vector.t nat xx.
Variable v'1 v'2 : Vector.t nat 2.
Eval lazy in (Vector.rev_append (0 :: v'1) v'2).
Eval lazy in (irev_append (0 :: v1) v2).
Eval lazy in (irev_append (0 :: v'1) v'2).

Definition useless m n (f : Fin.t (S (n + m))) :=
  isubst (S (n + m)) (S n + m) (irefl nat (S (n + m))) Fin.t f.

End test_suite.