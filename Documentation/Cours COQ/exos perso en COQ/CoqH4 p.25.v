Require Import Arith.

Fixpoint add n m :=
match n with 
0 => m
| S p => add p (S m) 
end.

Lemma ex1:  forall n m, add n (S m) = S(add n m).
Proof.
induction n.
simpl.
reflexivity.
simpl.
intro m.
rewrite IHn.
tauto.
Qed.

Lemma ex2 : forall n m, add (S n) m = S (add n m).
Proof.
assert (H1 :  forall n m, add (S n) m =add n (S m)).
simpl.
intros.
tauto.
intros.
rewrite H1.
apply ex1.
Qed.

Lemma ex3 : forall n m, add n m = n+m.
Proof.
induction n.
simpl; tauto.
intro m.
rewrite ex2.
rewrite IHn.
ring.
Qed.

Fixpoint sum_odd_n (n:nat) : nat :=
match n with 0 => 0 | S p => 1 + 2 * p + sum_odd_n p end.

Lemma xxx : forall n:nat, sum_odd_n n = n*n.
Proof.
induction n.
simpl.
tauto.
simpl.
rewrite IHn.
ring.
Qed.

