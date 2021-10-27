Require Import Arith.

Fixpoint sum_integers (n:nat) :=
    match n with 
    | 0 => 0
    | S p => p + 1 + (sum_integers p)
    end.

Lemma sum_integers_explicit : forall n:nat, 2*(sum_integers n) = n*(n+1).

Proof.
intros.
induction n.
intuition.
simpl.
repeat rewrite Plus.plus_assoc.
rewrite Nat.add_0_r.
repeat rewrite plus_n_Sm.
ring_simplify.
rewrite IHn.
ring.
Qed.




















