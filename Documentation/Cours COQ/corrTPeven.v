Require Import Arith.

Print le.
(*
Inductive le (n : nat) : nat -> Prop :=  le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m 
*)

Lemma l1 : forall n, le n 1 -> n=0\/n=1.
Proof.
  intros n Hn.
inversion Hn.
right; reflexivity.
inversion H0.
left; reflexivity.
Qed.

Inductive even : nat -> Prop :=
|even_O : even 0
|even_SS : forall m:nat, even m -> even (S (S m)).

Definition even' n := exists k:nat, n=2*k.

Lemma l1_even : forall n, even n -> even' n.
Proof.
  intros.
  induction H.
  unfold even'.
  exists 0.
  reflexivity.
  unfold even' in IHeven.
  unfold even'.
  elim IHeven.
  intros k Hk.
  exists (S k).
  rewrite Hk.
  simpl.
  Search (_+0)%nat.
  rewrite <- plus_n_O.
  Search (_+ (S _))%nat.
  rewrite <- Nat.add_succ_comm.
  (*ring.*)
  reflexivity.
Qed.

Require Import Lia.
Lemma l_aux : forall (x:nat), 1= 2 * x -> False.
Proof.
intros; lia.
Qed.

Lemma l1_even' : forall n, even' n -> even n.
Proof.
intros n.
assert ((even' n -> even n)/\(even' (S n)-> even (S n))).
induction n.
split.
intros H0.
apply even_O.
intros.
destruct H.
assert (Hf:False) by (apply l_aux with (x:=x); assumption).
elim Hf.
destruct IHn.
split.
assumption.
intros.
apply even_SS.
apply H.
destruct H1.
unfold even'.
exists (x-1).
Search (_*(_-_)).
rewrite Nat.mul_sub_distr_l.
replace n with (S (S n) - 2)%nat.
2: do 2 rewrite Nat.sub_succ; rewrite Nat.sub_0_r; reflexivity.
replace (2*1)%nat with 2 by reflexivity.
apply f_equal with (f:=fun (x:nat) => x-2).
assumption.
destruct H; assumption.
Qed.

(*Inductive even : nat -> Prop :=
  even_O : even 0
| even_S : forall m:nat, odd m -> even (S m)
with odd : nat -> Prop :=
  odd_1 : odd 1
| odd_S : forall m:nat, even m -> odd (S m).

Lemma f : even 6.
Proof.
apply even_S.
apply odd_S.
apply even_S.
apply odd_S.
apply even_S.
exact odd_1.
Qed.
 *)

Lemma f2' : forall n m:nat, even' n -> even' m -> even' (n+m).
Proof.
intros n m Hn Hm.
destruct Hn as [k Hk].
destruct Hm as [k' Hk'].
exists (k+k').
rewrite Hk.
rewrite Hk'.
ring.
Qed.

Lemma f2 : forall n m:nat, even n -> even m -> even (n+m).
Proof.
intros.
apply l1_even'.
apply f2'.
apply l1_even.
assumption.
apply l1_even.
assumption.
Qed.


