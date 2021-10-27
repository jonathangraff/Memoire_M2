Require Import Lia.
Require Import Arith.
Lemma ex_1 : forall A B C: Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
intros.
(* intuition.*)
destruct H as [H1 H9].
destruct H9 as [H2 H3].
split. split.
intuition.
intuition. intuition.
Qed.

Lemma ex_2 : forall A B C D: Prop, (A->B)/\(C->D)/\A/\C -> B/\D.
Proof. 
intros.
(* intuition. *)
destruct H as [H1 Ha]. destruct Ha as [H2 Hb]. destruct Hb as [H3 H4].
split .
apply H1.
intuition.
apply H2. intuition.
Qed.

Lemma ex_3 : forall A: Prop, ~(A/\~A).
Proof.
intros.
intros H. 
destruct H as [H1 H2].
case H2.
exact H1.
Qed.

Lemma ex4 : forall A B C : Prop, A\/(B\/C)->(A\/B)\/C.
Proof. intros.
destruct H as [H1|H2].
left. left. exact H1.
destruct H2 as [H3 |H4] .
left. right. exact H3.
right. assumption.
Qed. 

Lemma ex5 : forall A B : Prop, (A\/B)/\~A ->B.
intros.
destruct H as [H1 H2].
destruct H1 as [H0 |H8].
case H2. exact H0. exact H8.
Qed.

Lemma ex6 : forall A : Type, forall P Q : A -> Prop, (forall x, P x)
\/(forall y, Q y)-> forall x, P x \/ Q x.
Proof. 
intros.
destruct H as [H1|H2].
left. 
apply H1.
right.
apply H2.





