Lemma ex1 : forall A : Prop, A -> A.
Proof.
  intros A H.
  exact H.
Qed.

Check ex1.

Lemma ex1' : forall A : Prop, A -> A.
Proof.
  intros A H.
  assumption.
Qed.

Lemma K : forall A B : Prop, A -> B -> A.
Proof.
  intros A B HA HB.
  assumption.
Qed.


Check K.

Lemma S : forall A B C : Prop,
    (A->B->C) -> (A->B) -> A -> C.
Proof.
  intros A B C HABC HAB HA.
  apply HABC.
  assumption.
  apply HAB.
  assumption.
Qed.

Check S.

Lemma and_comm : forall A B:Prop, A/\B -> B/\A.
Proof.
  intros A B HAB.
  split.
  elim HAB.
  intros HA HB.
  assumption.
  elim HAB.
  intros HA HB.
  assumption.
Qed.

Check and_comm.
(* ici on regarde l'énoncé de and_comm *)

Lemma and_comm' : forall A B : Prop, A/\B->B/\A.
Proof.
  intros A B HAB.
  elim HAB.
  intros HA HB.
  split.
  assumption.
  assumption.
Qed.

Check and_comm'.

Lemma or_comm : forall A B : Prop, A\/B -> B\/A.
Proof.
  intros A B HAB.
  elim HAB.
  intros HA.
  right.
  assumption.
  intros HB.
  left.
  assumption.
 Qed. 

Check or_comm.

Lemma or_comm' : forall A B : Prop, A\/B -> B\/A.
Proof.
  intros A B HAB.
  elim HAB.
  intros HA; right; assumption.
  intros HB; left; assumption.
Qed.

Check or_comm'.