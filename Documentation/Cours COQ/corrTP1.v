Check True.
Check False.

Lemma lemme1 : forall A B C : Prop, (A -> B) -> (B->C) -> (A->C).
Proof.
  intros A B C HAB HBC HA.
apply HBC.
apply HAB.
exact HA.
Qed.

Lemma lemme2 : forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B HAB.
  split.  
  Show 2.
  elim HAB.
  
  intros.
  assumption.

  elim HAB.
  intros.
  assumption.
Qed.

Lemma lemme2' : forall A B : Prop, A /\ B -> B /\ A.
Proof.
intuition.
  
  intros A B HAB.
  elim HAB.
  intros.
  split.
  assumption.
  assumption.
Qed.
