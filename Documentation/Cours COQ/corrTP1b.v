Lemma contra1 : forall A B:Prop, (A->B)->(~B->~A).
Proof.
intros.
unfold not.
intros.
unfold not in H0.
apply H0.
apply H.
assumption.
Qed.

Axiom tiers_exclu : forall P : Prop, P\/~P.

Lemma contra2 : forall A B : Prop, (~B -> ~A) -> (A -> B).
Proof.
  intros.
  elim (tiers_exclu B).
  intros.
  assumption.
  intros.
  apply False_ind.
  apply H.
  assumption.
  assumption.
Qed.

Check Prop.
Check Set.
Check Type.