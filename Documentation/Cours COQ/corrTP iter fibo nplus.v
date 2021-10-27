Check conj.
(* forall A B : Prop, A -> B -> A /\ B *)
Check and_ind.
(* forall A B P : Prop, 
(A -> B -> P) -> A /\ B -> P *)

Lemma and_comm : forall A B:Prop, A/\B -> B/\A.
Proof.
exact (fun (A:Prop)(B:Prop) (H:A/\B) =>
      (@conj B A
             (@and_ind A B B (fun (x:A) (y:B) => y) H)
             (@and_ind A B A (fun (x:A) (y:B) => x) H))).
Qed.


Lemma and_comm' : forall A B:Prop, A/\B -> B/\A.
Proof.
  intros A  B H.
  induction H.
  split.
  assumption.
  assumption.
Qed.

Print and_comm'.

Fixpoint mplus (n m:nat) : nat :=
  match n with
    O => m 
  | S p => S (mplus p m)
  end.

Eval compute in (mplus 2 4).

Fixpoint nplus (n m :nat) : nat :=
  match n with
    O => m
  | S p => nplus p (S m)
  end.

Eval compute in (nplus 2 4).

Lemma nplus_S : forall a b:nat, S (nplus a b) = nplus a (S b).
Proof.
  intros a.
  induction a.
  simpl. reflexivity.
  simpl.
intros.  
rewrite IHa.
reflexivity.
Qed.

Lemma mplus_nplus : forall a b:nat, mplus a b= nplus a b.
  Proof.
    intros a b.
    induction a.
    simpl.
    reflexivity.
    simpl.
    rewrite IHa.
    apply nplus_S.
    Qed.

  Fixpoint iter (A:Set) (f:A->A) (x:A) (n:nat) :=
    match n with
        O => x
      | S p => iter A f (f x) p
      end.

  Fixpoint iter2 (A:Set) (f:A->A) (x:A) (n:nat) :=
    match n with
      O => x
    | S p => f (iter2 A f x p)
    end.

  Lemma iter_iter : forall A f x n, iter A f (f x) n = f (iter A f x n).
  Proof.
    intros A f x n.
    generalize x. clear x.
    induction n.
    simpl; reflexivity.
    simpl; intros.
    rewrite IHn.
    reflexivity.
    Qed.

    Lemma iter_iter2 : forall A, forall f, forall x, forall n, iter A f x n = iter2 A f x n.
  Proof.
    intros A f x n.
    induction n.
    simpl. reflexivity.
    simpl.
    rewrite <- IHn.
    apply iter_iter.
  Qed.

  Lemma mplus_assoc : forall a b c:nat,
      mplus a (mplus b c ) = mplus (mplus a b) c.
  Proof.
    intros a b c.
    induction a.
    simpl.
    reflexivity.
    simpl.
    apply f_equal.
    assumption.
  Qed.

  (* fonction de Fibonacci *)
(*  fib 0 = 0
            fib 1 = 1
                      fib n+2 = fib n+1 + fib n *)
  
  Fixpoint fib (n:nat) : nat :=
    match n with
      O => O
    | S p => match p with
               O => 1
             | S q => fib p + fib q
             end
    end.

  Lemma fib_croissante : forall n:nat, fib (S n) >= fib n.
    