Lemma p1 : forall A B C:Prop, (A->B) -> (B->C) -> (A->C).
(* fun (A:Prop) (B:Prop) (C:Prop) (H: A->B) (H0:B->C) (H1:A) => ? : C *)
(* fun (A:Prop) (B:Prop) (C:Prop) (H: A->B) (H0:B->C) (H1:A) => H0 (H H1) : C *)
Proof.
Show Proof.
intros.
Show Proof.
apply H0.
Show Proof.
apply H.
Show Proof.
exact H1.
Show Proof.
Qed.

Print p1.


Lemma and_comm : forall A B:Prop, A /\ B -> B /\ A.
(* fun (A:Prop) (B:Prop) (H:A/\B) => ? : B/\A *)
Check and_ind.
Print and.
(* fun (A:Prop) (B:Prop) (H:A/\B) => 
and_ind A B B/\A (fun (x:A) (y:B) => (conj  B A y x) H : B/\A *)
Proof.
intros.
Show Proof.
elim H.
Show Proof.
intros.
Show Proof.
apply conj.
assumption.
assumption.
Show Proof.
Qed.
Print and_comm.

Print list.

Fixpoint lg {A:Set} (l:list A) : nat :=
match l with
| nil => O
| cons _ xs => S (lg xs)
end.

Fixpoint app {A:Set} (l m:list A) : list A :=
match l with 
| nil => m
| cons x xs => cons x (app xs m)
end.

Lemma lg_app : forall A:Set, forall l m:list A,
lg (app l m) = lg l + lg m.
Proof.
intros A l m.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma plus_ass : forall a b c:nat, 
  plus a (plus b c) = plus (plus a b) c.
Proof.
induction a.
simpl.
reflexivity.
intros.
simpl.
rewrite IHa.
reflexivity.
Qed.


