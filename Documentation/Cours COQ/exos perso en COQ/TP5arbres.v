Require Import Arith.
Require Import Max.
Require Import List.

Inductive btree: Type :=
N: nat->btree
|Cg : nat->btree->btree
|Cd : nat->btree->btree
|C : nat->btree->btree->btree.

Check btree_ind.

Fixpoint mirror t:btree :=
match t with 
N n =>N n
|Cg n t1 =>Cd n (mirror t1)
|Cd n t1 => Cg n (mirror t1)
| C n t1 t2 => C n (mirror t2) (mirror t1)
end.

Definition tree := C 0 (Cg 1 (N 3)) (Cd 2 (C 4 (N 5)(N 6))).

Eval compute in mirror (tree).

Lemma idempotente : forall t:btree, mirror (mirror t) = t.
Proof. 
intros.
induction t.
reflexivity.
simpl; rewrite IHt;tauto.
simpl; rewrite IHt;tauto.
simpl.
rewrite IHt1.
rewrite IHt2.
tauto.
Qed.

Fixpoint tmap (f:nat->nat) (t:btree) :=
match t with 
N n => N (f n)
|Cg n t1 => Cg (f n) (tmap f t1) 
|Cd n t1 => Cd (f n) (tmap f t1) 
|C n t1 t2 => C (f n) (tmap f t1) (tmap f t2)
end.

Eval compute in tmap (fun x=>x*x) tree.

Lemma ex5 : forall (f g: nat->nat) (a: btree),
tmap f (tmap g a) = tmap (fun x => f (g x)) a.
Proof. 
intros.
induction a.
reflexivity.
simpl; rewrite IHa; tauto.
simpl; rewrite IHa; tauto.
simpl.
rewrite IHa1.
rewrite IHa2.
tauto.
Qed.

Fixpoint btree_to_list (t:btree) :=
match t with 
N n => n::nil
| Cg n t =>btree_to_list t++(n::nil)
| Cd n t =>n::btree_to_list t
|C n t1 t2 => (btree_to_list t1)++(n::nil)++(btree_to_list t2)
end.

Eval compute in btree_to_list tree.

Lemma interm : forall (f:nat->nat) (l1 l2:list nat), map f (l1++l2) =
(map f l1)++(map f l2) .
Proof.
intros.
induction l1.
reflexivity;simpl;rewrite IHl1;tauto.
simpl;rewrite IHl1;tauto.
Qed.

Lemma ex7 : forall (f:nat->nat) (t:btree), map f (btree_to_list t) = 
btree_to_list (tmap f t).
Proof.
intros.
induction t.
reflexivity.
simpl.
rewrite map_app.
rewrite IHt; tauto.
simpl.
rewrite IHt.
tauto.
simpl.
rewrite map_app.
rewrite IHt1.
simpl.
rewrite IHt2.
tauto.
Qed.

Fixpoint nb_labels (t:btree) := 
match t with 
N n => 1
|Cg n t => 1+nb_labels t
|Cd n t => 1+ nb_labels t
|C n t1 t2 => 1+nb_labels t1+nb_labels t2
end.

Eval compute in nb_labels tree.

Fixpoint height (t:btree) :=
match t with 
N n =>1
|Cg n t => 1+height t
|Cd n t => 1+height t
|C n t1 t2 => 1+ max (height t1) (height t2)
end.

Eval compute in height tree.

Check max_dec.
Check plus_comm.
Check le_plus_trans.

Lemma ex10 : forall t, height t <= nb_labels t.
Proof.
intros.
induction t.
reflexivity.
simpl.
apply le_n_S.
apply IHt.
simpl.
apply le_n_S.
apply IHt.
simpl.
apply le_n_S.
case_eq (max_dec (height t1) (height t2));intros.
rewrite e.
apply le_plus_trans.
apply IHt1.
rewrite e.
rewrite plus_comm.
apply le_plus_trans.
apply IHt2.
Qed.

Fixpoint btree_in (x: nat) (t: btree) : Prop :=
match t with
| N n => n=x
| Cg n t => (btree_in x t) \/ n=x
| Cd n t => n=x \/ (btree_in x t)
| C n l r => (btree_in x l) \/ n=x \/ (btree_in x r)
end.

Lemma ex11 : forall x t, btree_in x t -> In x (btree_to_list t).
Proof.
intros.
induction t; simpl.
left.
destruct H.
tauto.

Check in_or_app.
apply in_or_app.
destruct H as [H1 |H2]. 
left. 
apply IHt. 
exact H1.
right.
simpl.
left.
exact H2.

destruct H as [H1 |H2]. 
left.
exact H1.
right.
apply IHt.
exact H2.

destruct H as [H1 |H2]. 
apply in_or_app.
left.
apply IHt1.
exact H1.
apply in_or_app.
right.
Check in_or_app.
simpl.
destruct H2.
left.
exact H.
right.
apply IHt2.
exact H.
Qed.

Lemma btree_in_mirror_1: forall t x, btree_in x t -> btree_in x (mirror t).
Proof. 
intros.
induction t;simpl; 
destruct H; tauto.
Qed.

Lemma btree_in_mirror_2: forall t x, btree_in x (mirror t) -> btree_in x t.
Proof.
intros.
rewrite <- idempotente.
apply btree_in_mirror_1 with (t:=mirror t).
exact H.
Qed.

Fixpoint btree_lt t x :=
match t with 
N n => n<x
|Cg n t' =>  n<x
|Cd n t' => btree_lt t' x
|C n t1 t2 => btree_lt t2 x
end.


Definition treeRec := C 5 (Cg 3 (N 1)) (Cd 7 (C 9 (N 8)(N 10))).

Eval compute in btree_lt treeRec 5.

Fixpoint btree_gt t x :=
match t with 
N n => n>x
|Cg n t' =>  btree_gt t' x
|Cd n t' => n>x
|C n t1 t2 => btree_gt t1 x
end.

Eval compute in btree_gt treeRec 5.

Lemma btree_in_lt: forall t x n, btree_in x t -> btree_lt t n -> x < n.
Proof. 
intros H.
inversion H; intros.

subst.
intros.