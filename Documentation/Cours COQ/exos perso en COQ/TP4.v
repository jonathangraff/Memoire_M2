Require Import List.
Require Import Arith.

Fixpoint length  {A:Set} (l:list A):nat:=
match l with nil=> 0
|a::tail=>1+length tail
end.
Eval compute in length (1::5::8::3::nil).

Fixpoint map  {A B:Set} (f:A->B)  (l:list A): list B :=
match l with 
nil=>nil
|a::tail => (f a)::map f tail
end.

Eval compute in let f:=fun x=>x*x in 
map f (1::2::3::4::nil).

Lemma lgmap : forall {A B:Set}(l:list A)(f:A->B), 
length l = length (map f l).
Proof.
intros.
induction l.
simpl; tauto.
simpl.
rewrite IHl.
reflexivity.
Qed.

Definition compose {A B C : Set} (f:B->C) (g:A->B) :=
fun x => f (g x).

Eval compute in compose (fun x=>x*x) 
(fun x=>x+1) 2.

Lemma assoc : forall {A B C D:Set} (f:C->D) (g:B->C) 
(h:A->B) (x:A), compose  f (compose g h) x = 
compose (compose f g) h x.
Proof. 
intros.
unfold compose.
tauto.
Qed.

Lemma assmap : forall {A B C : Set} (f:B->C) (g:A->B)
(l: list A), map (compose f g) l = 
map f (map g l).
Proof.
intros.
unfold compose.
induction l.
unfold map;tauto.
simpl.
rewrite IHl.
tauto.
Qed.

Fixpoint append {A:Set} (l1 l2:list A):=
match l1 with 
nil=> l2
| a::tl=>a::(append tl l2)
end.

Eval compute in append (1::2::3::4::nil) (5::6::7::8::nil).

Lemma mapappend : forall {A B : Set} 
(f:A->B) (l1 l2: list A), map f (append l1 l2) = 
append (map f l1) (map f l2).
Proof.
intros.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Fixpoint reverse {A:Set} (l: list A):=
match l with 
nil => nil
|a::tl =>append (reverse tl) (a::nil)
end.

Eval compute in reverse (1::2::3::4::nil).

Lemma revmap : forall {A B : Set} (f:A->B) (l:list A), 
map f (reverse l) = reverse (map f l).
Proof. 
intros.
induction l;simpl.
tauto.
rewrite mapappend.
rewrite IHl.
simpl.
tauto.
Qed.

Lemma appendtrans : forall {A:Set} (l m n : list A), 
append (append l m) n = append l (append m n).
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma revappend : forall {A : Set} (l1 l2 : list A), 
reverse (append l1 l2) = append (reverse l2) (reverse l1).
Proof.
intros.
induction l1.
simpl.
assert (int : forall {A:Set} (l: list A), append l nil = l).
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
tauto.
rewrite int.
tauto.
simpl.
rewrite IHl1.
rewrite appendtrans.
tauto.
Qed.

Lemma revdbl : forall {A:Set} (l:list A), 
reverse (reverse l) = l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite revappend.
rewrite IHl.
unfold reverse.
simpl.
tauto.
Qed.

Lemma app1 : forall {A:Set} (l1 l2 : list A), 
length(append l1 l2) = length l1 + length l2.
Proof.
intros.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
tauto.
Qed.

Lemma rev1 : forall {A:Set} (l:list A), 
length (reverse l) = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite app1.
rewrite IHl.
simpl.
ring.
Qed.

Fixpoint foldr {A B:Set} (f:A->B->B) (l:list A) (z:B) :=
match l with
nil =>z
|a::tl => f a (foldr f (tl) z)
end.

Eval compute in foldr (fun x y=> x*y) 
(1::2::3::nil) 5.

Lemma f16 : forall {A B : Set} (f:A->B->B) (z:B)
(l1 l2 : list A), foldr f (append l1 l2) z= 
foldr f l1 (foldr f l2 z).
Proof.
intros.
induction l1.
reflexivity.
simpl.
rewrite IHl1.
tauto.
Qed.

Lemma f17 : forall {A : Set} (f:A->A) (h:A) (q l:list A), 
foldr (fun h q =>((f h):: q)) l nil = map f l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite IHl.
tauto.
Qed.

Lemma f18 : forall {A : Set} (h:A) (l:list A) (q:nat), 
foldr (fun h q =>q+1) l 0 = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite IHl.
ring.
Qed.

Lemma f19 : forall {A : Set} (h:A) (q l:list A), 
foldr (fun h q =>(h:: q)) l nil = l.
Proof.
intros.
(* apply @f17 with (A:=B) (f := fun x=>x) (h:=k). *)
induction l.
reflexivity.
simpl.
rewrite IHl.
tauto.
Qed.

(* Definition fct:= fun (h:_) (q:list _) =>
append (reverse q) (h::nil). *)
Definition fct:= fun (h:nat) (q:list nat) =>
append (q) (h::nil).

Eval compute in fct 3 (4::5::nil).
Eval compute in foldr fct (4::5::6::7::8::nil) nil.

Lemma f20 : forall {A : Set} (h:A) (q l:list A), 
foldr (fun h q =>(append q (h::nil))) l nil = reverse l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite IHl.
tauto.
Qed.

Fixpoint foldl {A B:Set} (f:B->A->B) (l:list A) (z:B) :=
match l with
nil =>z
|a::tl => foldl f tl (f z a)
end.

Eval compute in foldl (fun x y=> (x+1)*y) 
(1::2::3::nil) 5.

(* Definition flip := fun f=> (fun x y => f y x).
 *)
Lemma ex22 : forall {A B : Set} (f:A->B->B) (z:B) (l:list A), 
foldr f (reverse l) z = foldl (fun x y => f y x) l z.
Proof.
intros.
generalize z.
clear z.
induction l.
reflexivity.
simpl.
intro.
rewrite <- IHl with (z:=f a z).
assert(inter : forall {A B : Set} (f:A->B->B) (z:B) (a:A) (l:list A), 
foldr f (append l (a::nil)) z = foldr f l (f a z)).
intros.
induction l0.
reflexivity.
simpl.
rewrite IHl0.
tauto.
apply inter. 
Qed.

Fixpoint zip {A B:Set} (l : list A) (m:list B) := 
match l with 
nil=> nil
|a::tl => match m with 
  nil=>nil
  |b::tl2=>((a,b)::zip tl tl2)
end
end.

Eval compute in zip (1::2::3::nil) (4::5::6::nil).
Eval compute in zip (1::2::nil) (4::5::6::nil).
Eval compute in zip (1::2::3::nil) (4::5::nil).

Lemma inter : forall {A B:Set}(l : list A)(m:list B) , 
m=nil->zip l m = nil.
Proof.
intros.
rewrite H.
induction l;reflexivity.
Qed.

(* Lemma ex24 : forall {A B:Set}(l1 : list A) (l2:list B) , 
length (zip l1 l2) = length (zip l2 l1).
Proof.
intros.
induction l1.
simpl.
rewrite inter;reflexivity.
simpl.
 *)

Lemma ex25 : forall {A B:Set}(l1 : list A)(l2:list B) , 
length (zip l1 l2) = length l1 \/ length (zip l1 l2) = length l2.
Proof.
intros.
induction l1.
simpl.
left;tauto.
simpl.

reflexivity.





