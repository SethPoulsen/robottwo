Require Import ZArith.
Require Import ZArithRing.
Require Import Zcomplements.

Unset Standard Proposition Elimination Names.

(** Divisibility *)

Definition divide (a b : Z) : Prop := exists q : Z, b = (q * a)%Z.

Notation "( x | y )" := (divide x y) (at level 0) : Z_scope.

Local Open Scope Z_scope.


(** Results *)

Lemma divide_refl : forall a : Z, (a | a).
Proof.
intros. Admitted.
(* apply divide_intro with 1; ring. *)
(* Qed. *)


Lemma divide_refl_d: forall a: Z, (a | a).
Proof. 
intros. unfold divide. exists 1. ring. 
Qed. 

(* ========================================== *)
Lemma divide_mult_left : forall a b c : Z, (a | b) -> ((c * a)%Z | (c * b)%Z).
Proof.
intros. unfold divide.
destruct H. 
exists x.  
rewrite H. 
ring.
Qed.  




Require Import Zdiv.
Require Import ZArith.Zorder.
Require Import ssreflect.

Definition gcd (a b d : Z) : Prop := (d | a)%Z /\ (d | b)%Z /\
      (forall x : Z, ((x | a)%Z /\ (x | b)%Z) -> (d >= x)%Z).

(** Trivial properties of [gcd] *)

Lemma gcd_sym : forall a b d : Z, gcd a b d -> gcd b a d.
Proof.
intros. destruct H. destruct H0.
split. apply H0. split. apply H.
intros. 
apply H1. 
split. 
destruct H2. apply H3. 
destruct H2. apply H2.
Qed.  
 


Lemma gcd_0 : forall a : Z, gcd a 0 a.
Proof.
intro.
split.
exists 1%Z.
ring.
split.
exists 0%Z. 
ring.
intro. move => H.
destruct H.
destruct H.
destruct H0.
rewrite H.

Admitted.



Lemma gcd_minus : forall a b d : Z, gcd a (- b) d -> gcd b a d.
Proof.
 intros. split. 
destruct H.
destruct H0.
Admitted.



Lemma gcd_mult : forall a b c d : Z, gcd a b d -> gcd (c * a) (c * b) (c * d).
intros.
split.
destruct H.
destruct H.
exists x.
rewrite H.
ring.
split.
destruct H.
destruct H0.
destruct H0.
exists x.
rewrite H0.
ring.
intros.
destruct H.
destruct H1.
(*apply H2.*)
replace (c * d >= x)%Z with (d >= x / c)%Z.
apply H2.
split.
destruct H0.
destruct H0.
exists x0.
Admitted.