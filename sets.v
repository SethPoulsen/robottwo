Require Import ssreflect.
Require Import Ensembles.

Variable U : Type.


Lemma in_complements_notin_union: forall (A B: Ensemble U) (x: U),
    In U (Complement U A) x -> In U (Complement U B) x -> 
        ~ In U (Union U A B) x.
Proof.
intros. 
(* unfold not. *)
move=> inAuB.
destruct inAuB.

(* case x \in A *)
destruct H.
apply H1.

(* case x \in B *)
destruct H0.
apply H1.
Qed.

(* What is a sensible way to generate proofs where the goal includes a negation, given 
that the Coq standard library defines `~ P` as `P -> False`? *)

Lemma demorgan1: forall A B: Ensemble U, 
    Included U 
        (Intersection U (Complement U A) (Complement U B)) 
        (Complement U (Union U A B)).
Proof.
intros. 
move=> U1. (* Why do I need this one? something strange about the way the universe type U interacts with the definitions. *)
move=> inA.
destruct inA.   
apply in_complements_notin_union.
apply H.
apply H0. Show Proof.
Qed.

Lemma union_subset_bigger_union: forall A B C: Ensemble U,
    Included U
        (Union U A B)
        (Union U A (Union U B C)).
Proof. 
    intros. 
    move=> U1. 
    move=> inAuB.
    destruct inAuB.
    (* Case 1, x \in A *)
    apply Union_introl.
    apply H.
    (* Case 2, x \in B*)
    apply Union_intror.
    apply Union_introl.
    apply H.
Qed.
    


(* Doing this stuff with `In` is weird because it should be translated the same as `:` for the 
proofs that I want to write I guess? But its really annoying to deal with and makin that 
happen is going to be a pain. This *is* related to the U thing from above *)

(* TODO can I have all the Ensemble stuff automatically parametrised by U throughout so that I 
don't have to keep explicitly stating it? *)