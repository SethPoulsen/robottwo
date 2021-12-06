From Robottwo Require Import Loader.

Require Import ZArith.
(** Divisibility *)

Definition divide (a b : Z) : Prop := exists q : Z, b = (q * a)%Z.

Notation "( x | y )" := (divide x y) (at level 0) : Z_scope.

Local Open Scope Z_scope.

Lemma divide_refl_inst: forall a: Z, (a | a).
Proof.
intro x.
ExploreProof intro x.
unfold divide.
ExploreProof unfold divide.
exists 1.
ExploreProof exists 1.
ring.
ExploreProof ring.
Qed.


Lemma divide_refl: forall a: Z, (a | a).
Proof.
intros.
unfold divide.
exists 1.
ring.
Qed.
