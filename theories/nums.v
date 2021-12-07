From Robottwo Require Import Loader.

Require Import ZArith.
(** Divisibility *)

Definition divide (a b : Z) : Prop := exists q : Z, b = (q * a)%Z.

Notation "( x | y )" := (divide x y) (at level 0) : Z_scope .

Local Open Scope Z_scope.

Lemma divide_refl_inst: forall a: Z, (a | a).
Proof.

PreExplain intro x.
intro x.
PostExplain intro x.

PreExplain unfold divide.
unfold divide.
PostExplain unfold divide.

PreExplain exists 1.
exists 1.
PostExplain exists 1.

PreExplain ring.
ring.
PostExplain ring.
Qed.

Lemma divide_refl: forall a: Z, (a | a).
Proof.
intro x.
unfold divide.
exists 1.
ring.
Qed.

Lemma divide_mult_left : forall a b c : Z, (a | b) -> ((c * a)%Z | (c * b)%Z).
Proof.
intros. unfold divide.
destruct H.
exists x.
rewrite H.
ring.
Qed.

Lemma divide_mult_left_inst : forall a b c : Z, (a | b) -> ((c * a)%Z | (c * b)%Z).
Proof.

PreExplain intro a.
intro a.
PostExplain intro a.

PreExplain intro b.
intro b.
PostExplain intro b.

PreExplain intro c.
intro c.
PostExplain intro c.

PreExplain unfold divide.
unfold divide.
PostExplain unfold divide.

PreExplain intro H.
intro H.
PostExplain intro H.

PreExplain destruct H.
destruct H.
PostExplain destruct H.

PreExplain exists x.
exists x.
PostExplain exists x.

PreExplain rewrite H.
rewrite H.
PostExplain rewrite H.

PreExplain ring.
ring.
PostExplain ring.
Qed.
