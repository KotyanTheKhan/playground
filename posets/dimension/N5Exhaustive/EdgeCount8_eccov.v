(** Permutation invariance of [edge_count_5]: it depends only on the set of
    five elements, not their order.  Proved once (5^5 destruct over the cover)
    and reused by every count-8 closure so those need only a 25-case (x,y)
    enumeration instead of a 5^7 cartesian blow-up. *)

From Stdlib Require Import Arith Lia Classical.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount.

Lemma edge_count_5_cover_invariant :
  forall {B : Type} (R2 : B -> B -> Prop) (a b c d e p q r s t : B),
    (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
    p <> q -> p <> r -> p <> s -> p <> t ->
    q <> r -> q <> s -> q <> t -> r <> s -> r <> t -> s <> t ->
    edge_count_5 R2 a b c d e = edge_count_5 R2 p q r s t.
Proof.
  intros B R2 a b c d e p q r s t Hcov
         Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst.
  unfold edge_count_5.
  destruct (Hcov p) as [?|[?|[?|[?|?]]]];
  destruct (Hcov q) as [?|[?|[?|[?|?]]]];
  destruct (Hcov r) as [?|[?|[?|[?|?]]]];
  destruct (Hcov s) as [?|[?|[?|[?|?]]]];
  destruct (Hcov t) as [?|[?|[?|[?|?]]]];
  subst; try congruence; lia.
Qed.
