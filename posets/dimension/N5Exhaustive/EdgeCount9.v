(** edge_count_5 = 9 case for the n=5 dispatcher.

    FOCUSED ADMIT (2026-05-29): every 5-element poset with exactly 9
    comparable pairs has a 2-realizer (dimension <= 2).  True by Hiraguchi
    (every poset on <= 5 elements has dim <= 2; the smallest 3-dimensional
    poset, the standard example S_3, has 6 elements).

    Introduced by the master edge-count dispatch in [N5DispatcherShapes.v]
    to refine the monolithic [n5_residual_classes_two_realizer] admit into
    per-edge-count obligations.  The [EdgeCount4] reflection-enumeration
    template does NOT scale here (C(25,9) edge-sets is infeasible for
    native_compute), so the closing technique is still pending.  See
    docs/superpowers/plans/2026-05-29-admit1-n5-residual.md. *)

From Stdlib Require Import List Classical Arith Lia.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount9.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma n5_edge_count_9_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 9 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Admitted.

End EdgeCount9.
