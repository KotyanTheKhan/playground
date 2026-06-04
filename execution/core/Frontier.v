From Stdlib Require Import Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs.
From Execution Require Import Op Event Edges Rank Poset.

#[local] Existing Instance hb_IsPoset.

Section Frontier.
  Context (E : ExecPoset).

  Definition ConsistentCut (C : Ensemble (ep_carrier E)) : Prop :=
    forall x y, ep_order E x y -> Ensembles.In _ C y -> Ensembles.In _ C x.

  Definition Frontier (F : Ensemble (ep_carrier E)) : Prop :=
    exists C, ConsistentCut C /\
      (forall x, Ensembles.In _ F x <->
         (Ensembles.In _ C x /\
          (forall y, Ensembles.In _ C y -> ep_order E x y -> y = x))).

  Definition IsBarrier (L U : Ensemble (ep_carrier E)) : Prop :=
    (forall x, Ensembles.In _ L x \/ Ensembles.In _ U x) /\
    (forall x, ~ (Ensembles.In _ L x /\ Ensembles.In _ U x)) /\
    (exists x, Ensembles.In _ L x) /\ (exists y, Ensembles.In _ U y) /\
    (forall x y, Ensembles.In _ L x -> Ensembles.In _ U y -> ep_order E x y).
End Frontier.

Lemma frontier_is_antichain :
  forall E F, Frontier E F ->
    forall x y, Ensembles.In _ F x -> Ensembles.In _ F y -> ep_order E x y -> x = y.
Proof.
  intros E F HF x y HxF HyF Hxy.
  destruct HF as [C [Hcut Hmax]].
  apply Hmax in HxF. destruct HxF as [HxC Hxmax].
  apply Hmax in HyF. destruct HyF as [HyC _].
  symmetry.
  apply Hxmax; assumption.
Qed.

Lemma barrier_lower_consistent :
  forall E L U, IsBarrier E L U -> ConsistentCut E L.
Proof.
  intros E L U HB.
  unfold ConsistentCut.
  intros x y Hxy HyL.
  destruct HB as [Hcov [Hdisj [_ [_ Hbelow]]]].
  destruct (Hcov x) as [HxL | HxU].
  - exact HxL.
  - exfalso.
    apply (Hdisj x).
    split.
    + assert (Hyx : ep_order E y x) by (apply Hbelow; assumption).
      assert (Heq : x = y) by
        (apply (poset_antisym (R := ep_order E)); assumption).
      rewrite Heq.
      exact HyL.
    + exact HxU.
Qed.

Lemma barrier_upper_disjoint_below :
  forall E L U, IsBarrier E L U ->
    forall x y, Ensembles.In _ U x -> Ensembles.In _ L y -> ~ ep_order E x y.
Proof.
  intros E L U HB x y HxU HyL Hxy.
  destruct HB as [_ [Hdisj [_ [_ Hbelow]]]].
  assert (Hyx : ep_order E y x) by (apply Hbelow; assumption).
  assert (Heq : x = y) by
    (apply (poset_antisym (R := ep_order E)); assumption).
  apply (Hdisj x).
  split.
  - rewrite Heq. exact HyL.
  - exact HxU.
Qed.
