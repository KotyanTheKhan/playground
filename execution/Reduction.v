(* dimension-preserving / reducing maps between posets *)

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal.

(** * Reduction relations between posets

    [PosetDimension R d] is a typeclass (lives in [Type]), so to embed it in
    [Prop]-valued definitions and statements we wrap it with [inhabited].

    Notation: [dim_at R d] abbreviates [inhabited (PosetDimension R d)]. *)

Local Notation dim_at R d := (inhabited (PosetDimension R d)).

(** [PreservesDim A R B S]: the two posets share the same Dushnik–Miller
    dimension (every [d] is a dimension of [R] iff it is a dimension of [S]). *)
Definition PreservesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall d, dim_at R d <-> dim_at S d.

(** [ReducesDim A R B S]: dim R ≤ dim S.  The witnesses are term-level
    instances so [PosetDimension] stays in [Type]. *)
Definition ReducesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall dR dS, PosetDimension R dR -> PosetDimension S dS -> dR <= dS.

(** ** Basic algebra of [PreservesDim] *)

Lemma preserves_dim_refl : forall A (R : A -> A -> Prop), PreservesDim A R A R.
Proof.
  intros A R. unfold PreservesDim. intro d. tauto.
Qed.

Lemma preserves_dim_sym :
  forall A R B S, PreservesDim A R B S -> PreservesDim B S A R.
Proof.
  intros A R B S Hpres. unfold PreservesDim in *. intro d. rewrite Hpres. tauto.
Qed.

Lemma preserves_dim_trans :
  forall A R B S C T,
    PreservesDim A R B S -> PreservesDim B S C T -> PreservesDim A R C T.
Proof.
  intros A R B S C T H1 H2. unfold PreservesDim in *. intro d.
  rewrite H1. rewrite H2. tauto.
Qed.

(** ** Basic algebra of [ReducesDim] *)

Lemma reduces_dim_refl :
  forall A (R : A -> A -> Prop) `{IsPoset A R}, ReducesDim A R A R.
Proof.
  intros A R HPos. unfold ReducesDim.
  intros dR dS HdR HdS.
  pose proof (posdim_unique A R dR dS HdR HdS) as Heq.
  lia.
Qed.

Lemma reduces_dim_trans :
  forall A R B S C T `{IsPoset B S},
    (exists dS, dim_at S dS) ->
    ReducesDim A R B S -> ReducesDim B S C T -> ReducesDim A R C T.
Proof.
  intros A R B S C T HSPos Hex H1 H2.
  destruct Hex as [dS [HdS]].
  unfold ReducesDim in *.
  intros dR dT HdR HdT.
  specialize (H1 dR dS HdR HdS).
  specialize (H2 dS dT HdS HdT).
  lia.
Qed.

(** ** Relationship between [PreservesDim] and [ReducesDim] *)

Lemma preserves_dim_reduces :
  forall A R B S `{IsPoset A R} `{IsPoset B S},
    (exists dS, dim_at S dS) ->
    PreservesDim A R B S -> ReducesDim A R B S.
Proof.
  intros A R B S HRA HSB Hex Hpres.
  destruct Hex as [dS [HdS]].
  unfold ReducesDim. intros dR dS' HdR HdS'.
  assert (HinhR : dim_at R dR) by exact (inhabits HdR).
  assert (HinhS_dR : dim_at S dR) by (apply (Hpres dR); exact HinhR).
  destruct HinhS_dR as [HdR_S].
  pose proof (posdim_unique B S dR dS' HdR_S HdS') as Heq.
  lia.
Qed.

(** ** Dim ≤ 2 corollaries *)

Lemma preserves_dim2 :
  forall A R B S,
    PreservesDim A R B S ->
    ((exists d, dim_at R d /\ d <= 2) <-> (exists d, dim_at S d /\ d <= 2)).
Proof.
  intros A R B S Hpres. split.
  - intros [d [Hd Hle]].
    exists d. split.
    + apply (Hpres d). exact Hd.
    + exact Hle.
  - intros [d [Hd Hle]].
    exists d. split.
    + apply (Hpres d). exact Hd.
    + exact Hle.
Qed.

Lemma reduces_dim2 :
  forall A R B S,
    ReducesDim A R B S ->
    (exists dR, dim_at R dR) ->
    (exists d, dim_at S d /\ d <= 2) ->
    (exists d, dim_at R d /\ d <= 2).
Proof.
  intros A R B S Hred Hex [dS [HdS Hle]].
  destruct Hex as [dR [HdR]].
  destruct HdS as [HdS].
  pose proof (Hred dR dS HdR HdS) as Hle2.
  exists dR. split.
  - exact (inhabits HdR).
  - lia.
Qed.
