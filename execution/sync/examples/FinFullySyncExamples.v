(* n-way fully-sync examples (test-only)

   The concrete [E_min] 2-block instance of the n-way fully-synchronized
   dim<=2 lever.  [blocks := [Lmin; Umin]] is a fully-synchronized
   decomposition (the single prefix-barrier is exactly [E_min_barrier]),
   and each block has dimension <= 2 (subposet of [E_min], dim 2). *)

From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FinPosetDim FinFullySync FullySyncDim2
                              DimExamples FrontierExamples.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.

(* [union_upto E_min [Lmin;Umin] 1] is exactly [Lmin] as an ensemble. *)
Lemma union_upto1_eq_Lmin :
  union_upto E_min [Lmin; Umin] 1 = Lmin.
Proof.
  apply Extensionality_Ensembles. split.
  - intros x [i [Hi Hin]].
    assert (i = 0) by lia. subst i. simpl in Hin. exact Hin.
  - intros x Hin. exists 0. split; [lia | simpl; exact Hin].
Qed.

(* The complement of [union_upto … 1] is exactly [Umin]. *)
Lemma not_union_upto1_eq_Umin :
  (fun x => ~ Ensembles.In _ (union_upto E_min [Lmin; Umin] 1) x) = Umin.
Proof.
  apply Extensionality_Ensembles. split.
  - intros x Hnin.
    unfold Ensembles.In, Umin. intro Heq.
    apply Hnin. rewrite union_upto1_eq_Lmin.
    unfold Ensembles.In, Lmin. exact Heq.
  - intros x Hin Hcontra.
    rewrite union_upto1_eq_Lmin in Hcontra.
    unfold Ensembles.In, Umin in Hin.
    unfold Ensembles.In, Lmin in Hcontra.
    exact (Hin Hcontra).
Qed.

Example E_min_is_fully_sync_2 : IsFullySync E_min [Lmin; Umin].
Proof.
  unfold IsFullySync. split; [| split; [| split]].
  - (* (1) nonempty blocks *)
    intros blk Hblk. destruct Hblk as [<- | [<- | []]].
    + exists ev_a. unfold Ensembles.In, Lmin. reflexivity.
    + exists ev_b. unfold Ensembles.In, Umin. discriminate.
  - (* (2) cover *)
    intro x. pose proof (valid_event_min_cases x) as Hx. cbv zeta in Hx.
    destruct Hx as [Hx | [Hx | [Hx | Hx]]].
    + exists 0. split; [simpl; lia |].
      change (Ensembles.In _ Lmin x). unfold Ensembles.In, Lmin. exact Hx.
    + exists 1. split; [simpl; lia |].
      change (Ensembles.In _ Umin x). unfold Ensembles.In, Umin.
      rewrite Hx. discriminate.
    + exists 1. split; [simpl; lia |].
      change (Ensembles.In _ Umin x). unfold Ensembles.In, Umin.
      rewrite Hx. discriminate.
    + exists 1. split; [simpl; lia |].
      change (Ensembles.In _ Umin x). unfold Ensembles.In, Umin.
      rewrite Hx. discriminate.
  - (* (3) pairwise disjoint *)
    intros i j x Hi Hj Hij Hin.
    simpl in Hi, Hj.
    destruct i as [|[|i]]; destruct j as [|[|j]]; try lia.
    + (* i=0, j=1 : Lmin x and Umin x *)
      change (Ensembles.In _ Lmin x) in Hin. change (~ Ensembles.In _ Umin x).
      unfold Ensembles.In, Lmin in Hin. unfold Ensembles.In, Umin.
      intro HU. exact (HU Hin).
    + (* i=1, j=0 : Umin x and Lmin x *)
      change (Ensembles.In _ Umin x) in Hin. change (~ Ensembles.In _ Lmin x).
      unfold Ensembles.In, Umin in Hin. unfold Ensembles.In, Lmin.
      intro HL. exact (Hin HL).
  - (* (4) prefix-union barrier *)
    intros kk Hk0 Hk2. simpl in Hk2.
    assert (kk = 1) by lia. subst kk.
    rewrite not_union_upto1_eq_Umin, union_upto1_eq_Lmin.
    exact E_min_barrier.
Qed.

Example E_min_dim_le_2_via_fully_sync :
  exists d, exec_has_dimension E_min d /\ d <= 2.
Proof.
  apply (fully_sync_dim_le2 E_min [Lmin; Umin] E_min_is_fully_sync_2).
  assert (Hblk : forall S : Ensemble (ep_carrier E_min),
            exists d, inhabited (PosetDimension (sub_order E_min S) d) /\ d <= 2).
  { intro S. destruct E_min_dim_2 as [Hd2].
    destruct (subposet_dimension_le (ep_order E_min) S 2 Hd2)
      as [dq [Hinh Hle]].
    exists dq; split; [exact Hinh | exact Hle]. }
  intros blk Hblk_in. apply Hblk.
Qed.
