(* ExecPoset n-way fully-synchronized dim<=2 lever *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FinPosetDimSurgery FinPosetDim FinFullySync.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* In a fully-synchronized decomposition, everything in an earlier block is
   below everything in a later block — extracted from the prefix-union barrier
   at the cut index [j]. *)
Lemma fully_sync_pairwise_below :
  forall E blocks, IsFullySync E blocks ->
    forall i j, i < j -> j < length blocks ->
      forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                  Ensembles.In _ (nth j blocks (Empty_set _)) y -> ep_order E x y.
Proof.
  intros E blocks Hfs i j Hij Hj x y Hxi Hyj.
  destruct Hfs as [Hne [Hcov [Hdis Hbar]]].
  assert (Hj0 : 0 < j) by lia.
  pose proof (Hbar j Hj0 Hj) as HB.
  destruct HB as [_ [_ [_ [_ Hbelow]]]].
  (* x is in the prefix union (index i < j). *)
  assert (HxL : Ensembles.In _ (union_upto E blocks j) x).
  { exists i. split; [exact Hij | exact Hxi]. }
  (* y is not in the prefix union: any witnessing index i' < j would collide
     with j by disjointness. *)
  assert (HyU : ~ Ensembles.In _ (union_upto E blocks j) y).
  { intros [i' [Hi'j Hyi']].
    apply (Hdis i' j y).
    - lia.
    - exact Hj.
    - lia.
    - exact Hyi'.
    - exact Hyj. }
  exact (Hbelow x y HxL HyU).
Qed.

(* The ExecPoset instantiation of the n-way ordinal-partition dim<=2 theorem:
   a fully-synchronized decomposition whose every block has dimension <= 2
   yields a whole-execution dimension <= 2. *)
Lemma fully_sync_dim_le2 :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
Proof.
  intros E blocks Hfs Hblocks.
  (* The execution carrier is finite. *)
  pose proof (cardinal_finite _ _ (ep_size E) (ep_size_ok E)) as Hfin.
  (* The decomposition is an ordinal partition of (ep_carrier E, ep_order E). *)
  pose proof (fully_sync_pairwise_below E blocks Hfs) as Hbel.
  assert (Hpart : fin_ordinal_partition (ep_order E) blocks).
  { destruct Hfs as [Hne [Hcov [Hdis _]]].
    unfold fin_ordinal_partition.
    repeat split.
    - exact Hne.
    - exact Hcov.
    - exact Hdis.
    - exact Hbel. }
  (* Block hypotheses transfer definitionally: [fin_sub_order (ep_order E) blk]
     is [sub_order E blk]. *)
  assert (Hblocks' : forall blk, List.In blk blocks ->
            exists d, inhabited (PosetDimension (fin_sub_order (ep_order E) blk) d) /\ d <= 2).
  { exact Hblocks. }
  destruct (fin_fully_sync_dim_le2 (ep_order E) Hfin blocks Hpart Hblocks')
    as [d [Hd Hle]].
  exists d. split.
  - exact Hd.
  - exact Hle.
Qed.
