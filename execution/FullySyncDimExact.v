(* ExecPoset exact n-way fully-synchronized dimension *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal
                              FullySync FullySyncDim2 FinPosetDimSurgery FinPosetDim
                              FinFullySync FinFullySyncDim.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* The ExecPoset instantiation of the exact n-way ordinal-partition dimension
   theorem: in a fully-synchronized decomposition with at least two distinct
   events, the whole-execution dimension equals the max (clamped at 1) of the
   per-block dimensions. *)
Lemma fully_sync_dimension :
  forall E blocks dims, IsFullySync E blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    forall dW, PosetDimension (ep_order E) dW ->
      dW = Nat.max 1 (fold_right Nat.max 0 dims).
Proof.
  intros E blocks dims Hfs Hlendims Hdims Hge2 dW HdW.
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
  assert (Hdims' : forall i, i < length blocks ->
            PosetDimension (fin_sub_order (ep_order E) (nth i blocks (Empty_set _)))
                           (nth i dims 0)).
  { exact Hdims. }
  apply (fin_fully_sync_dimension (ep_order E) Hfin blocks dims Hpart Hlendims Hdims'
           Hge2 dW HdW).
Qed.
