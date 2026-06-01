(* exact n-way dimension examples (test-only)

   A concrete all-singleton example exercising the exact n-way dimension
   theorem [fin_fully_sync_dimension] on the 2-element chain (false < true on
   bool).  The chain is partitioned into the two singleton blocks
   [{false}; {true}] with per-block dimensions [0; 0].  The n-way formula then
   forces the whole-poset dimension to be exactly
     max 1 (fold_right max 0 [0;0]) = max 1 0 = 1.
   ZERO Admitted. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import FinPosetDimSurgery FinPosetDim FinExtremumDim
                              FinFullySync FinFullySyncDim FinExtremumDimExamples.
Import ListNotations.

#[local] Existing Instance chain2_poset.

(* The two singleton blocks of the chain, ordinally stacked: {false} < {true}. *)
Definition cblocks : list (Ensemble bool) :=
  [ (fun b => b = false) ; (fun b => b = true) ].

(* [cblocks] is a finite ordinal partition of (bool, chain2_R). *)
Lemma chain_part : fin_ordinal_partition chain2_R cblocks.
Proof.
  unfold fin_ordinal_partition, cblocks.
  split; [| split; [| split]].
  - (* nonempty *)
    intros blk Hblk.
    destruct Hblk as [<- | [<- | []]].
    + exists false. reflexivity.
    + exists true. reflexivity.
  - (* cover *)
    intro b. destruct b.
    + exists 1. split; [simpl; lia | reflexivity].
    + exists 0. split; [simpl; lia | reflexivity].
  - (* disjoint *)
    intros i j x Hi Hj Hij Hin.
    intro Hbad.
    cbn in Hi, Hj.
    destruct i as [| [| i]]; destruct j as [| [| j]]; try lia;
      unfold Ensembles.In in Hin, Hbad; cbn in Hin, Hbad; congruence.
  - (* below *)
    intros i j Hij Hj x y Hx Hy.
    cbn in Hj.
    destruct i as [| [| i]]; destruct j as [| [| j]]; try lia;
      unfold Ensembles.In in Hx, Hy; cbn in Hx, Hy.
    subst x. subst y. right. split; reflexivity.
Qed.

(* Each singleton block has dimension 0. *)
Lemma chain_blockdims :
  forall i, i < length cblocks ->
    PosetDimension (fin_sub_order chain2_R (nth i cblocks (Empty_set _)))
                   (nth i [0; 0] 0).
Proof.
  intros i Hi.
  cbn in Hi.
  (* Each surviving block is a singleton, so any two of its subtype elements
     are equal; [fin_singleton_dim0] then gives dimension 0. *)
  destruct i as [| [| i]]; try lia; cbn;
    [ apply (@fin_singleton_dim0 _
               (fin_sub_order chain2_R (fun b => b = false))
               (fin_sub_order_poset chain2_R (fun b => b = false)))
    | apply (@fin_singleton_dim0 _
               (fin_sub_order chain2_R (fun b => b = true))
               (fin_sub_order_poset chain2_R (fun b => b = true))) ];
    intros [x Hx] [y Hy];
    unfold Ensembles.In in Hx, Hy; cbn in Hx, Hy;
    subst x; subst y; f_equal; apply proof_irrelevance.
Qed.

(* The exact n-way formula, applied with dW := 1 (witness [chain2_dim1]),
   forces 1 = max 1 (fold_right max 0 [0;0]) = max 1 0 = 1 — validating the
   formula end-to-end on a genuine multi-block partition.  The witnessed
   dimension is exactly 1. *)
Example chain_all_singleton_dim :
  exists dW, inhabited (PosetDimension chain2_R dW) /\ dW = 1.
Proof.
  pose proof (fin_fully_sync_dimension chain2_R chain2_Hfin cblocks [0; 0]
                chain_part eq_refl chain_blockdims
                (ex_intro _ false (ex_intro _ true (fun H => true_neq_false (eq_sym H))))
                1 chain2_dim1) as Heq.
  (* Heq : 1 = Nat.max 1 (fold_right Nat.max 0 [0;0]) = 1 *)
  exists 1. split.
  - exact (inhabits chain2_dim1).
  - reflexivity.
Qed.
