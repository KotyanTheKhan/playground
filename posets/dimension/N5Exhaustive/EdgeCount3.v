(** edge_count_5 = 3 case for n=5 dispatcher.

    When [edge_count_5 R2 a b c d e = 3] over 5 pairwise distinct
    elements covering the carrier, there are exactly three strict
    edges.  We extract them, classify by structure, and dispatch
    to the appropriate per-class realizer. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import
  EdgeCount EdgeCount3_extract
  EdgeCount3_chain3 EdgeCount3_claw_up EdgeCount3_claw_down
  EdgeCount3_N EdgeCount3_V_chain EdgeCount3_inv_V_chain.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount3.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  (** Main lemma: edge_count = 3 yields a 2-realizer. *)
  Lemma n5_edge_count_3_two_realizer :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 3 ->
      exists r : Ensemble (B -> B -> Prop),
        IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec.
    destruct (edge_count_3_three_edges R2 a b c d e
                Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec)
      as [x1 [y1 [x2 [y2 [x3 [y3
         [HR1 [Hxy1 [HR2' [Hxy2 [HR3 [Hxy3
         [Hd12 [Hd13 Hd23]]]]]]]]]]]]]].
    (* ===== STAGE 1: 6 transitivity checks → chain3. ===== *)
    destruct (classic (y1 = x2)) as [Hy1x2 | Hny1x2].
    { assert (HRy1y2 : R2 y1 y2) by (rewrite Hy1x2; exact HR2').
      assert (HRx1y2 : R2 x1 y2) by (apply (poset_trans x1 y1 y2); assumption).
      assert (Hx1y2_neq : x1 <> y2).
      { intro Heq. subst y2. apply Hxy1. apply (poset_antisym _ _ HR1 HRy1y2). }
      assert (Hy1_y2 : y1 <> y2) by (rewrite Hy1x2; exact Hxy2).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 y1 y2 Hxy1 Hx1y2_neq Hy1_y2 HR1 HRy1y2 HRx1y2). }
    destruct (classic (y1 = x3)) as [Hy1x3 | Hny1x3].
    { assert (HRy1y3 : R2 y1 y3) by (rewrite Hy1x3; exact HR3).
      assert (HRx1y3 : R2 x1 y3) by (apply (poset_trans x1 y1 y3); assumption).
      assert (Hx1y3_neq : x1 <> y3).
      { intro Heq. subst y3. apply Hxy1. apply (poset_antisym _ _ HR1 HRy1y3). }
      assert (Hy1_y3 : y1 <> y3) by (rewrite Hy1x3; exact Hxy3).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 y1 y3 Hxy1 Hx1y3_neq Hy1_y3 HR1 HRy1y3 HRx1y3). }
    destruct (classic (y2 = x1)) as [Hy2x1 | Hny2x1].
    { assert (HRy2y1 : R2 y2 y1) by (rewrite Hy2x1; exact HR1).
      assert (HRx2y1 : R2 x2 y1) by (apply (poset_trans x2 y2 y1); assumption).
      assert (Hx2y1_neq : x2 <> y1).
      { intro Heq. subst y1. apply Hxy2. apply (poset_antisym _ _ HR2' HRy2y1). }
      assert (Hy2_y1 : y2 <> y1) by (rewrite Hy2x1; exact Hxy1).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x2 y2 y1 Hxy2 Hx2y1_neq Hy2_y1 HR2' HRy2y1 HRx2y1). }
    destruct (classic (y2 = x3)) as [Hy2x3 | Hny2x3].
    { assert (HRy2y3 : R2 y2 y3) by (rewrite Hy2x3; exact HR3).
      assert (HRx2y3 : R2 x2 y3) by (apply (poset_trans x2 y2 y3); assumption).
      assert (Hx2y3_neq : x2 <> y3).
      { intro Heq. subst y3. apply Hxy2. apply (poset_antisym _ _ HR2' HRy2y3). }
      assert (Hy2_y3 : y2 <> y3) by (rewrite Hy2x3; exact Hxy3).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x2 y2 y3 Hxy2 Hx2y3_neq Hy2_y3 HR2' HRy2y3 HRx2y3). }
    destruct (classic (y3 = x1)) as [Hy3x1 | Hny3x1].
    { assert (HRy3y1 : R2 y3 y1) by (rewrite Hy3x1; exact HR1).
      assert (HRx3y1 : R2 x3 y1) by (apply (poset_trans x3 y3 y1); assumption).
      assert (Hx3y1_neq : x3 <> y1).
      { intro Heq. subst y1. apply Hxy3. apply (poset_antisym _ _ HR3 HRy3y1). }
      assert (Hy3_y1 : y3 <> y1) by (rewrite Hy3x1; exact Hxy1).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x3 y3 y1 Hxy3 Hx3y1_neq Hy3_y1 HR3 HRy3y1 HRx3y1). }
    destruct (classic (y3 = x2)) as [Hy3x2 | Hny3x2].
    { assert (HRy3y2 : R2 y3 y2) by (rewrite Hy3x2; exact HR2').
      assert (HRx3y2 : R2 x3 y2) by (apply (poset_trans x3 y3 y2); assumption).
      assert (Hx3y2_neq : x3 <> y2).
      { intro Heq. subst y2. apply Hxy3. apply (poset_antisym _ _ HR3 HRy3y2). }
      assert (Hy3_y2 : y3 <> y2) by (rewrite Hy3x2; exact Hxy2).
      apply (n5_edge_count_3_chain3 R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x3 y3 y2 Hxy3 Hx3y2_neq Hy3_y2 HR3 HRy3y2 HRx3y2). }
    (* ===== STAGE 2: bipartite case (no chain).
       All yi <> xj for i, j ∈ {1,2,3}. *)
    (* Classify by source equalities. *)
    destruct (classic (x1 = x2)) as [Hx12 | Hnx12].
    { (* x1 = x2 *)
      subst x2.
      assert (Hy12_neq : y1 <> y2)
        by (destruct Hd12 as [Hd | Hd]; [contradiction (Hd eq_refl) | exact Hd]).
      destruct (classic (x1 = x3)) as [Hx13 | Hnx13].
      { (* x1 = x2 = x3 → 3-claw-up at x1 *)
        subst x3.
        assert (Hy13_neq : y1 <> y3)
          by (destruct Hd13 as [Hd | Hd]; [contradiction (Hd eq_refl) | exact Hd]).
        assert (Hy23_neq : y2 <> y3)
          by (destruct Hd23 as [Hd | Hd]; [contradiction (Hd eq_refl) | exact Hd]).
        apply (n5_edge_count_3_claw_up R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x1 y1 y2 y3 Hxy1 Hxy2 Hxy3 Hy12_neq Hy13_neq Hy23_neq
                 HR1 HR2' HR3). }
      (* x1 = x2 <> x3.  x3's source is distinct from x1.  Edge (x3, y3) is
         disjoint from V edges (x1, y1), (x1, y2) on source. *)
      (* Now: check target sharing. *)
      (* If y3 = y1 OR y3 = y2: N-shape. *)
      destruct (classic (y3 = y1)) as [Hy3y1 | Hny3y1].
      { (* Edges (x1, y1), (x1, y2), (x3, y1).  This is N-shape with
           p=x1, q=y2, r=x1, ... wait, let me check the N pattern.
           N: R2 p q, R2 r q, R2 r s.  In our edges: (x1, y1), (x1, y2), (x3, y1).
           Reformat: target y1 shared by (x1, y1) and (x3, y1).  Source x1 shared
           by (x1, y1) and (x1, y2).
           N-pattern: R2 p q, R2 r q, R2 r s.
           Map: p := x3, q := y1, r := x1, s := y2.
           Then R2 p q = R2 x3 y1.  We have R2 x3 y3 = R2 x3 y1 (since y3 = y1). ✓
                R2 r q = R2 x1 y1.  We have HR1. ✓
                R2 r s = R2 x1 y2.  We have HR2' with x2 = x1. ✓ *)
        (* Edges (x1, y1), (x1, y2), (x3, y1).  N-pattern: R2 p q, R2 r q, R2 r s.
           Map: p:=x3, q:=y1, r:=x1, s:=y2. *)
        subst y3.
        assert (Hx3_y1 : x3 <> y1)
          by (intro He; subst y1; apply Hxy3; reflexivity).
        assert (Hx1_y2 : x1 <> y2) by exact Hxy2.
        assert (Hy1_y2 : y1 <> y2) by exact Hy12_neq.
        assert (Hx3_x1 : x3 <> x1) by (intro He; apply Hnx13; symmetry; exact He).
        assert (Hx3_y2 : x3 <> y2) by (intro He; apply Hny2x3; symmetry; exact He).
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x3 y1 x1 y2 Hx3_y1 Hx3_x1 Hx3_y2
                 (fun He => Hxy1 (eq_sym He))
                 Hy1_y2 Hx1_y2 HR3 HR1 HR2'). }
      destruct (classic (y3 = y2)) as [Hy3y2 | Hny3y2].
      { (* Edges (x1, y1), (x1, y2), (x3, y2).  N-pattern map:
           p:=x3, q:=y2, r:=x1, s:=y1. *)
        subst y3.
        assert (Hx3_y2 : x3 <> y2) by exact Hxy3.
        assert (Hx3_x1 : x3 <> x1) by (intro He; apply Hnx13; symmetry; exact He).
        assert (Hx3_y1 : x3 <> y1) by (intro He; apply Hny1x3; symmetry; exact He).
        assert (Hy2_x1 : y2 <> x1) by (intro He; subst x1; apply Hxy2; reflexivity).
        assert (Hy2_y1 : y2 <> y1) by (intro He; apply Hy12_neq; symmetry; exact He).
        assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x3 y2 x1 y1 Hx3_y2 Hx3_x1 Hx3_y1 Hy2_x1 Hy2_y1 Hx1_y1
                 HR3 HR2' HR1). }
      (* No target sharing y3 with y1 or y2.  So y3 disjoint from {y1, y2}.
         Edges (x1, y1), (x1, y2), (x3, y3) with all 5 elements distinct:
         {x1, y1, y2, x3, y3} all distinct.  V + chain configuration. *)
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      assert (Hx1_y2 : x1 <> y2) by exact Hxy2.
      assert (Hx1_x3 : x1 <> x3) by exact Hnx13.
      assert (Hx1_y3 : x1 <> y3) by (intro He; subst y3; contradiction (Hny3x1 eq_refl)).
      assert (Hy1_y2 : y1 <> y2) by exact Hy12_neq.
      assert (Hy1_x3 : y1 <> x3) by (intro He; subst x3; contradiction (Hny1x3 eq_refl)).
      assert (Hy1_y3 : y1 <> y3) by (intro He; apply Hny3y1; symmetry; exact He).
      assert (Hy2_x3 : y2 <> x3) by (intro He; subst x3; contradiction (Hny2x3 eq_refl)).
      assert (Hy2_y3 : y2 <> y3) by (intro He; apply Hny3y2; symmetry; exact He).
      assert (Hx3_y3 : x3 <> y3) by exact Hxy3.
      apply (n5_edge_count_3_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 y1 y2 x3 y3 Hx1_y1 Hx1_y2 Hx1_x3 Hx1_y3
               Hy1_y2 Hy1_x3 Hy1_y3 Hy2_x3 Hy2_y3 Hx3_y3
               HR1 HR2' HR3). }
    (* x1 <> x2 *)
    destruct (classic (x1 = x3)) as [Hx13 | Hnx13].
    { (* x1 = x3, but x1 <> x2.  So edges (x1, y1), (x2, y2), (x1, y3) share source x1
         between (x1, y1) and (x1, y3).  Edge (x2, y2) different source. *)
      subst x3.
      assert (Hy13_neq : y1 <> y3)
        by (destruct Hd13 as [Hd | Hd]; [contradiction (Hd eq_refl) | exact Hd]).
      (* Check target sharing with (x2, y2). *)
      destruct (classic (y2 = y1)) as [Hy2y1 | Hny2y1].
      { (* (x2, y1), (x1, y1), (x1, y3): N-shape *)
        subst y2.
        assert (Hx2_y1 : x2 <> y1) by exact Hxy2.
        assert (Hx2_x1 : x2 <> x1) by (intro He; apply Hnx12; symmetry; exact He).
        assert (Hx2_y3 : x2 <> y3) by (intro He; subst y3; contradiction (Hny3x2 eq_refl)).
        assert (Hx1_y3 : x1 <> y3) by exact Hxy3.
        assert (Hy1_y3 : y1 <> y3) by exact Hy13_neq.
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x2 y1 x1 y3 Hx2_y1 Hx2_x1 Hx2_y3
                 (fun He => Hxy1 (eq_sym He)) Hy1_y3 Hx1_y3
                 HR2' HR1 HR3). }
      destruct (classic (y2 = y3)) as [Hy2y3 | Hny2y3].
      { (* (x2, y3), (x1, y1), (x1, y3): N-shape with target y3 shared *)
        subst y2.
        assert (Hx2_y3 : x2 <> y3) by exact Hxy2.
        assert (Hx2_x1 : x2 <> x1) by (intro He; apply Hnx12; symmetry; exact He).
        assert (Hx2_y1 : x2 <> y1) by (intro He; subst y1; contradiction (Hny1x2 eq_refl)).
        assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
        assert (Hy3_y1 : y3 <> y1) by (intro He; apply Hy13_neq; symmetry; exact He).
        assert (Hy3_x1 : y3 <> x1) by exact Hny3x1.
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x2 y3 x1 y1 Hx2_y3 Hx2_x1 Hx2_y1 Hy3_x1 Hy3_y1 Hx1_y1
                 HR2' HR3 HR1). }
      (* No target sharing: (x2, y2) disjoint.  V + chain with V at x1. *)
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      assert (Hx1_y3 : x1 <> y3) by exact Hxy3.
      assert (Hx1_x2 : x1 <> x2) by exact Hnx12.
      assert (Hx1_y2 : x1 <> y2) by (intro He; subst y2; contradiction (Hny2x1 eq_refl)).
      assert (Hy1_y3 : y1 <> y3) by exact Hy13_neq.
      assert (Hy1_x2 : y1 <> x2) by (intro He; subst x2; contradiction (Hny1x2 eq_refl)).
      assert (Hy1_y2 : y1 <> y2) by (intro He; apply Hny2y1; symmetry; exact He).
      assert (Hy3_x2 : y3 <> x2) by (intro He; subst x2; contradiction (Hny3x2 eq_refl)).
      assert (Hy3_y2 : y3 <> y2) by (intro He; apply Hny2y3; symmetry; exact He).
      assert (Hx2_y2 : x2 <> y2) by exact Hxy2.
      apply (n5_edge_count_3_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 y1 y3 x2 y2 Hx1_y1 Hx1_y3 Hx1_x2 Hx1_y2
               Hy1_y3 Hy1_x2 Hy1_y2 Hy3_x2 Hy3_y2 Hx2_y2
               HR1 HR3 HR2'). }
    (* x1 <> x2 AND x1 <> x3 *)
    destruct (classic (x2 = x3)) as [Hx23 | Hnx23].
    { (* x2 = x3, with x1 distinct *)
      subst x3.
      assert (Hy23_neq : y2 <> y3)
        by (destruct Hd23 as [Hd | Hd]; [contradiction (Hd eq_refl) | exact Hd]).
      destruct (classic (y1 = y2)) as [Hy1y2 | Hny1y2].
      { (* Edges: (x1, y1), (x2, y1), (x2, y3) — N-shape with target y1 shared. *)
        subst y2.
        assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
        assert (Hx1_x2 : x1 <> x2) by exact Hnx12.
        assert (Hx1_y3 : x1 <> y3) by (intro He; subst y3; contradiction (Hny3x1 eq_refl)).
        assert (Hx2_y1 : x2 <> y1) by exact Hxy2.
        assert (Hy1_y3 : y1 <> y3) by exact Hy23_neq.
        (* N-pattern: R2 p q, R2 r q, R2 r s.  Here: (x1,y1),(x2,y1),(x2,y3).
           Map: p:=x1, q:=y1, r:=x2, s:=y3. *)
        assert (Hy1_x2 : y1 <> x2) by (intro He; apply Hx2_y1; symmetry; exact He).
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x1 y1 x2 y3 Hx1_y1 Hx1_x2 Hx1_y3 Hy1_x2 Hy1_y3 Hxy3
                 HR1 HR2' HR3). }
      destruct (classic (y1 = y3)) as [Hy1y3 | Hny1y3].
      { (* Edges: (x1, y1), (x2, y2), (x2, y1) — N-shape with target y1 shared. *)
        subst y3.
        assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
        assert (Hx1_x2 : x1 <> x2) by exact Hnx12.
        assert (Hx1_y2 : x1 <> y2) by (intro He; subst y2; contradiction (Hny2x1 eq_refl)).
        assert (Hx2_y1 : x2 <> y1) by exact Hxy3.
        assert (Hy1_y2 : y1 <> y2) by exact Hny1y2.
        assert (Hy1_x2 : y1 <> x2) by (intro He; apply Hx2_y1; symmetry; exact He).
        (* (x1,y1), (x2,y1), (x2,y2): same N-pattern with s := y2. *)
        apply (n5_edge_count_3_N R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 x1 y1 x2 y2 Hx1_y1 Hx1_x2 Hx1_y2 Hy1_x2 Hy1_y2 Hxy2
                 HR1 HR3 HR2'). }
      (* y1 <> y2 and y1 <> y3.  V + chain: V at x2 (edges (x2,y2),(x2,y3)),
         chain (x1, y1). *)
      assert (Hx2_y2 : x2 <> y2) by exact Hxy2.
      assert (Hx2_y3 : x2 <> y3) by exact Hxy3.
      assert (Hx2_x1 : x2 <> x1) by (intro He; apply Hnx12; symmetry; exact He).
      assert (Hx2_y1 : x2 <> y1) by (intro He; subst x2; contradiction (Hny1x2 eq_refl)).
      assert (Hy2_y3 : y2 <> y3) by exact Hy23_neq.
      assert (Hy2_x1 : y2 <> x1) by (intro He; subst x1; contradiction (Hny2x1 eq_refl)).
      assert (Hy2_y1 : y2 <> y1) by (intro He; apply Hny1y2; symmetry; exact He).
      assert (Hy3_x1 : y3 <> x1) by (intro He; subst x1; contradiction (Hny3x1 eq_refl)).
      assert (Hy3_y1 : y3 <> y1) by (intro He; apply Hny1y3; symmetry; exact He).
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      apply (n5_edge_count_3_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x2 y2 y3 x1 y1 Hx2_y2 Hx2_y3 Hx2_x1 Hx2_y1
               Hy2_y3 Hy2_x1 Hy2_y1 Hy3_x1 Hy3_y1 Hx1_y1
               HR2' HR3 HR1). }
    (* All sources distinct: x1, x2, x3 pairwise distinct.
       Now look at targets.  |T| ≤ 3.  Total vertices = |S| + |T|.
       With |S|=3 and |T|≤3, |S|+|T|≤6.  But bipartite, S∩T=∅, so all
       distinct.  Total ≤ 6 vertices.  With 5 elements, |T|=2 forced
       (pigeonhole). *)
    destruct (classic (y1 = y2)) as [Hy12 | Hny12].
    { (* y1 = y2 *)
      subst y2.
      (* All sources distinct, y1 = y2.  Check y3. *)
      destruct (classic (y1 = y3)) as [Hy13 | Hny13].
      { (* y1 = y2 = y3 → 3-claw-down *)
        subst y3.
        assert (Hx12_neq : x1 <> x2) by exact Hnx12.
        assert (Hx13_neq : x1 <> x3) by exact Hnx13.
        assert (Hx23_neq : x2 <> x3) by exact Hnx23.
        apply (n5_edge_count_3_claw_down R2 Hcard a b c d e
                 Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
                 y1 x1 x2 x3
                 (fun He => Hxy1 (eq_sym He))
                 (fun He => Hxy2 (eq_sym He))
                 (fun He => Hxy3 (eq_sym He))
                 Hx12_neq Hx13_neq Hx23_neq
                 HR1 HR2' HR3). }
      (* y1 = y2, y3 different.  N-shape: edges (x1,y1),(x2,y1),(x3,y3).
         N pattern: R2 p q, R2 r q, R2 r s.
         Here (x1,y1),(x2,y1) share target.  (x3,y3) disjoint or shares src
         with x3? No, x3 distinct.  So (x3, y3) is disjoint from {x1,x2,y1}
         only if x3 ∉ {x1,x2,y1} and y3 ∉ {x1,x2,y1}.
         Hmm — this is V + chain if all 5 distinct.  But N has 4 distinct.
         Let me check vertices: {x1, x2, y1, x3, y3}.  Need 5 distinct for ∧+chain.
         If x3 = y1, no — that's transitivity (Hny3x1, etc. exclude this).
         Wait, x3 = y1 would mean Hny1x3 hold: y1 ≠ x3 ✓.
         If y3 = x1 or y3 = x2: transitivity rules excluded these.
         If y3 = y1: case above.  Excluded here.
         So all 5 distinct. ∧ + chain configuration with ∧ at y1, chain (x3, y3). *)
      assert (Hx1_x2 : x1 <> x2) by exact Hnx12.
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      assert (Hx1_x3 : x1 <> x3) by exact Hnx13.
      assert (Hx1_y3 : x1 <> y3) by (intro He; subst y3; contradiction (Hny3x1 eq_refl)).
      assert (Hx2_y1 : x2 <> y1) by exact Hxy2.
      assert (Hx2_x3 : x2 <> x3) by exact Hnx23.
      assert (Hx2_y3 : x2 <> y3) by (intro He; subst y3; contradiction (Hny3x2 eq_refl)).
      assert (Hy1_x3 : y1 <> x3) by (intro He; subst x3; contradiction (Hny1x3 eq_refl)).
      assert (Hy1_y3 : y1 <> y3) by exact Hny13.
      assert (Hx3_y3 : x3 <> y3) by exact Hxy3.
      apply (n5_edge_count_3_inv_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 x2 y1 x3 y3 Hx1_x2 Hx1_y1 Hx1_x3 Hx1_y3
               Hx2_y1 Hx2_x3 Hx2_y3 Hy1_x3 Hy1_y3 Hx3_y3
               HR1 HR2' HR3). }
    (* Sources pairwise distinct, y1 <> y2. *)
    destruct (classic (y1 = y3)) as [Hy13 | Hny13].
    { (* y1 = y3, distinct sources *)
      subst y3.
      (* Edges (x1,y1),(x2,y2),(x3,y1).  y2 <> y1 (Hny12).  ∧+chain? Or N?
         {x1,x2,y1,x3,y2}: x1<>x2 (Hnx12), x1<>x3 (Hnx13), x2<>x3 (Hnx23).
         y1<>x1,x2,x3 (from Hxy1, Hny1x2, Hny1x3).
         y2<>x1,x2,x3 (from Hny2x1, Hxy2, Hny2x3).
         y1<>y2 (Hny12).
         So 5 distinct! ∧+chain with ∧ at y1 (sources x1, x3), chain (x2, y2). *)
      assert (Hx1_x3 : x1 <> x3) by exact Hnx13.
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      assert (Hx1_x2 : x1 <> x2) by exact Hnx12.
      assert (Hx1_y2 : x1 <> y2) by (intro He; subst y2; contradiction (Hny2x1 eq_refl)).
      assert (Hx3_y1 : x3 <> y1) by exact Hxy3.
      assert (Hx3_x2 : x3 <> x2) by (intro He; apply Hnx23; symmetry; exact He).
      assert (Hx3_y2 : x3 <> y2) by (intro He; subst y2; contradiction (Hny2x3 eq_refl)).
      assert (Hy1_x2 : y1 <> x2) by (intro He; subst x2; contradiction (Hny1x2 eq_refl)).
      assert (Hy1_y2 : y1 <> y2) by exact Hny12.
      assert (Hx2_y2 : x2 <> y2) by exact Hxy2.
      apply (n5_edge_count_3_inv_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x1 x3 y1 x2 y2 Hx1_x3 Hx1_y1 Hx1_x2 Hx1_y2
               Hx3_y1 Hx3_x2 Hx3_y2 Hy1_x2 Hy1_y2 Hx2_y2
               HR1 HR3 HR2'). }
    destruct (classic (y2 = y3)) as [Hy23 | Hny23].
    { (* y2 = y3, distinct sources, y1 <> y2, y1 <> y3 *)
      subst y3.
      assert (Hx2_x3 : x2 <> x3) by exact Hnx23.
      assert (Hx2_y2 : x2 <> y2) by exact Hxy2.
      assert (Hx2_x1 : x2 <> x1) by (intro He; apply Hnx12; symmetry; exact He).
      assert (Hx2_y1 : x2 <> y1) by (intro He; subst y1; contradiction (Hny1x2 eq_refl)).
      assert (Hx3_y2 : x3 <> y2) by exact Hxy3.
      assert (Hx3_x1 : x3 <> x1) by (intro He; apply Hnx13; symmetry; exact He).
      assert (Hx3_y1 : x3 <> y1) by (intro He; subst y1; contradiction (Hny1x3 eq_refl)).
      assert (Hy2_x1 : y2 <> x1) by (intro He; subst x1; contradiction (Hny2x1 eq_refl)).
      assert (Hy2_y1 : y2 <> y1) by (intro He; apply Hny12; symmetry; exact He).
      assert (Hx1_y1 : x1 <> y1) by exact Hxy1.
      apply (n5_edge_count_3_inv_V_chain R2 Hcard a b c d e
               Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
               x2 x3 y2 x1 y1 Hx2_x3 Hx2_y2 Hx2_x1 Hx2_y1
               Hx3_y2 Hx3_x1 Hx3_y1 Hy2_x1 Hy2_y1 Hx1_y1
               HR2' HR3 HR1). }
    (* All sources distinct and all targets distinct.  But 6 vertices needed
       in a 5-element bipartite carrier, impossible. *)
    exfalso.
    (* By pigeonhole: {x1,x2,x3,y1,y2,y3} are 6 distinct elements in {a..e}, but
       only 5 elements exist. *)
    (* Wait — we haven't proven yet that the 6 are all in {a..e} AND pairwise distinct.
       From above: x's pairwise distinct (Hnx12, Hnx13, Hnx23).  y's pairwise distinct
       (Hny12, Hny13, Hny23).  No y = x (no chain ⇒ all yi ≠ xj for i,j).
       Specifically: y1≠x1 (Hxy1), y1≠x2 (Hny1x2), y1≠x3 (Hny1x3); similarly all 9
       yi≠xj.  And Hxyi gives yi≠xi.  So all 6 are pairwise distinct.
       But {a..e} has 5 elements, so by Hcov each of the 6 equals one of {a..e}.
       Pigeonhole: 6 → 5 means two equal, contradicting pairwise distinct. *)
    (* Use Hcov to map each to {a..e} and derive contradiction via cases. *)
    destruct (Hcov x1) as [Hx1|[Hx1|[Hx1|[Hx1|Hx1]]]];
    destruct (Hcov x2) as [Hx2|[Hx2|[Hx2|[Hx2|Hx2]]]];
    destruct (Hcov x3) as [Hx3|[Hx3|[Hx3|[Hx3|Hx3]]]];
    destruct (Hcov y1) as [Hyl1|[Hyl1|[Hyl1|[Hyl1|Hyl1]]]];
    destruct (Hcov y2) as [Hyl2|[Hyl2|[Hyl2|[Hyl2|Hyl2]]]];
    destruct (Hcov y3) as [Hyl3|[Hyl3|[Hyl3|[Hyl3|Hyl3]]]];
    subst; congruence.
  Qed.

End EdgeCount3.
