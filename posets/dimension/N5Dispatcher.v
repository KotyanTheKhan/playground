(** n = 5 dispatcher cascade.

    Extracted from N5Realizers.v to keep per-file compilation costs
    manageable.  Contains:

    - [n5_residual_classes_two_realizer] — focused [Admitted] for the
      residual catch-all (single TODO).
    - [n5_dispatcher_microcase_i] — single-fact lemma routing the (q, p)
      branch to antisymmetry-against-[HRpq] contradiction.
    - [n5_dispatcher_microcase_ii] .. [n5_dispatcher_microcase_xiv] —
      Qed-closed handlers for the second-edge cascade branches.
      Extracted from the dispatcher to split its giant Qed into
      independently-compilable proof terms.  Partial progress on the
      broader refactor: micro-cases (xv)–(xix) of the same second-
      edge cascade remain inline inside
      [n5_nonantichain_nonchain_two_realizer] and contribute the bulk
      of its compile time.
    - [n5_nonantichain_nonchain_two_realizer] — the dispatcher that
      pattern-matches each Qed-closed isomorphism class lemma in
      N5Realizers.v, falling through to [n5_residual_classes_two_realizer]
      when no per-class shape matches.

    All per-class lemmas plus the tactics and helpers
    ([n5_neq_assumption], [n5_split_witness], [n5_close_forall_via],
    [carrier_5_destructure], [n5_chain_contra_inc],
    [n5_two_realizer_framework]) live in N5Realizers.v and are made
    available via the [Require Import] below. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

(** Focused (refined) admit for the n=5 non-antichain non-chain case
    EXCLUDING the single-strict-edge class.

    Captures all isomorphism classes on 5 elements that are neither
    antichain, chain, nor the one-edge class (the latter is closed by
    [n5_one_edge_two_realizer]).  The hypothesis [Hmulti] asserts that
    in addition to a chosen strict edge [(p, q)], at least one other
    off-diagonal pair is in [R2]. *)
Lemma n5_residual_classes_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 5 ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  (exists p q x y : B,
     p <> q /\ R2 p q /\
     x <> y /\ R2 x y /\ ~ (x = p /\ y = q)) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Admitted.

(** Dispatcher for the n=5 non-antichain non-chain case.

    Extracts a strict edge [(p, q)] from the non-antichain hypothesis,
    then performs a cascade of classical pattern checks for each Qed-
    closed isomorphism class.  Each branch checks whether the global
    [R2] relation matches the shape predicate in the corresponding
    per-class lemma; if so, routes Qed-style; otherwise falls through.

    Qed-routed branches (Qed per-class lemmas):
      - [n5_chain3_plus_2isolated_two_realizer]      (3-chain + 2 isolated)
      - [n5_disjoint_chains_plus_isolated_two_realizer]
                                                     (2 disjoint edges + 1 iso)
      - [n5_V_plus_2isolated_two_realizer]           (V-shape + 2 iso)
      - [n5_inv_V_plus_2isolated_two_realizer]       (∧-shape + 2 iso)
      - [n5_N_plus_isolated_two_realizer]            (N-shape + 1 iso)
      - [n5_3claw_up_plus_isolated_two_realizer]     (3-claw-up + 1 iso)
      - [n5_3claw_down_plus_isolated_two_realizer]   (3-claw-down + 1 iso)
      - [n5_disjoint_chain3_chain2_two_realizer]     (3-chain + 2-chain)
      - [n5_V_plus_chain_two_realizer]               (V-shape + 2-chain)
      - [n5_inv_V_plus_chain_two_realizer]           (∧-shape + 2-chain)
      - [n5_chain4_plus_isolated_two_realizer]       (4-chain + 1 iso)
      - [n5_bowtie_plus_isolated_two_realizer]       (K_{2,2} + 1 iso)
      - [n5_diamond_plus_isolated_two_realizer]      (diamond + 1 iso)
      - [n5_pendant_plus_isolated_two_realizer]      (3-chain + pendant + 1 iso)
      - [n5_N_plus_pendant_two_realizer]             (N-shape + pendant d<e)
      - [n5_3claw_up_pendant_two_realizer]           (3-claw-up + pendant d<e)
      - [n5_3claw_down_pendant_two_realizer]         (3-claw-down + pendant e<d)
      - [n5_Y_up_plus_isolated_two_realizer]         (Y-up shape + 1 iso)
      - [n5_fence_two_realizer]                      (5-fence / W zigzag)
      - [n5_Y_down_plus_isolated_two_realizer]       (Y-down shape + 1 iso)
      - [n5_M_shape_two_realizer]                    (M-shape / dual fence)
      - [n5_4claw_up_two_realizer]                   (K_{1,4} up / 4-claw-up)
      - [n5_4claw_down_two_realizer]                 (K_{1,4} down / 4-claw-down)
      - [n5_inv_N_plus_isolated_two_realizer]        (dual-N / Z-shape + 1 iso)
      - [n5_chain3_plus_V_top_two_realizer]          (3-chain + V at top, 9 edges)
      - [n5_chain3_plus_inv_V_bottom_two_realizer]   (3-chain + inv-V at bottom, 9 edges)
      - [n5_diamond_pendant_above_two_realizer]      (diamond + pendant above top, 9 edges)
      - [n5_diamond_pendant_below_two_realizer]      (diamond + pendant below bottom, 9 edges)
      - [n5_bowtie_pendant_up_two_realizer]          (bowtie + pendant above one top, 7 edges)
      - [n5_bowtie_pendant_down_two_realizer]        (bowtie + pendant below one bottom, 7 edges)
      - [n5_chain3_top_pendant_plus_isolated_two_realizer]
                                                     (3-chain + top pendant + iso, dual of pendant)
      - [n5_inv_V_pendant_top_two_realizer]          (inv-V + pendant above apex, 5 edges + iso)
      - [n5_V_pendant_bot_two_realizer]              (V + pendant below bottom, 5 edges + iso)
      - [n5_chain4_top_pendant_two_realizer]         (4-chain + extra pendant below top, 7 edges)
      - [n5_chain4_bot_pendant_two_realizer]         (4-chain + extra pendant above bottom, 7 edges)
      - [n5_Y_down_pendant_two_realizer]             (Y-down + pendant below one branch, 8 edges)
      - [n5_Y_up_pendant_below_two_realizer]         (Y-up + pendant below the base, 9 edges)
      - [n5_Y_up_pendant_above_two_realizer]         (Y-up + pendant above one branch, 8 edges)
      - [n5_T_shape_extended_two_realizer]           (T-shape + pendant below branch tip, 6 edges)
      - [n5_3claw_up_chain_in_leaf_two_realizer]     (3-claw-up + chain in one leaf, 5 edges)
      - [n5_3claw_down_chain_in_leaf_two_realizer]   (3-claw-down + chain in one leaf, 5 edges)
      - [n5_3claw_up_chain_below_apex_two_realizer]
                                                     (3-claw-up + chain below apex, 7 edges)
      - [n5_3claw_down_chain_above_apex_two_realizer]
                                                     (3-claw-down + chain above apex, 7 edges)
      - [n5_N_plus_bottom_extension_two_realizer]
                                                     (N-shape + bottom extension on left chain, 5 edges)
      - [n5_N_plus_top_pendant_on_left_two_realizer]
                                                     (N-shape + top pendant on left chain a<e, 4 edges)
      - [n5_3claw_up_pendant_at_one_leaf_two_realizer]
                                                     (3-claw-up at c + pendant a<b at one leaf, 4 edges)
      - [n5_inv_N_plus_top_extension_two_realizer]
                                                     (inv-N + top-extension on one chain, 5 edges)
      - [n5_Y_down_pendant_above_two_realizer]
                                                     (Y-down + pendant above the top, 9 edges)
      - [n5_inv_N_plus_pendant_two_realizer]
                                                     (inv-N + pendant edge e<d, 5 edges)
      - [n5_3claw_down_extra_leaf_two_realizer]
                                                     (3-claw-down at b + extra child d at parent c, 4 edges)
      - [n5_3claw_up_extra_parent_two_realizer]
                                                     (3-claw-up at b + extra parent d at child c, 4 edges)
      - [n5_K_2_3_two_realizer]                      (K_{2,3} bipartite, 6 edges)
      - [n5_K_3_2_two_realizer]                      (K_{3,2} bipartite, 6 edges)
      - [n5_3claw_down_pendant_at_one_leaf_two_realizer]
                                                     (3-claw-down at c + pendant b<a at one leaf, 4 edges)
      - [n5_inv_N_plus_bot_pendant_on_left_two_realizer]
                                                     (inv-N + bot-pendant on left chain, 4 edges)
      - [n5_3fan_two_realizer]                       (3-fan / min+max+3-antichain middle, 7 edges)
      - [n5_pentagon_two_realizer]                   (N_5 pentagon: 2-chain + 3-chain joined at bot/top, 8 edges)
      - [n5_kite_two_realizer]                       (apex with 3 children, one extended to a top, 5 edges)
      - [n5_inv_kite_two_realizer]                   (apex with 3 parents, one extended from a bottom, 5 edges)
      - [n5_3_layer_diamond_two_realizer]            (3-layer poset: common min + K_{2,2} on top, 8 edges)
      - [n5_bowtie_top_cap_two_realizer]             (K_{2,2,1}: bowtie + common top cap, 8 edges)
      - [n5_bowtie_bot_cap_two_realizer]             (K_{1,2,2}: common bottom + bowtie cap, dual of top_cap, 8 edges)
      - [n5_V_chain_one_leaf_plus_isolated_two_realizer]
                                                     (V + chain extending one leaf + isolated, 4 edges)
      - [n5_inv_V_chain_one_leaf_plus_isolated_two_realizer]
                                                     (inv-V + chain extending one bottom + isolated, 4 edges, dual)
      - [n5_diamond_pendant_top_only_two_realizer]
                                                     (diamond + pendant below top only, 6 edges; no transitives to diamond bottom/intermediates)
      - [n5_diamond_pendant_bot_only_two_realizer]
                                                     (diamond + pendant above bottom only, 6 edges; dual of top_only)
      - [n5_K_2_3_minus_edge_two_realizer]
                                                     (K_{2,3} minus one edge, 5 edges; bowtie + half-pendant)
      - [n5_K_3_2_minus_edge_two_realizer]
                                                     (K_{3,2} minus one edge, 5 edges; dual; bowtie + half-pendant above)
      - [n5_K_2_3_minus_two_edges_two_realizer]
                                                     (K_{2,3} minus two edges from different bottoms to different tops, 4 edges)
      - [n5_K_3_2_minus_two_edges_two_realizer]
                                                     (K_{3,2} minus two edges from different tops to different bottoms, 4 edges; dual of K_{2,3} variant)
      - [n5_K_3_2_minus_matching_two_realizer]
                                                     (K_{3,2} minus a perfect matching: two non-adjacent edges, 4 edges; isomorphic to K_{2,3}_minus_two_edges — dispatch branch unreachable in practice)
      - [n5_one_edge_two_realizer]                   (single edge)

    Residual fall-through: routes to [n5_residual_classes_two_realizer]
    (focused admit) with the witness edge plus a second edge. *)

(** Micro-case (ii) of the second-edge cascade inside the residual handler:
    second edge is [(r, s)].  The carrier admits a third strict edge in
    one of 18 labelings (routed to upstream per-class lemmas) or, if no
    third edge exists, forms two disjoint chains [(p,q)] and [(r,s)] plus
    isolated [t] — contradicting [HnDisj]. *)
Lemma n5_dispatcher_microcase_ii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 r s)
    (Hnot_pq : ~ (r = p /\ s = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists.  Peel off well-defined 3rd-edge
       labelings that match upstream per-class shapes; route the
       remainder to the focused admit. *)
    (* Sub-case (a): third edge is [(q, t)].  By transitivity R2 p t.
       If no fourth edge exists beyond {(p,q),(q,t),(p,t),(r,s)}, the
       carrier is the 3-chain [p < q < t] disjoint from chain [r < s],
       contradicting [HnCC]. *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRpt_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urs. }
    (* Sub-case (b): third edge is [(t, p)].  Symmetric to (a) but with
       t<p<q chain. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists t, p, q, r, s.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRtq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_urs. }
    (* Sub-case (c): third edge is [(s, t)].  By transitivity R2 r t.
       Carrier is 3-chain [r < s < t] disjoint from chain [p < q]. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r s t HRxy HRst_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = s /\ b = t) /\ ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, s, t, p, q.
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        split; [exact HRrt_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_ust |]. exact Hnot_urt. }
    (* Sub-case (d): third edge is [(t, r)].  By transitivity R2 t s.
       Carrier is 3-chain [t < r < s] disjoint from chain [p < q]. *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t r s HRtr HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = t /\ b = r) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists t, r, s, p, q.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRtr |].
        split; [exact HRxy |].
        split; [exact HRts_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_utr |]. exact Hnot_uts. }
    (* Sub-case (e): third edge is [(p, t)].  V at [p] with leaves [q],
       [t], plus chain [r < s].  Contradicts [HnVc]. *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnVc.
        n5_split_witness p q t r s.
        n5_close_forall_via Hno_fourth. }
    (* Sub-case (f): third edge is [(t, q)].  Inv-V at [q] with bottoms
       [p], [t], plus chain [r < s].  Contradicts [HninvVc]. *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HninvVc.
        n5_split_witness p t q r s.
        n5_close_forall_via Hno_fourth. }
    (* Sub-case (g): third edge is [(r, t)].  V at [r] with leaves [s],
       [t], plus chain [p < q].  Contradicts [HnVc]. *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists r, s, t, p, q.
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrt |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |]. exact Hnot_urt. }
    (* Sub-case (h): third edge is [(t, s)].  Inv-V at [s] with bottoms
       [r], [t], plus chain [p < q].  Contradicts [HninvVc]. *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HninvVc.
        exists r, t, s, p, q.
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |]. exact Hnot_uts. }
    (* Sub-case (i): third edge is [(q, r)].  By transitivity, R2 contains
       the 4-chain [p < q < r < s] plus isolated [t].  Contradicts [HnC4]. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      assert (HRqs : R2 q s) by exact (HR2.(poset_trans) q r s HRqr HRxy).
      assert (HRps : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = r /\ b = s) /\ ~ (a = p /\ b = r) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRps |].
        split; [exact HRqs |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; right; right; right; exact Huqs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* Sub-case (j): third edge is [(s, p)].  By transitivity, R2 contains
       the 4-chain [r < s < p < q] plus isolated [t].  Contradicts [HnC4]. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRrp : R2 r p) by exact (HR2.(poset_trans) r s p HRxy HRsp).
      assert (HRsq : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      assert (HRrq : R2 r q) by exact (HR2.(poset_trans) r s q HRxy HRsq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = s /\ b = p) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists r, s, p, q, t.
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRrp |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_usq. }
    (* Sub-case (k): third edge is [(p, r)].  By transitivity R2 p s.
       Carrier is 3-chain [p<r<s] + pendant [p<q] (HnPd). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p r s HRpr HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = p /\ b = r) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnPd.
        exists p, r, s, q, t.
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRpr |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_upr |]. exact Hnot_ups. }
    (* Sub-case (l): third edge is [(r, p)].  By transitivity R2 r q.
       Carrier is 3-chain [r<p<q] + pendant [r<s] (HnPd). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* Sub-case (o): third edge is [(q, s)].  By transitivity R2 p s.
       R2 = {(p,q),(r,s),(q,s),(p,s)}: 3-chain p<q<s + pendant r<s (HnTopP). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnTopP.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRxy |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* Sub-case (p): third edge is [(s, q)].  By transitivity R2 r q.
       R2 = {(p,q),(r,s),(s,q),(r,q)}: 3-chain r<s<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r s q HRxy HRsq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnTopP.
        exists r, s, q, p, t.
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpt_neq |].
        split; [exact HRxy |].
        split; [exact HRsq |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* Sub-case (m): third edge is [(p, s)].  R2 contains {(p,q),(p,s),
       (r,s)}: N-shape (HnN) with a=r, c=p, b=s, d=q, plus isolated t.
       Note: positioned after (o) so that when 3rd edge is (q,s) — which
       also implies R2 p s by transitivity — case (o) fires first. *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists r, s, p, q, t.
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |]. exact Hnot_ups. }
    (* Sub-case (n): third edge is [(r, q)].  R2 contains {(p,q),(r,s),
       (r,q)}: N-shape with a=p, b=q, c=r, d=s, plus isolated t.
       Note: positioned after (p) so that when 3rd edge is (s,q) — which
       also implies R2 r q by transitivity — case (p) fires first. *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRrq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urs |]. exact Hnot_urq. }
    (* Sub-case (q): third edge is [(q, p)] — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* Sub-case (r): third edge is [(s, r)] — antisymmetry contradiction. *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { exfalso. apply Hrs_neq.
      exact (HR2.(poset_antisym) r s HRxy HRsr). }
    (* All 18 possible 3rd-edge labelings are ruled out: by Hcov5 the
       witness (a, b) from Hthird must be one of the 18 remaining ordered
       pairs over {p, q, r, s, t} (excluding diagonal and (p,q), (r,s)),
       and each negative classical hypothesis above rejects one. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_rs]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rs; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRts; exact HRab ].
  - (* No third edge: build the disjoint-chains witness and contradict
       [HnDisj]. *)
    exfalso. apply HnDisj.
    exists p, q, r, s, t.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
      [right; exact Hurs |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_urs.
Qed.

(** Micro-case (iii) of the second-edge cascade inside the residual handler:
    second edge is [(s, r)].  Extracted from
    [n5_nonantichain_nonchain_two_realizer] so that its Qed-closure compiles
    independently of the surrounding ~17k-line cascade.

    Shape: if no third strict edge exists, the carrier consists of disjoint
    chains [(p, q)] and [(s, r)] plus isolated [t], contradicting [HnDisj];
    otherwise route to [n5_residual_classes_two_realizer]. *)
Lemma n5_dispatcher_microcase_iii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (HRpq : R2 p q)
    (HRxy : R2 s r)
    (Hnot_pq : ~ (s = p /\ r = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d)))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = r)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists: route to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, s, r.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRxy |].
    exact Hnot_pq.
  - exfalso. apply HnDisj.
    exists p, q, s, r, t.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hst_neq |].
    split; [exact Hrt_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
      [right; exact Husr |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_usr.
Qed.

(** Micro-case (iv) of the second-edge cascade inside the residual handler:
    second edge is [(r, t)].  The carrier admits a third strict edge in one
    of 18 labelings (routed to upstream per-class lemmas) or, if no third
    edge exists, forms two disjoint chains [(p,q)] and [(r,t)] plus isolated
    [s] — contradicting [HnDisj]. *)
Lemma n5_dispatcher_microcase_iv :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 r t)
    (Hnot_pq : ~ (r = p /\ t = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. *)
    (* (a) third edge = (q, s): p<q<s chain + r<t chain (HnCC). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRps_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (b) third edge = (s, p): s<p<q chain + r<t chain (HnCC). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists s, p, q, r, t.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRsq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (c) third edge = (t, s): r<t<s chain + p<q chain (HnCC). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r t s HRxy HRts).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = t /\ b = s) /\ ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists r, t, s, p, q.
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRrs_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_uts |]. exact Hnot_urs. }
    (* (d) third edge = (s, r): s<r<t chain + p<q chain (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { assert (HRst_new : R2 s t) by exact (HR2.(poset_trans) s r t HRsr HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = s /\ b = r) /\ ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists s, r, t, p, q.
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRsr |].
        split; [exact HRxy |].
        split; [exact HRst_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [left; exact Husr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_usr |]. exact Hnot_ust. }
    (* (e) third edge = (p, s): V at p with leaves q, s + chain r<t (HnVc). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnVc.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (f) third edge = (s, q): inv-V at q with bottoms p, s + chain r<t (HninvVc). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (g) third edge = (r, s): V at r with leaves t, s + chain p<q (HnVc). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists r, t, s, p, q.
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrs |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |]. exact Hnot_urs. }
    (* (h) third edge = (s, t): inv-V at t with bottoms r, s + chain p<q (HninvVc). *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists r, s, t, p, q.
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |]. exact Hnot_ust. }
    (* (i) third edge = (q, r): 4-chain p<q<r<t + iso s (HnC4). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      assert (HRqt : R2 q t) by exact (HR2.(poset_trans) q r t HRqr HRxy).
      assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = r /\ b = t) /\ ~ (a = p /\ b = r) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRpt_new |].
        split; [exact HRqt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; right; right; right; exact Huqt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (j) third edge = (t, p): 4-chain r<t<p<q + iso s (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRrp : R2 r p) by exact (HR2.(poset_trans) r t p HRxy HRtp).
      assert (HRtq : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRrq : R2 r q) by exact (HR2.(poset_trans) r t q HRxy HRtq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = t /\ b = p) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists r, t, p, q, s.
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRrp |].
        split; [exact HRrq |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    (* (k) third edge = (p, r): 3-chain p<r<t + pendant p<q (HnPd). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p r t HRpr HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = p /\ b = r) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnPd.
        exists p, r, t, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRpr |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_upr |]. exact Hnot_upt. }
    (* (l) third edge = (r, p): 3-chain r<p<q + pendant r<t (HnPd). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (o) third edge = (q, t): 3-chain p<q<t + pendant r<t (HnTopP). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnTopP.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRxy |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (p) third edge = (t, q): 3-chain r<t<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r t q HRxy HRtq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
        exists r, t, q, p, s.
        split; [exact Hrt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hps_neq |].
        split; [exact HRxy |].
        split; [exact HRtq |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_utq |]. exact Hnot_urq. }
    (* (m) third edge = (p, t): N-shape r<t,p<t,p<q (HnN). *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists r, t, p, q, s.
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRpt_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |]. exact Hnot_upt. }
    (* (n) third edge = (r, q): N-shape p<q,r<q,r<t (HnN). *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = t) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRrq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urt |]. exact Hnot_urq. }
    (* (q) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (r) third edge = (t, r) — antisymmetry with HRxy : R2 r t. *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { exfalso. apply Hrt_neq.
      exact (HR2.(poset_antisym) r t HRxy HRtr). }
    (* All 18 possible 3rd-edge labelings ruled out. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_rt]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rt; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRts; exact HRab ].
  - exfalso. apply HnDisj.
    exists p, q, r, t, s.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hrs_neq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
      [right; exact Hurt |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_urt.
Qed.

(** Micro-case (v) of the second-edge cascade inside the residual handler:
    second edge is [(t, r)].  Mirrors micro-case (iv) under [r ↔ t]: the
    third-edge expansion routes 17 well-defined labelings to upstream
    per-class lemmas / antisymmetry, and the residual falls through to
    [n5_residual_classes_two_realizer]; if no third edge exists, the
    carrier forms two disjoint chains [(p,q)] and [(t,r)] plus isolated
    [s] — contradicting [HnDisj]. *)
Lemma n5_dispatcher_microcase_v :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (HRpq : R2 p q)
    (HRxy : R2 t r)
    (Hnot_pq : ~ (t = p /\ r = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. *)
    (* (a) third edge = (q, s): p<q<s chain + t<r chain (HnCC). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRps_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* (b) third edge = (s, p): s<p<q chain + t<r chain (HnCC). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists s, p, q, t, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRsq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* (c) third edge = (r, s): t<r<s chain + p<q chain (HnCC).
       (Mirror of (iv) sub-case (c) under r↔t.) *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t r s HRxy HRrs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = r /\ b = s) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
        exists t, r, s, p, q.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrs |].
        split; [exact HRts_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_urs |]. exact Hnot_uts. }
    (* (d) third edge = (s, t): s<t<r chain + p<q chain (HnCC).
       (Mirror of (iv) sub-case (d) under r↔t.) *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s t r HRst HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = s /\ b = t) /\ ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists s, t, r, p, q.
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRst |].
        split; [exact HRxy |].
        split; [exact HRsr_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; left; exact Hutr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_ust |]. exact Hnot_usr. }
    (* (e) third edge = (p, s): V at p with leaves q, s + chain t<r (HnVc). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnVc.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* (f) third edge = (s, q): inv-V at q with bottoms p, s + chain t<r (HninvVc). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, s, q, t, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* (g) third edge = (t, s): V at t with leaves r, s + chain p<q (HnVc).
       (Mirror of (iv) sub-case (g) under r↔t.) *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVc.
        exists t, r, s, p, q.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |]. exact Hnot_uts. }
    (* (h) third edge = (s, r): inv-V at r with bottoms t, s + chain p<q (HninvVc).
       (Mirror of (iv) sub-case (h) under r↔t.) *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists t, s, r, p, q.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |]. exact Hnot_usr. }
    (* (i) third edge = (q, t): 4-chain p<q<t<r + iso s (HnC4).
       (Mirror of (iv) sub-case (i) under r↔t.) *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      assert (HRqr : R2 q r) by exact (HR2.(poset_trans) q t r HRqt HRxy).
      assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = t /\ b = r) /\ ~ (a = p /\ b = t) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRxy |].
        split; [exact HRpt_new |].
        split; [exact HRpr_new |].
        split; [exact HRqr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; right; right; right; exact Huqr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (j) third edge = (r, p): 4-chain t<r<p<q + iso s (HnC4).
       (Mirror of (iv) sub-case (j) under r↔t.) *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRtp_new : R2 t p) by exact (HR2.(poset_trans) t r p HRxy HRrp).
      assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t r q HRxy HRrq_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = r /\ b = p) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists t, r, p, q, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRrq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_urq. }
    (* (k) third edge = (p, t): 3-chain p<t<r + pendant p<q (HnPd).
       (Mirror of (iv) sub-case (k) under r↔t.) *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p t r HRpt HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
        exists p, t, r, q, s.
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRpt |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; left; exact Hutr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_upt |]. exact Hnot_upr. }
    (* (l) third edge = (t, p): 3-chain t<p<q + pendant t<r (HnPd).
       (Mirror of (iv) sub-case (l) under r↔t.) *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists t, p, q, r, s.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (o) third edge = (q, r): 3-chain p<q<r + pendant t<r (HnTopP).
       (Mirror of (iv) sub-case (o) under r↔t.) *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnTopP.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRxy |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (p) third edge = (r, q): 3-chain t<r<q + pendant p<q (HnTopP).
       (Mirror of (iv) sub-case (p) under r↔t.) *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t r q HRxy HRrq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnTopP.
        exists t, r, q, p, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hps_neq |].
        split; [exact HRxy |].
        split; [exact HRrq |].
        split; [exact HRpq |].
        split; [exact HRtq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    (* (m) third edge = (p, r): N-shape t<r, p<r, p<q (HnN).
       (Mirror of (iv) sub-case (m) under r↔t.) *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, r, p, q, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRpr_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |]. exact Hnot_upr. }
    (* (n) third edge = (t, q): N-shape p<q, t<q, t<r (HnN).
       (Mirror of (iv) sub-case (n) under r↔t.) *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRtq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utr |]. exact Hnot_utq. }
    (* (q) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (r) third edge = (r, t) — antisymmetry with HRxy : R2 t r. *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { exfalso. apply Hrt_neq.
      exact (HR2.(poset_antisym) r t HRrt HRxy). }
    (* Otherwise route remaining third-edge cases to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, t, r.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [exact HRxy |].
    exact Hnot_pq.
  - exfalso. apply HnDisj.
    exists p, q, t, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
      [right; exact Hutr |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_utr.
Qed.

(** Micro-case (vi) of the second-edge cascade inside the residual handler:
    second edge is [(s, t)].  Mirrors micro-case (iv) under [r ↔ s]: the
    third-edge expansion routes 18 well-defined labelings to upstream
    per-class lemmas / antisymmetry; if no third edge exists, the carrier
    forms two disjoint chains [(p,q)] and [(s,t)] plus isolated [r] —
    contradicting [HnDisj]. *)
Lemma n5_dispatcher_microcase_vi :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 s t)
    (Hnot_pq : ~ (s = p /\ t = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. *)
    (* (a) third edge = (q, r): p<q<r chain + s<t chain (HnCC). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRpr_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (b) third edge = (r, p): r<p<q chain + s<t chain (HnCC). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    (* (c) third edge = (t, r): s<t<r chain + p<q chain (HnCC). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s t r HRxy HRtr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = t /\ b = r) /\ ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists s, t, r, p, q.
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRtr |].
        split; [exact HRsr_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; left; exact Hutr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_utr |]. exact Hnot_usr. }
    (* (d) third edge = (r, s): r<s<t chain + p<q chain (HnCC). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r s t HRrs HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = r /\ b = s) /\ ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, s, t, p, q.
        split; [exact Hrs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRrs |].
        split; [exact HRxy |].
        split; [exact HRrt_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_urs |]. exact Hnot_urt. }
    (* (e) third edge = (p, r): V at p with leaves q, r + chain s<t (HnVc). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
      - exfalso. apply HnVc.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (f) third edge = (r, q): inv-V at q with bottoms p, r + chain s<t (HninvVc). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    (* (g) third edge = (s, r): V at s with leaves t, r + chain p<q (HnVc). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRsr |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists s, t, r, p, q.
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRsr |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_usr. }
    (* (h) third edge = (r, t): inv-V at t with bottoms s, r + chain p<q (HninvVc). *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists s, r, t, p, q.
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_urt. }
    (* (i) third edge = (q, s): 4-chain p<q<s<t + iso r (HnC4). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      assert (HRqt : R2 q t) by exact (HR2.(poset_trans) q s t HRqs HRxy).
      assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = s /\ b = t) /\ ~ (a = p /\ b = s) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        split; [exact HRqt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; right; right; right; exact Huqt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (j) third edge = (t, p): 4-chain s<t<p<q + iso r (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRsp : R2 s p) by exact (HR2.(poset_trans) s t p HRxy HRtp).
      assert (HRtq : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRsq : R2 s q) by exact (HR2.(poset_trans) s t q HRxy HRtq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = t /\ b = p) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists s, t, p, q, r.
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRsp |].
        split; [exact HRsq |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (k) third edge = (p, s): 3-chain p<s<t + pendant p<q (HnPd). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p s t HRps HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnPd.
        exists p, s, t, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRps |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (l) third edge = (s, p): 3-chain s<p<q + pendant s<t (HnPd). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists s, p, q, t, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (o) third edge = (q, t): 3-chain p<q<t + pendant s<t (HnTopP). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnTopP.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRxy |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (p) third edge = (t, q): 3-chain s<t<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s t q HRxy HRtq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
        exists s, t, q, p, r.
        split; [exact Hst_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hpr_neq |].
        split; [exact HRxy |].
        split; [exact HRtq |].
        split; [exact HRpq |].
        split; [exact HRsq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_utq |]. exact Hnot_usq. }
    (* (m) third edge = (p, t): N-shape s<t,p<t,p<q (HnN). *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists s, t, p, q, r.
        split; [exact Hst_neq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRpt_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_upt. }
    (* (n) third edge = (s, q): N-shape p<q,s<q,s<t (HnN). *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = t) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq_third |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRsq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ust |]. exact Hnot_usq. }
    (* (q) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (r) third edge = (t, s) — antisymmetry with HRxy : R2 s t. *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { exfalso. apply Hst_neq.
      exact (HR2.(poset_antisym) s t HRxy HRts). }
    (* All 18 possible 3rd-edge labelings ruled out. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_st]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_st; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRts; exact HRab
        | apply HnRtr; exact HRab ].
  - exfalso. apply HnDisj.
    exists p, q, s, t, r.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hst_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
      [right; exact Hust |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_ust.
Qed.

(** Micro-case (vii) of the second-edge cascade inside the residual handler:
    second edge is [(t, s)].  Mirrors micro-case (v) under [r ↔ s]: the
    third-edge expansion routes 17 well-defined labelings to upstream
    per-class lemmas / antisymmetry, and the residual falls through to
    [n5_residual_classes_two_realizer]; if no third edge exists, the
    carrier forms two disjoint chains [(p,q)] and [(t,s)] plus isolated
    [r] — contradicting [HnDisj]. *)
Lemma n5_dispatcher_microcase_vii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (HRpq : R2 p q)
    (HRxy : R2 t s)
    (Hnot_pq : ~ (t = p /\ s = q))
    (HnDisj :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj
         HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. *)
    (* (a) third edge = (q, r): p<q<r chain + t<s chain (HnCC). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnCC.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRpr_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* (b) third edge = (r, p): r<p<q chain + t<s chain (HnCC). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRrq_new |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    (* (c) third edge = (s, r): t<s<r chain + p<q chain (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t s r HRxy HRsr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = s /\ b = r) /\ ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRsr |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
        exists t, s, r, p, q.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRsr |].
        split; [exact HRtr_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_usr |]. exact Hnot_utr. }
    (* (d) third edge = (r, t): r<t<s chain + p<q chain (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r t s HRrt HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = r /\ b = t) /\ ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, t, s, p, q.
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRrt |].
        split; [exact HRxy |].
        split; [exact HRrs_new |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_urt |]. exact Hnot_urs. }
    (* (e) third edge = (p, r): V at p with leaves q, r + chain t<s (HnVc). *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
      - exfalso. apply HnVc.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* (f) third edge = (r, q): inv-V at q with bottoms p, r + chain t<s (HninvVc). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    (* (g) third edge = (t, r): V at t with leaves s, r + chain p<q (HnVc). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVc.
        exists t, s, r, p, q.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRtr |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; left; exact Hutr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_utr. }
    (* (h) third edge = (r, s): inv-V at s with bottoms t, r + chain p<q (HninvVc). *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_third |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists t, r, s, p, q.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hpq_neq |].
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_urs. }
    (* (i) third edge = (q, t): 4-chain p<q<t<s + iso r (HnC4). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      assert (HRqs : R2 q s) by exact (HR2.(poset_trans) q t s HRqt HRxy).
      assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = t /\ b = s) /\ ~ (a = p /\ b = t) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRxy |].
        split; [exact HRpt_new |].
        split; [exact HRps_new |].
        split; [exact HRqs |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; right; right; right; exact Huqs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (j) third edge = (s, p): 4-chain t<s<p<q + iso r (HnC4). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRtp_new : R2 t p) by exact (HR2.(poset_trans) t s p HRxy HRsp).
      assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t s q HRxy HRsq_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = s /\ b = p) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists t, s, p, q, r.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRsq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_usq. }
    (* (k) third edge = (p, t): 3-chain p<t<s + pendant p<q (HnPd). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p t s HRpt HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
        exists p, t, s, q, r.
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRpt |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_upt |]. exact Hnot_ups. }
    (* (l) third edge = (t, p): 3-chain t<p<q + pendant t<s (HnPd). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists t, p, q, s, r.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (o) third edge = (q, s): 3-chain p<q<s + pendant t<s (HnTopP). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnTopP.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRxy |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (p) third edge = (s, q): 3-chain t<s<q + pendant p<q (HnTopP). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t s q HRxy HRsq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnTopP.
        exists t, s, q, p, r.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hpr_neq |].
        split; [exact HRxy |].
        split; [exact HRsq |].
        split; [exact HRpq |].
        split; [exact HRtq_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (m) third edge = (p, s): N-shape t<s, p<s, p<q (HnN). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, s, p, q, r.
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_ups. }
    (* (n) third edge = (t, q): N-shape p<q, t<q, t<s (HnN). *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRtq_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uts |]. exact Hnot_utq. }
    (* (q) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (r) third edge = (s, t) — antisymmetry with HRxy : R2 t s. *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { exfalso. apply Hst_neq.
      exact (HR2.(poset_antisym) s t HRst HRxy). }
    (* Otherwise route remaining third-edge cases to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, t, s.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact HRxy |].
    exact Hnot_pq.
  - exfalso. apply HnDisj.
    exists p, q, t, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
      [right; exact Huts |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_uts.
Qed.

(** Micro-case (viii) of the second-edge cascade inside the residual handler:
    second edge is [(p, r)] — V at [p] with leaves [q] and [r], plus
    isolated [s], [t].  If no third strict edge exists, this contradicts
    [HnV] (the V+2isolated shape).  Otherwise the third-edge expansion
    peels off each well-defined labeling and routes to the matching
    upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_viii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 p r)
    (Hnot_pq : ~ (p = p /\ r = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawUp :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnVpb :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d a /\ R2 d b /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = b) \/ (x = d /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnV HnN HnClawUp HnCC HnVc HnC4 HnPd HnYup HnYdn HnTopP HnVpb.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (r, p) — antisymmetry with HRxy : R2 p r. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { exfalso. apply Hpr_neq.
      exact (HR2.(poset_antisym) p r HRxy HRrp). }
    (* (c) third edge = (q, r): 3-chain p<q<r + iso s, t (HnChain3).
       If a 4th edge exists, peel off all 14 well-defined labelings and
       route to upstream per-class shapes; the residual lemma is only
       reached via reduced 5th-edge witnesses inside each sub-branch. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = q /\ b = r)))
        as [Hfourth | Hno_fourth].
      - (* (c.i) fourth edge = (s, p): 4-chain s<p<q<r + iso t (HnC4). *)
        destruct (classic (R2 s p)) as [HRsp | HnRsp].
        { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
          assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq_new HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = p) /\
                    ~ (a = s /\ b = q) /\ ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
            split; [exact HRsp |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnC4.
            exists s, p, q, r, t.
            split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
            split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact Hst_neq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrt_neq |].
            split; [exact HRsp |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRsq_new |].
            split; [exact HRsr_new |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
              [left; exact Husp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; right; right; left; exact Husq |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; right; right; left; exact Husr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_usp |].
            split; [exact Hnot_usq |]. exact Hnot_usr. }
        (* (c.ii) fourth edge = (t, p): 4-chain t<p<q<r + iso s (HnC4). *)
        destruct (classic (R2 t p)) as [HRtp | HnRtp].
        { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
          assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq_new HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
            split; [exact HRtp |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnC4.
            exists t, p, q, r, s.
            split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
            split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrs_neq |].
            split; [exact HRtp |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRtq_new |].
            split; [exact HRtr_new |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; left; exact Hutr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_utr. }
        (* (c.iii) fourth edge = (r, s): 4-chain p<q<r<s + iso t (HnC4). *)
        destruct (classic (R2 r s)) as [HRrs_fourth | HnRrs_fourth].
        { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p r s HRxy HRrs_fourth).
          assert (HRqs_new : R2 q s) by exact (HR2.(poset_trans) q r s HRqr_third HRrs_fourth).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = r /\ b = s) /\
                    ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hrs_neq |].
            split; [exact HRrs_fourth |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnC4.
            exists p, q, r, s, t.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRrs_fourth |].
            split; [exact HRxy |].
            split; [exact HRps_new |].
            split; [exact HRqs_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
              [right; right; left; exact Hurs |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; right; right; left; exact Hups |].
            destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
              [right; right; right; right; right; exact Huqs |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_urs |].
            split; [exact Hnot_ups |]. exact Hnot_uqs. }
        (* (c.iv) fourth edge = (r, t): 4-chain p<q<r<t + iso s (HnC4). *)
        destruct (classic (R2 r t)) as [HRrt | HnRrt].
        { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p r t HRxy HRrt).
          assert (HRqt_new : R2 q t) by exact (HR2.(poset_trans) q r t HRqr_third HRrt).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = r /\ b = t) /\
                    ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hrt_neq |].
            split; [exact HRrt |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnC4.
            exists p, q, r, t, s.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hrs_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRrt |].
            split; [exact HRxy |].
            split; [exact HRpt_new |].
            split; [exact HRqt_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
              [right; right; left; exact Hurt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; right; right; left; exact Hupt |].
            destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
              [right; right; right; right; right; exact Huqt |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_urt |].
            split; [exact Hnot_upt |]. exact Hnot_uqt. }
        (* (c.v) fourth edge = (q, s): Y-up apex p, branch q->{r,s} (HnYup). *)
        destruct (classic (R2 q s)) as [HRqs | HnRqs].
        { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = q /\ b = s) /\
                    ~ (a = p /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqs_neq |].
            split; [exact HRqs |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnYup.
            exists p, q, r, s, t.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRqs |].
            split; [exact HRxy |].
            split; [exact HRps_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
              [right; right; left; exact Huqs |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; right; right; exact Hups |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_uqs |]. exact Hnot_ups. }
        (* (c.vi) fourth edge = (q, t): Y-up apex p, branch q->{r,t} (HnYup). *)
        destruct (classic (R2 q t)) as [HRqt | HnRqt].
        { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = q /\ b = t) /\
                    ~ (a = p /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqt_neq |].
            split; [exact HRqt |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnYup.
            exists p, q, r, t, s.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hrs_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRqt |].
            split; [exact HRxy |].
            split; [exact HRpt_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
              [right; right; left; exact Huqt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; right; right; exact Hupt |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_uqt |]. exact Hnot_upt. }
        (* (c.vii) fourth edge = (s, q): Y-down apex r, q parents p,s (HnYdn). *)
        destruct (classic (R2 s q)) as [HRsq | HnRsq].
        { assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = q) /\
                    ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
            split; [exact HRsq |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnYdn.
            exists r, q, p, s, t.
            split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
            split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact Hrt_neq |].
            split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
            split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
            split; [exact Hqt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRsq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRsr_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; left; exact Husq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; right; right; exact Husr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_usq |]. exact Hnot_usr. }
        (* (c.viii) fourth edge = (t, q): Y-down apex r, q parents p,t (HnYdn). *)
        destruct (classic (R2 t q)) as [HRtq | HnRtq].
        { assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq HRqr_third).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = q) /\
                    ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
            split; [exact HRtq |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnYdn.
            exists r, q, p, t, s.
            split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
            split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
            split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
            split; [exact Hrs_neq |].
            split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
            split; [exact Hqs_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRtr_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; left; exact Hutq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; left; exact Hupr |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; exact Hutr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |].
            split; [exact Hnot_utq |]. exact Hnot_utr. }
        (* (c.ix) fourth edge = (s, r): top pendant s<r (HnTopP). *)
        destruct (classic (R2 s r)) as [HRsr | HnRsr].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
            split; [exact HRsr |].
            intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
          - exfalso. apply HnTopP.
            exists p, q, r, s, t.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRsr |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; left; exact Husr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_usr. }
        (* (c.x) fourth edge = (t, r): top pendant t<r (HnTopP). *)
        destruct (classic (R2 t r)) as [HRtr | HnRtr].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
            split; [exact HRtr |].
            intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
          - exfalso. apply HnTopP.
            exists p, q, r, t, s.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hrs_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRtr |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; left; exact Hutr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_utr. }
        (* (c.xi) fourth edge = (p, s): bottom pendant p<s (HnPd). *)
        destruct (classic (R2 p s)) as [HRps | HnRps].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = p /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hps_neq |].
            split; [exact HRps |].
            intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
          - exfalso. apply HnPd.
            exists p, q, r, s, t.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRps |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; left; exact Hups |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_ups. }
        (* (c.xii) fourth edge = (p, t): bottom pendant p<t (HnPd). *)
        destruct (classic (R2 p t)) as [HRpt | HnRpt].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = p /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hpt_neq |].
            split; [exact HRpt |].
            intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
          - exfalso. apply HnPd.
            exists p, q, r, t, s.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hrs_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRpt |].
            split; [exact HRxy |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
              [right; right; left; exact Hupt |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_upt. }
        (* (c.xiii) fourth edge = (s, t): disjoint 2-chain s<t (HnCC). *)
        destruct (classic (R2 s t)) as [HRst | HnRst].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = s /\ b = t)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hst_neq |].
            split; [exact HRst |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnCC.
            exists p, q, r, s, t.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hrs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hst_neq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRst |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; left; exact Hupr |].
            destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
              [right; right; right; exact Hust |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_ust. }
        (* (c.xiv) fourth edge = (t, s): disjoint 2-chain t<s (HnCC). *)
        destruct (classic (R2 t s)) as [HRts | HnRts].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRts |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnCC.
            exists p, q, r, t, s.
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hrt_neq |].
            split; [exact Hrs_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRpq |].
            split; [exact HRqr_third |].
            split; [exact HRxy |].
            split; [exact HRts |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; left; exact Huqr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; left; exact Hupr |].
            destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
              [right; right; right; exact Huts |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_uts. }
        (* (c.xv) fourth edge = (r, q) — antisymmetry contradiction. *)
        destruct (classic (R2 r q)) as [HRrq | HnRrq].
        { exfalso. apply Hqr_neq.
          exact (HR2.(poset_antisym) q r HRqr_third HRrq). }
        (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
        exfalso.
        destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_pr Hnot_ab_qr]]]]]].
        destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
          destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
          subst a b;
          first
            [ apply Hab_neq; reflexivity
            | apply Hnot_ab_pq; split; reflexivity
            | apply Hnot_ab_qr; split; reflexivity
            | apply Hnot_ab_pr; split; reflexivity
            | apply HnRqp; exact HRab
            | apply HnRrq; exact HRab
            | apply HnRrp; exact HRab
            | apply HnRps; exact HRab
            | apply HnRpt; exact HRab
            | apply HnRqs; exact HRab
            | apply HnRqt; exact HRab
            | apply HnRrs_fourth; exact HRab
            | apply HnRrt; exact HRab
            | apply HnRsp; exact HRab
            | apply HnRsq; exact HRab
            | apply HnRsr; exact HRab
            | apply HnRst; exact HRab
            | apply HnRtp; exact HRab
            | apply HnRtq; exact HRab
            | apply HnRtr; exact HRab
            | apply HnRts; exact HRab ].
      - exfalso. apply HnChain3.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRqr_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; exact Huqr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) third edge = (r, q): 3-chain p<r<q + iso s, t (HnChain3). *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnChain3.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRrq_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_urq. }
    (* (e) third edge = (p, s): 3-claw-up at p with leaves q, r, s + iso t
       (HnClawUp). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnClawUp.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_ups. }
    (* (f) third edge = (p, t): 3-claw-up, iso s. *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnClawUp.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_upt. }
    (* (g) third edge = (s, p): V with pendant below the common bottom
       (HnVpb) with a=p, b=q, c=r, d=s. Edges a<b, a<c, d<a, d<b, d<c.
       iso t. *)
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s p r HRsp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnVpb.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (h) third edge = (t, p): V with pendant below (HnVpb), iso s. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      assert (HRtr_via : R2 t r) by exact (HR2.(poset_trans) t p r HRtp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVpb.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        split; [exact HRtr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (i) third edge = (q, s): pendant 3-chain p<q<s + pendant p<r
       (HnPd) with a=p, b=q, c=s, d=r. iso t. *)
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRqs_third |].
        split; [exact HRxy |].
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (j) third edge = (q, t): pendant 3-chain p<q<t + pendant p<r
       (HnPd), iso s. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRqt_third |].
        split; [exact HRxy |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (k) third edge = (r, s): pendant 3-chain p<r<s + pendant p<q
       (HnPd) with a=p, b=r, c=s, d=q. iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p r s HRxy HRrs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists p, r, s, q, t.
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        split; [exact HRpq |].
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; left; exact Hurs |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urs |]. exact Hnot_ups. }
    (* (l) third edge = (r, t): pendant 3-chain p<r<t + pendant p<q
       (HnPd), iso s. *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p r t HRxy HRrt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = r /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists p, r, t, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        split; [exact HRpq |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; left; exact Hurt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urt |]. exact Hnot_upt. }
    (* (m) third edge = (s, q): N-shape (a<b, c<b, c<d) with a=s, b=q,
       c=p, d=r. iso t. (HnN) *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnN.
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_usq. }
    (* (n) third edge = (t, q): N-shape with a=t, c=p, b=q, d=r. iso s. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists t, q, p, r, s.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRtq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_utq. }
    (* (o) third edge = (s, r): N-shape with a=s, b=r, c=p, d=q. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists s, r, p, q, t.
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRsr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [left; exact Husr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (p) third edge = (t, r): N-shape with a=t, b=r, c=p, d=q. iso s. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, r, p, q, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRtr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (q) third edge = (s, t): V at p + disjoint chain s<t (HnVc) with
       a=p, b=q, c=r, d=s, e=t. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnVc.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (r) third edge = (t, s): V at p + disjoint chain t<s (HnVc) with
       a=p, b=q, c=r, d=t, e=s. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVc.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_pr]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_pr; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRtr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRts_third; exact HRab ].
  - exfalso. apply HnV.
    exists p, q, r, s, t.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
      [right; exact Hupr |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_upr.
Qed.

(** Micro-case (i) of the second-edge cascade inside the residual handler:
    if the second strict edge is [(q, p)] then antisymmetry against
    [R2 p q] forces [p = q], contradicting [p <> q].  Routes to [False],
    so the residual realizer-existence goal follows by [exfalso]. *)
Lemma n5_dispatcher_microcase_i :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (p q : B)
    (Hpq_neq : p <> q)
    (HRpq : R2 p q)
    (HRqp : R2 q p),
  False.
Proof.
  intros B R2 HR2 p q Hpq_neq HRpq HRqp.
  apply Hpq_neq.
  exact (HR2.(poset_antisym) p q HRpq HRqp).
Qed.

(** Micro-case (ix) of the second-edge cascade inside the residual handler:
    second edge is [(p, s)] — V at [p] with leaves [q] and [s], plus
    isolated [r], [t].  If no third strict edge exists, this contradicts
    [HnV] (the V+2isolated shape).  Otherwise the third-edge expansion
    peels off each well-defined labeling and routes to the matching
    upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_ix :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 p s)
    (Hnot_pq : ~ (p = p /\ s = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawUp :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnVpb :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d a /\ R2 d b /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = b) \/ (x = d /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnV HnN HnClawUp HnVc HnPd HnVpb.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (s, p) — antisymmetry with HRxy : R2 p s. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRxy HRsp). }
    (* (c) third edge = (q, s): 3-chain p<q<s + iso r, t (HnChain3). *)
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnChain3.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRqs_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; exact Huqs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (d) third edge = (s, q): 3-chain p<s<q + iso r, t (HnChain3). *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnChain3.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRsq_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_usq. }
    (* (e) third edge = (p, r): 3-claw-up at p with leaves q, s, r + iso t
       (HnClawUp). *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnClawUp.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_upr. }
    (* (f) third edge = (p, t): 3-claw-up, iso r. *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnClawUp.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (g) third edge = (r, p): V with pendant below the common bottom
       (HnVpb) with a=p, b=q, c=s, d=r. Edges a<b, a<c, d<a, d<b, d<c.
       iso t. *)
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      assert (HRrs_via : R2 r s) by exact (HR2.(poset_trans) r p s HRrp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVpb.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        split; [exact HRrs_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (h) third edge = (t, p): V with pendant below (HnVpb), iso r. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      assert (HRts_via : R2 t s) by exact (HR2.(poset_trans) t p s HRtp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVpb.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        split; [exact HRts_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (i) third edge = (q, r): pendant 3-chain p<q<r + pendant p<s
       (HnPd) with a=p, b=q, c=r, d=s. iso t. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRqr_third |].
        split; [exact HRxy |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (j) third edge = (q, t): pendant 3-chain p<q<t + pendant p<s
       (HnPd), iso r. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRqt_third |].
        split; [exact HRxy |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (k) third edge = (s, r): pendant 3-chain p<s<r + pendant p<q
       (HnPd) with a=p, b=s, c=r, d=q. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p s r HRxy HRsr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists p, s, r, q, t.
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        split; [exact HRpq |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; left; exact Husr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_usr |]. exact Hnot_upr. }
    (* (l) third edge = (s, t): pendant 3-chain p<s<t + pendant p<q
       (HnPd), iso r. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p s t HRxy HRst_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = s /\ b = t) /\ ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists p, s, t, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        split; [exact HRpq |].
        split; [exact HRpt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; left; exact Hust |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_ust |]. exact Hnot_upt. }
    (* (m) third edge = (r, q): N-shape (a<b, c<b, c<d) with a=r, b=q,
       c=p, d=s. iso t. (HnN) *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists r, q, p, s, t.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urq. }
    (* (n) third edge = (t, q): N-shape with a=t, c=p, b=q, d=s. iso r. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists t, q, p, s, r.
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRtq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_utq. }
    (* (o) third edge = (r, s): N-shape with a=r, b=s, c=p, d=q. iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists r, s, p, q, t.
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRrs_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (p) third edge = (t, s): N-shape with a=t, b=s, c=p, d=q. iso r. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists t, s, p, q, r.
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRts_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (q) third edge = (r, t): V at p + disjoint chain r<t (HnVc) with
       a=p, b=q, c=s, d=r, e=t. *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (s) third edge = (t, r): V at p + disjoint chain t<r (HnVc) with
       a=p, b=q, c=s, d=t, e=r. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnVc.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_ps]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_ps; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRts_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRtr_third; exact HRab ].
  - exfalso. apply HnV.
    exists p, q, s, r, t.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hst_neq |].
    split; [exact Hrt_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
      [right; exact Hups |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_ups.
Qed.

(** Micro-case (x) of the second-edge cascade inside the residual handler:
    second edge is [(p, t)] — V at [p] with leaves [q] and [t], plus
    isolated [r], [s].  If no third strict edge exists, this contradicts
    [HnV] (the V+2isolated shape).  Otherwise the third-edge expansion
    peels off each well-defined labeling and routes to the matching
    upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_x :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 p t)
    (Hnot_pq : ~ (p = p /\ t = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawUp :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = d) \/ (x = a /\ y = c)))))
    (HnVpb :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 a c /\ R2 d a /\ R2 d b /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = b) \/ (x = d /\ y = c))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnV HnN HnClawUp HnVc HnPd HnVpb.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { exfalso. apply Hpt_neq.
      exact (HR2.(poset_antisym) p t HRxy HRtp). }
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = q /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnChain3.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRqt_third |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; exact Huqt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnChain3.
        exists p, t, q, s, r.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRtq_third |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_utq. }
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnClawUp.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_ups. }
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnClawUp.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_upr. }
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      assert (HRst_via : R2 s t) by exact (HR2.(poset_trans) s p t HRsp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnVpb.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        split; [exact HRst_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      assert (HRrt_via : R2 r t) by exact (HR2.(poset_trans) r p t HRrp_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVpb.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        split; [exact HRrt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRqs_third |].
        split; [exact HRxy |].
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnPd.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRqr_third |].
        split; [exact HRxy |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p t s HRxy HRts_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = t /\ b = s) /\ ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists p, t, s, q, r.
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRxy |].
        split; [exact HRts_third |].
        split; [exact HRpq |].
        split; [exact HRps_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; left; exact Huts |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uts |]. exact Hnot_ups. }
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p t r HRxy HRtr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = t /\ b = r) /\ ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnPd.
        exists p, t, r, q, s.
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRxy |].
        split; [exact HRtr_third |].
        split; [exact HRpq |].
        split; [exact HRpr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; left; exact Hutr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_utr |]. exact Hnot_upr. }
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnN.
        exists s, q, p, t, r.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRsq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_usq. }
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists r, q, p, t, s.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrq_third |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_urq. }
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact HRst_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists s, t, p, q, r.
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRst_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact HRrt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists r, t, p, q, s.
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRrt_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnVc.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_usr. }
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnVc.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; left; exact Hupt |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_upt |]. exact Hnot_urs. }
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_pt]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_pt; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRts_third; exact HRab
        | apply HnRtr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRrs_third; exact HRab ].
  - exfalso. apply HnV.
    exists p, q, t, s, r.
    split; [exact Hpq_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
      [right; exact Hupt |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_upt.
Qed.

(** Micro-case (xi) of the second-edge cascade inside the residual handler:
    second edge is [(r, q)] — inv-V at [q] with bottoms [p] and [r], plus
    isolated [s], [t].  If no third strict edge exists, this contradicts
    [HninvV] (the inv-V+2isolated shape).  Otherwise the third-edge
    expansion peels off each well-defined labeling and routes to the
    matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xi :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 r q)
    (Hnot_pq : ~ (r = p /\ q = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HninvV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawDn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a d /\ R2 b d /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HniVcol :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d a /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = c)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q)))
    as [Hthird | Hno_third].
  - destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { exfalso. apply Hqr_neq.
      exact (HR2.(poset_antisym) q r HRqr HRxy). }
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnChain3.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpr_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [left; exact Hupr |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_upr. }
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = p)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp_third |].
        intros [_ Hpq]; apply Hpq_neq; exact Hpq.
      - exfalso. apply HnChain3.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrp_third |].
        split; [exact HRpq |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urp. }
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists r, q, p, s, t.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_ups. }
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists r, q, p, t, s.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_upt. }
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HniVcol.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HniVcol.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      assert (HRrs_via : R2 r s) by exact (HR2.(poset_trans) r q s HRxy HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqs_third |].
        split; [exact HRps_via |].
        split; [exact HRrs_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      assert (HRrt_via : R2 r t) by exact (HR2.(poset_trans) r q t HRxy HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists t, q, p, r, s.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt_third |].
        split; [exact HRpt_via |].
        split; [exact HRrt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnClawDn.
        exists p, r, s, q, t.
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_usq. }
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnClawDn.
        exists p, r, t, q, s.
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnN.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s r q HRsr_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = r) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HniVcol.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsr_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usr |]. exact Hnot_usq. }
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t r q HRtr_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = r) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HniVcol.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtr_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [left; exact Hurq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utr |]. exact Hnot_utq. }
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, r, q, s, t.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HninvVc.
        exists p, r, q, t, s.
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_rq]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRtr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRts_third; exact HRab ].
  - exfalso. apply HninvV.
    exists p, r, q, s, t.
    split; [exact Hpr_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
      [right; exact Hurq |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_urq.
Qed.

(** Micro-case (xii) of the second-edge cascade inside the residual handler:
    second edge is [(s, q)] — inv-V at [q] with bottoms [p] and [s], plus
    isolated [r], [t].  If no third strict edge exists, this contradicts
    [HninvV] (the inv-V+2isolated shape).  Otherwise the third-edge
    expansion peels off each well-defined labeling and routes to the
    matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 s q)
    (Hnot_pq : ~ (s = p /\ q = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HninvV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawDn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a d /\ R2 b d /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HniVcol :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d a /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = c)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (q, s) — antisymmetry with HRxy : R2 s q. *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRqs HRxy). }
    (* (c) third edge = (p, s): 3-chain p<s<q + iso r, t (HnChain3). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnChain3.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRps_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [left; exact Hups |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_ups. }
    (* (d) third edge = (s, p): 3-chain s<p<q + iso r, t (HnChain3). *)
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = p)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact HRsp_third |].
        intros [_ Hpq]; apply Hpq_neq; exact Hpq.
      - exfalso. apply HnChain3.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsp_third |].
        split; [exact HRpq |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_usp. }
    (* (e) third edge = (p, r): N-shape (a→b, c→b, c→d with
       a=s, b=q, c=p, d=r); iso t (HnN). *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists s, q, p, r, t.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_upr. }
    (* (f) third edge = (p, t): N-shape, iso r (HnN). *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnN.
        exists s, q, p, t, r.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; exact Hupt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_upt. }
    (* (g) third edge = (r, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=s, d=r. Edges a<c, b<c, d<a, d<c. iso t. *)
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HniVcol.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (h) third edge = (t, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=s, d=t. iso r. *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HniVcol.
        exists p, s, q, t, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtp_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (i) third edge = (q, r): Y-down at r (HnYdn) with a=r, b=q,
       c=p, d=s. R2 c b, R2 d b, R2 b a, R2 c a, R2 d a. iso t. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s q r HRxy HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists r, q, p, s, t.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqr_third |].
        split; [exact HRpr_via |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (j) third edge = (q, t): Y-down at t (HnYdn), iso r. *)
    destruct (classic (R2 q t)) as [HRqt_third | HnRqt_third].
    { assert (HRpt_via : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt_third).
      assert (HRst_via : R2 s t) by exact (HR2.(poset_trans) s q t HRxy HRqt_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = q /\ b = t) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists t, q, p, s, r.
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt_third |].
        split; [exact HRpt_via |].
        split; [exact HRst_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (k) third edge = (r, q): 3-claw-down (HnClawDn) with
       a=p, b=s, c=r, d=q (R2 a d, R2 b d, R2 c d). iso t. *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnClawDn.
        exists p, s, r, q, t.
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* (l) third edge = (t, q): 3-claw-down, iso r. *)
    destruct (classic (R2 t q)) as [HRtq_third | HnRtq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnClawDn.
        exists p, s, t, q, r.
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (m) third edge = (s, r): N-shape (a→b, c→b, c→d) with
       a=p, b=q, c=s, d=r. iso t. *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnN.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (n) third edge = (s, t): N-shape, iso r. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnN.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; exact Hust |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (o) third edge = (r, s): inv-V chain (HniVcol) with
       a=s, c=q, b=p, d=r (a<c, b<c, d<a, d<c). iso t. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r s q HRrs_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = s) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HniVcol.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urs |]. exact Hnot_urq. }
    (* (p) third edge = (t, s): inv-V chain (HniVcol), iso r. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t s q HRts_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = s) /\ ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HniVcol.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRts_third |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [left; exact Husq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uts |]. exact Hnot_utq. }
    (* (q) third edge = (r, t): inv-V + disjoint chain (HninvVc) with
       a=p, b=s, c=q, d=r, e=t (R2 a c, R2 b c, R2 d e). *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HninvVc.
        exists p, s, q, r, t.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; exact Hurt |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (r) third edge = (t, r): inv-V + disjoint chain (HninvVc) with
       a=p, b=s, c=q, d=t, e=r. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HninvVc.
        exists p, s, q, t, r.
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_sq]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_sq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRqt_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRtq_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRrs_third; exact HRab
        | apply HnRts_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRtr_third; exact HRab ].
  - exfalso. apply HninvV.
    exists p, s, q, r, t.
    split; [exact Hps_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hst_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hrt_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
      [right; exact Husq |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_usq.
Qed.

(** Micro-case (xiii) of the second-edge cascade inside the residual handler:
    second edge is [(t, q)] — inv-V at [q] with bottoms [p] and [t], plus
    isolated [r], [s].  If no third strict edge exists, this contradicts
    [HninvV] (the inv-V+2isolated shape).  Otherwise the third-edge
    expansion peels off each well-defined labeling and routes to the
    matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xiii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 t q)
    (Hnot_pq : ~ (t = p /\ q = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HninvV :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\
            (forall x y : B,
               R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))))
    (HnN :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 c b /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    (HnClawDn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a d /\ R2 b d /\ R2 c d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d)))))
    (HninvVc :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    (HniVcol :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a c /\ R2 b c /\ R2 d a /\ R2 d c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = a) \/
                (x = d /\ y = c)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn.
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q)))
    as [Hthird | Hno_third].
  - (* A third strict edge exists. Peel off well-defined 3rd-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) third edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) third edge = (q, t) — antisymmetry with HRxy : R2 t q. *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { exfalso. apply Hqt_neq.
      exact (HR2.(poset_antisym) q t HRqt HRxy). }
    (* (c) third edge = (p, t): 3-chain p<t<q + iso s, r (HnChain3). *)
    destruct (classic (R2 p t)) as [HRpt_third | HnRpt_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = p /\ b = t)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnChain3.
        exists p, t, q, s, r.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpt_third |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [left; exact Hupt |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; exact Hutq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_upt. }
    (* (d) third edge = (t, p): 3-chain t<p<q + iso s, r (HnChain3). *)
    destruct (classic (R2 t p)) as [HRtp_third | HnRtp_third].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = p)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp_third |].
        intros [_ Hpq]; apply Hpq_neq; exact Hpq.
      - exfalso. apply HnChain3.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRtp_third |].
        split; [exact HRpq |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_utp. }
    (* (e) third edge = (p, s): N-shape (a→b, c→b, c→d with
       a=t, b=q, c=p, d=s); iso r (HnN). *)
    destruct (classic (R2 p s)) as [HRps_third | HnRps_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = p /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps_third |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnN.
        exists t, q, p, s, r.
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; exact Hups |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_ups. }
    (* (f) third edge = (p, r): N-shape, iso s (HnN). *)
    destruct (classic (R2 p r)) as [HRpr_third | HnRpr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = p /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr_third |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnN.
        exists t, q, p, r, s.
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; exact Hupr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_upr. }
    (* (g) third edge = (s, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=t, d=s. Edges a<c, b<c, d<a, d<c. iso r. *)
    destruct (classic (R2 s p)) as [HRsp_third | HnRsp_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [exact HRsp_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HniVcol.
        exists p, t, q, s, r.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsp_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (h) third edge = (r, p): inv-V chain on one bottom (HniVcol)
       with a=p, c=q, b=t, d=r. iso s. *)
    destruct (classic (R2 r p)) as [HRrp_third | HnRrp_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp_third HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HniVcol.
        exists p, t, q, r, s.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrp_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (i) third edge = (q, s): Y-down at s (HnYdn) with a=s, b=q,
       c=p, d=t. R2 c b, R2 d b, R2 b a, R2 c a, R2 d a. iso r. *)
    destruct (classic (R2 q s)) as [HRqs_third | HnRqs_third].
    { assert (HRps_via : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs_third).
      assert (HRts_via : R2 t s) by exact (HR2.(poset_trans) t q s HRxy HRqs_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = q /\ b = s) /\ ~ (a = p /\ b = s) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists s, q, p, t, r.
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqs_third |].
        split; [exact HRps_via |].
        split; [exact HRts_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (j) third edge = (q, r): Y-down at r (HnYdn), iso s. *)
    destruct (classic (R2 q r)) as [HRqr_third | HnRqr_third].
    { assert (HRpr_via : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr_third).
      assert (HRtr_via : R2 t r) by exact (HR2.(poset_trans) t q r HRxy HRqr_third).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = q /\ b = r) /\ ~ (a = p /\ b = r) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr_third |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYdn.
        exists r, q, p, t, s.
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqr_third |].
        split; [exact HRpr_via |].
        split; [exact HRtr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (k) third edge = (s, q): 3-claw-down (HnClawDn) with
       a=p, b=t, c=s, d=q (R2 a d, R2 b d, R2 c d). iso r. *)
    destruct (classic (R2 s q)) as [HRsq_third | HnRsq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact HRsq_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnClawDn.
        exists p, t, s, q, r.
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hqr_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_usq. }
    (* (l) third edge = (r, q): 3-claw-down, iso s. *)
    destruct (classic (R2 r q)) as [HRrq_third | HnRrq_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnClawDn.
        exists p, t, r, q, s.
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hqs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_urq. }
    (* (m) third edge = (t, s): N-shape (a→b, c→b, c→d) with
       a=p, b=q, c=t, d=s. iso r. *)
    destruct (classic (R2 t s)) as [HRts_third | HnRts_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; exact Huts |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (n) third edge = (t, r): N-shape, iso s. *)
    destruct (classic (R2 t r)) as [HRtr_third | HnRtr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_third |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnN.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; exact Hutr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (o) third edge = (s, t): inv-V chain (HniVcol) with
       a=t, c=q, b=p, d=s (a<c, b<c, d<a, d<c). iso r. *)
    destruct (classic (R2 s t)) as [HRst_third | HnRst_third].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s t q HRst_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = s /\ b = t) /\ ~ (a = s /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [exact HRst_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HniVcol.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRst_third |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_ust |]. exact Hnot_usq. }
    (* (p) third edge = (r, t): inv-V chain (HniVcol), iso s. *)
    destruct (classic (R2 r t)) as [HRrt_third | HnRrt_third].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r t q HRrt_third HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = r /\ b = t) /\ ~ (a = r /\ b = q)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact HRrt_third |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HniVcol.
        exists t, p, q, r, s.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrt_third |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |].
        split; [exact Hnot_urt |]. exact Hnot_urq. }
    (* (q) third edge = (s, r): inv-V + disjoint chain (HninvVc) with
       a=p, b=t, c=q, d=s, e=r (R2 a c, R2 b c, R2 d e). *)
    destruct (classic (R2 s r)) as [HRsr_third | HnRsr_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_third |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HninvVc.
        exists p, t, q, s, r.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsr_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; exact Husr |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_usr. }
    (* (r) third edge = (r, s): inv-V + disjoint chain (HninvVc) with
       a=p, b=t, c=q, d=r, e=s. *)
    destruct (classic (R2 r s)) as [HRrs_third | HnRrs_third].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfourth | Hno_fourth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs_third |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HninvVc.
        exists p, t, q, r, s.
        split; [exact Hpt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrs_third |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; exact Hurs |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utq |]. exact Hnot_urs. }
    (* All 18 possible 3rd-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hthird as [a [b [Hab_neq [HRab [Hnot_ab_pq Hnot_ab_tq]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_tq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRpt_third; exact HRab
        | apply HnRtp_third; exact HRab
        | apply HnRps_third; exact HRab
        | apply HnRpr_third; exact HRab
        | apply HnRsp_third; exact HRab
        | apply HnRrp_third; exact HRab
        | apply HnRqs_third; exact HRab
        | apply HnRqr_third; exact HRab
        | apply HnRsq_third; exact HRab
        | apply HnRrq_third; exact HRab
        | apply HnRts_third; exact HRab
        | apply HnRtr_third; exact HRab
        | apply HnRst_third; exact HRab
        | apply HnRrt_third; exact HRab
        | apply HnRsr_third; exact HRab
        | apply HnRrs_third; exact HRab ].
  - exfalso. apply HninvV.
    exists p, t, q, s, r.
    split; [exact Hpt_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
      [right; exact Hutq |].
    exfalso. apply Hno_third.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |]. exact Hnot_utq.
Qed.

(** Micro-case (xiv) of the second-edge cascade inside the residual handler:
    second edge is [(q, r)] — by transitivity [R2 p r] holds, so the carrier
    contains the 3-chain [p < q < r] plus isolated [s], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xiv :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 q r)
    (Hnot_pq : ~ (q = p /\ r = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRpr : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
            ~ (a = p /\ b = r)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (s, p): 4-chain s<p<q<r + iso t (HnC4). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists s, p, q, r, t.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_new |].
        split; [exact HRsr_new |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (b) fourth edge = (t, p): 4-chain t<p<q<r + iso s (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists t, p, q, r, s.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_new |].
        split; [exact HRtr_new |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (c) fourth edge = (r, s): 4-chain p<q<r<s + iso t (HnC4). *)
    destruct (classic (R2 r s)) as [HRrs_fourth | HnRrs_fourth].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p r s HRpr HRrs_fourth).
      assert (HRqs_new : R2 q s) by exact (HR2.(poset_trans) q r s HRxy HRrs_fourth).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = r /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_fourth |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrs_fourth |].
        split; [exact HRpr |].
        split; [exact HRps_new |].
        split; [exact HRqs_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; right; right; right; exact Huqs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (d) fourth edge = (r, t): 4-chain p<q<r<t + iso s (HnC4). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p r t HRpr HRrt).
      assert (HRqt_new : R2 q t) by exact (HR2.(poset_trans) q r t HRxy HRrt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = r /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt |].
        split; [exact HRpr |].
        split; [exact HRpt_new |].
        split; [exact HRqt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; right; right; right; exact Huqt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_urt |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (e) fourth edge = (q, s): 5-edge Y-up shape with apex p, branch
       q->{r,s} (HnYup). Note: positioned before (g) (p,s) so that when
       edge = (q,s), transitive p<s is also true but we route here first. *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqs |].
        split; [exact HRpr |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (f) fourth edge = (q, t): Y-up apex p, branch q->{r,t} (HnYup). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt |].
        split; [exact HRpr |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (g) fourth edge = (s, q): Y-down apex r, q has parents p,s (HnYdn). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRsr_new : R2 s r) by exact (HR2.(poset_trans) s q r HRsq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists r, q, p, s, t.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRsr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (h) fourth edge = (t, q): Y-down apex r, q has parents p,t (HnYdn). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { assert (HRtr_new : R2 t r) by exact (HR2.(poset_trans) t q r HRtq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists r, q, p, t, s.
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
        split; [exact Hrs_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRtr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |].
        split; [exact Hnot_utq |]. exact Hnot_utr. }
    (* (i) fourth edge = (s, r): 3-chain p<q<r + top pendant s<r + iso t
       (HnTopP). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; symmetry; exact Hrs_eq |].
        split; [exact HRsr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsr |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (j) fourth edge = (t, r): 3-chain p<q<r + top pendant t<r + iso s
       (HnTopP). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_utr. }
    (* (k) fourth edge = (p, s): pendant from chain bottom (HnPd):
       3-chain p<q<r + pendant p<s + iso t. *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = p /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnPd.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_ups. }
    (* (l) fourth edge = (p, t): pendant from chain bottom (HnPd). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = p /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRpr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_upt. }
    (* (m) fourth edge = (s, t): 3-chain p<q<r + disjoint 2-chain s<t (HnCC). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists p, q, r, s, t.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRst |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_ust. }
    (* (n) fourth edge = (t, s): 3-chain p<q<r + disjoint 2-chain t<s (HnCC). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists p, q, r, t, s.
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRts |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; left; exact Huqr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_uts. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (r, q) — antisymmetry contradiction. *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { exfalso. apply Hqr_neq.
      exact (HR2.(poset_antisym) q r HRxy HRrq). }
    (* (q) fourth edge = (r, p) — antisymmetry contradiction. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { exfalso. apply Hpr_neq.
      exact (HR2.(poset_antisym) p r HRpr HRrp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qr Hnot_ab_pr]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qr; split; reflexivity
        | apply Hnot_ab_pr; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRst; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRts; exact HRab ].
  - exfalso. apply HnChain3.
    exists p, q, r, s, t.
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    split; [exact HRpr |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
      [right; left; exact Hupr |].
    destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
      [right; right; exact Huqr |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_uqr |]. exact Hnot_upr.
Qed.

(** Micro-case (xv) of the second-edge cascade inside the residual handler:
    second edge is [(q, s)] — by transitivity [R2 p s] holds, so the carrier
    contains the 3-chain [p < q < s] plus isolated [r], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xv :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 q s)
    (Hnot_pq : ~ (q = p /\ s = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRps : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
            ~ (a = p /\ b = s)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (r, p): 4-chain r<p<q<s + iso t (HnC4). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r q s HRrq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        split; [exact HRrs_new |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (b) fourth edge = (t, p): 4-chain t<p<q<s + iso r (HnC4). *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t q s HRtq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists t, p, q, s, r.
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtq_new |].
        split; [exact HRts_new |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; left; exact Hutq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utp |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (c) fourth edge = (s, r): 4-chain p<q<s<r + iso t (HnC4). *)
    destruct (classic (R2 s r)) as [HRsr_fourth | HnRsr_fourth].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p s r HRps HRsr_fourth).
      assert (HRqr_new : R2 q r) by exact (HR2.(poset_trans) q s r HRxy HRsr_fourth).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = s /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr_fourth |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsr_fourth |].
        split; [exact HRps |].
        split; [exact HRpr_new |].
        split; [exact HRqr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; right; right; right; exact Huqr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_usr |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) fourth edge = (s, t): 4-chain p<q<s<t + iso r (HnC4). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p s t HRps HRst).
      assert (HRqt_new : R2 q t) by exact (HR2.(poset_trans) q s t HRxy HRst).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = s /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hrp _]; apply Hps_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        split; [exact HRqt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; left; exact Hupt |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; right; right; right; exact Huqt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_ust |].
        split; [exact Hnot_upt |]. exact Hnot_uqt. }
    (* (e) fourth edge = (q, r): 5-edge Y-up shape with apex p, branch
       q->{s,r} (HnYup). Note: positioned before (k) (p,r) so that when
       edge = (q,r), transitive p<r is also true but we route here first. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqr |].
        split; [exact HRps |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (f) fourth edge = (q, t): Y-up apex p, branch q->{s,t} (HnYup). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqt |].
        split; [exact HRps |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_uqt |]. exact Hnot_upt. }
    (* (g) fourth edge = (r, q): Y-down apex s, q has parents p,r (HnYdn). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r q s HRrq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists s, q, p, r, t.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRrs_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (h) fourth edge = (t, q): Y-down apex s, q has parents p,t (HnYdn). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { assert (HRts_new : R2 t s) by exact (HR2.(poset_trans) t q s HRtq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = q) /\
                ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists s, q, p, t, r.
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; exact Hqt_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRts_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |].
        split; [exact Hnot_utq |]. exact Hnot_uts. }
    (* (i) fourth edge = (r, s): 3-chain p<q<s + top pendant r<s + iso t
       (HnTopP). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrs |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (j) fourth edge = (t, s): 3-chain p<q<s + top pendant t<s + iso r
       (HnTopP). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts |].
        intros [_ Hrq]; apply Hqs_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_uts. }
    (* (k) fourth edge = (p, r): pendant from chain bottom (HnPd):
       3-chain p<q<s + pendant p<r + iso t. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
      - exfalso. apply HnPd.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_upr. }
    (* (l) fourth edge = (p, t): pendant from chain bottom (HnPd). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = p /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRps |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_upt. }
    (* (m) fourth edge = (r, t): 3-chain p<q<s + disjoint 2-chain r<t (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists p, q, s, r, t.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRrt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urt. }
    (* (n) fourth edge = (t, r): 3-chain p<q<s + disjoint 2-chain t<r (HnCC). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists p, q, s, t, r.
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRtr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; left; exact Huqs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_utr. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (s, q) — antisymmetry contradiction. *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRxy HRsq). }
    (* (q) fourth edge = (s, p) — antisymmetry contradiction. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRps HRsp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qs Hnot_ab_ps]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qs; split; reflexivity
        | apply Hnot_ab_ps; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRsr_fourth; exact HRab
        | apply HnRst; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRts; exact HRab
        | apply HnRtr; exact HRab ].
  - exfalso. apply HnChain3.
    exists p, q, s, r, t.
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hst_neq |].
    split; [exact Hrt_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    split; [exact HRps |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
      [right; left; exact Hups |].
    destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
      [right; right; exact Huqs |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_uqs |]. exact Hnot_ups.
Qed.

(** Micro-case (xvi) of the second-edge cascade inside the residual handler:
    second edge is [(q, t)] — by transitivity [R2 p t] holds, so the carrier
    contains the 3-chain [p < q < t] plus isolated [r], [s].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xvi :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 q t)
    (Hnot_pq : ~ (q = p /\ t = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRpt : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRxy).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
            ~ (a = p /\ b = t)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (r, p): 4-chain r<p<q<t + iso s (HnC4). *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r q t HRrq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [exact HRrp |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrq_new |].
        split; [exact HRrt_new |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    (* (b) fourth edge = (s, p): 4-chain s<p<q<t + iso r (HnC4). *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      assert (HRst_new : R2 s t) by exact (HR2.(poset_trans) s q t HRsq_new HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists s, p, q, t, r.
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRsq_new |].
        split; [exact HRst_new |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (c) fourth edge = (t, r): 4-chain p<q<t<r + iso s (HnC4). *)
    destruct (classic (R2 t r)) as [HRtr_fourth | HnRtr_fourth].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p t r HRpt HRtr_fourth).
      assert (HRqr_new : R2 q r) by exact (HR2.(poset_trans) q t r HRxy HRtr_fourth).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = t /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = q /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr_fourth |].
        intros [Hrp _]; apply Hpt_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRtr_fourth |].
        split; [exact HRpt |].
        split; [exact HRpr_new |].
        split; [exact HRqr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; left; exact Hutr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; left; exact Hupr |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; right; right; right; exact Huqr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_upr |]. exact Hnot_uqr. }
    (* (d) fourth edge = (t, s): 4-chain p<q<t<s + iso r (HnC4). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p t s HRpt HRts).
      assert (HRqs_new : R2 q s) by exact (HR2.(poset_trans) q t s HRxy HRts).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = t /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = q /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Hrp _]; apply Hpt_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRts |].
        split; [exact HRpt |].
        split; [exact HRps_new |].
        split; [exact HRqs_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; left; exact Huts |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; left; exact Hups |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; right; right; right; exact Huqs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_ups |]. exact Hnot_uqs. }
    (* (e) fourth edge = (q, r): 5-edge Y-up shape with apex p, branch
       q->{t,r} (HnYup). Note: positioned before (k) (p,r) so that when
       edge = (q,r), transitive p<r is also true but we route here first. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRpr_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqr |].
        split; [exact HRpt |].
        split; [exact HRpr_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqr |]. exact Hnot_upr. }
    (* (f) fourth edge = (q, s): Y-up apex p, branch q->{t,s} (HnYup). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnYup.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRqs |].
        split; [exact HRpt |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_uqs |]. exact Hnot_ups. }
    (* (g) fourth edge = (r, q): Y-down apex t, q has parents p,r (HnYdn). *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r q t HRrq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = q) /\
                ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact HRrq |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists t, q, p, r, s.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; exact Hqr_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRrt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; left; exact Hurq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    (* (h) fourth edge = (s, q): Y-down apex t, q has parents p,s (HnYdn). *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { assert (HRst_new : R2 s t) by exact (HR2.(poset_trans) s q t HRsq HRxy).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = q) /\
                ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists t, q, p, s, r.
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; exact Hqs_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRst_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; left; exact Husq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (i) fourth edge = (r, t): 3-chain p<q<t + top pendant r<t + iso s
       (HnTopP). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [_ Hrq]; apply Hqt_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRrt |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    (* (j) fourth edge = (s, t): 3-chain p<q<t + top pendant s<t + iso r
       (HnTopP). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [_ Hrq]; apply Hqt_neq; symmetry; exact Hrq.
      - exfalso. apply HnTopP.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRst |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (k) fourth edge = (p, r): pendant from chain bottom (HnPd):
       3-chain p<q<t + pendant p<r + iso s. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hsq]; apply Hqr_neq; symmetry; exact Hsq.
      - exfalso. apply HnPd.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpr |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_upr. }
    (* (l) fourth edge = (p, s): pendant from chain bottom (HnPd). *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = p /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Htq]; apply Hqs_neq; symmetry; exact Htq.
      - exfalso. apply HnPd.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRps |].
        split; [exact HRpt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ups. }
    (* (m) fourth edge = (r, s): 3-chain p<q<t + disjoint 2-chain r<s (HnCC). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs |].
        intros [Hsp _]; apply Hpr_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists p, q, t, r, s.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact Hrs_neq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRrs |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; exact Hurs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urs. }
    (* (n) fourth edge = (s, r): 3-chain p<q<t + disjoint 2-chain s<r (HnCC). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr |].
        intros [Htp _]; apply Hps_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists p, q, t, s, r.
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRpq |].
        split; [exact HRxy |].
        split; [exact HRpt |].
        split; [exact HRsr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; left; exact Huqt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_usr. }
    (* (o) fourth edge = (q, p) — antisymmetry contradiction. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (p) fourth edge = (t, q) — antisymmetry contradiction. *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { exfalso. apply Hqt_neq.
      exact (HR2.(poset_antisym) q t HRxy HRtq). }
    (* (q) fourth edge = (t, p) — antisymmetry contradiction. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { exfalso. apply Hpt_neq.
      exact (HR2.(poset_antisym) p t HRpt HRtp). }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_qt Hnot_ab_pt]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_qt; split; reflexivity
        | apply Hnot_ab_pt; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRps; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRtr_fourth; exact HRab
        | apply HnRts; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRst; exact HRab
        | apply HnRsr; exact HRab ].
  - exfalso. apply HnChain3.
    exists p, q, t, r, s.
    split; [exact Hpq_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hps_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqs_neq |].
    split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
    split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
    split; [exact Hrs_neq |].
    split; [exact HRpq |].
    split; [exact HRxy |].
    split; [exact HRpt |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [left; exact Hupq |].
    destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
      [right; left; exact Hupt |].
    destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
      [right; right; exact Huqt |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_uqt |]. exact Hnot_upt.
Qed.

(** Micro-case (xvii) of the second-edge cascade inside the residual handler:
    second edge is [(r, p)] — by transitivity [R2 r q] holds, so the carrier
    admits the 3-chain [r < p < q] plus isolated [s], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xvii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 r p)
    (Hnot_pq : ~ (r = p /\ p = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRrq : R2 r q) by exact (HR2.(poset_trans) r p q HRxy HRpq).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
            ~ (a = r /\ b = q)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) fourth edge = (p, r) — antisymmetry with HRxy : R2 r p. *)
    destruct (classic (R2 p r)) as [HRpr_fourth | HnRpr_fourth].
    { exfalso. apply Hpr_neq.
      exact (HR2.(poset_antisym) p r HRpr_fourth HRxy). }
    (* (c) fourth edge = (q, r) — antisymmetry with HRrq : R2 r q. *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { exfalso. apply Hqr_neq.
      exact (HR2.(poset_antisym) q r HRqr HRrq). }
    (* (d) fourth edge = (s, r): 4-chain s<r<p<q + iso t (HnC4). *)
    destruct (classic (R2 s r)) as [HRsr | HnRsr].
    { assert (HRsp_new : R2 s p) by exact (HR2.(poset_trans) s r p HRsr HRxy).
      assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = r) /\
                ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRsr |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnC4.
        exists s, r, p, q, t.
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact Hst_neq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRsr |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsp_new |].
        split; [exact HRsq_new |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [left; exact Husr |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; right; right; left; exact Husp |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usr |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (e) fourth edge = (t, r): 4-chain t<r<p<q + iso s (HnC4). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { assert (HRtp_new : R2 t p) by exact (HR2.(poset_trans) t r p HRtr HRxy).
      assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = r) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists t, r, p, q, s.
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqs_neq |].
        split; [exact HRtr |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [left; exact Hutr |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utr |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (f) fourth edge = (q, s): 4-chain r<p<q<s + iso t (HnC4). *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
      assert (HRrs_new : R2 r s) by exact (HR2.(poset_trans) r p s HRxy HRps_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = q /\ b = s) /\
                ~ (a = p /\ b = s) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqs_neq |].
        split; [exact HRqs |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqs |].
        split; [exact HRrq |].
        split; [exact HRrs_new |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
          [right; right; left; exact Huqs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; left; exact Hurs |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; right; right; right; exact Hups |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqs |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (g) fourth edge = (q, t): 4-chain r<p<q<t + iso s (HnC4). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      assert (HRrt_new : R2 r t) by exact (HR2.(poset_trans) r p t HRxy HRpt_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRrq |].
        split; [exact HRrt_new |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; left; exact Hurt |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    (* (h) fourth edge = (r, s): 3-chain r<p<q + pendant r<s + iso t
       (HnPd) with a=r, b=p, c=q, d=s. *)
    destruct (classic (R2 r s)) as [HRrs_fourth | HnRrs_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrs_neq |].
        split; [exact HRrs_fourth |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_fourth |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; left; exact Hurs |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urs. }
    (* (i) fourth edge = (r, t): 3-chain r<p<q + pendant r<t + iso s
       (HnPd) with a=r, b=p, c=q, d=t. *)
    destruct (classic (R2 r t)) as [HRrt_fourth | HnRrt_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt_fourth |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnPd.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrt_fourth |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; left; exact Hurt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_urt. }
    (* (j) fourth edge = (p, s): Y-up apex r, branch p->{q,s} (HnYup)
       with a=r, b=p, c=q, d=s. *)
    destruct (classic (R2 p s)) as [HRps | HnRps].
    { assert (HRrs_via : R2 r s) by exact (HR2.(poset_trans) r p s HRxy HRps).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = p /\ b = s) /\
                ~ (a = r /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hps_neq |].
        split; [exact HRps |].
        intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
      - exfalso. apply HnYup.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRps |].
        split; [exact HRrq |].
        split; [exact HRrs_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
          [right; right; left; exact Hups |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [right; right; right; right; exact Hurs |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_ups |]. exact Hnot_urs. }
    (* (k) fourth edge = (p, t): Y-up apex r, branch p->{q,t} (HnYup). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { assert (HRrt_via : R2 r t) by exact (HR2.(poset_trans) r p t HRxy HRpt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnYup.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt |].
        split; [exact HRrq |].
        split; [exact HRrt_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_upt |]. exact Hnot_urt. }
    (* (l) fourth edge = (s, p): Y-down apex q, p has parents r,s
       (HnYdn) with a=q, b=p, c=r, d=s. *)
    destruct (classic (R2 s p)) as [HRsp | HnRsp].
    { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsp_eq; apply Hps_neq; symmetry; exact Hsp_eq |].
        split; [exact HRsp |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnYdn.
        exists q, p, r, s, t.
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRsp |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRsq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_usp |]. exact Hnot_usq. }
    (* (m) fourth edge = (t, p): Y-down apex q, p has parents r,t
       (HnYdn) with a=q, b=p, c=r, d=t. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htp_eq; apply Hpt_neq; symmetry; exact Htp_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists q, p, r, t, s.
        split; [intro Hqp_eq; apply Hpq_neq; symmetry; exact Hqp_eq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (n) fourth edge = (s, q): 3-chain r<p<q + top pendant s<q + iso t
       (HnTopP) with a=r, b=p, c=q, d=s. *)
    destruct (classic (R2 s q)) as [HRsq | HnRsq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsq_eq; apply Hqs_neq; symmetry; exact Hsq_eq |].
        split; [exact HRsq |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnTopP.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_usq. }
    (* (o) fourth edge = (t, q): 3-chain r<p<q + top pendant t<q + iso s
       (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Htq_eq; apply Hqt_neq; symmetry; exact Htq_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRrq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_utq. }
    (* (p) fourth edge = (s, t): 3-chain r<p<q + disjoint chain s<t
       (HnCC). *)
    destruct (classic (R2 s t)) as [HRst | HnRst].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRst |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnCC.
        exists r, p, q, s, t.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrs_neq |].
        split; [exact Hrt_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hst_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRst |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_ust. }
    (* (q) fourth edge = (t, s): 3-chain r<p<q + disjoint chain t<s
       (HnCC). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q) /\ ~ (a = t /\ b = s)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists r, p, q, t, s.
        split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
        split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
        split; [exact Hrt_neq |].
        split; [exact Hrs_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqs_neq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRts |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [right; right; right; exact Huts |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_urp |].
        split; [exact Hnot_urq |]. exact Hnot_uts. }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_rp Hnot_ab_rq]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_rp; split; reflexivity
        | apply Hnot_ab_rq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr_fourth; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRsr; exact HRab
        | apply HnRtr; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt_fourth; exact HRab
        | apply HnRps; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRsp; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRsq; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRst; exact HRab
        | apply HnRts; exact HRab ].
  - exfalso. apply HnChain3.
    exists r, p, q, s, t.
    split; [intro Hrp_eq; apply Hpr_neq; symmetry; exact Hrp_eq |].
    split; [intro Hrq_eq; apply Hqr_neq; symmetry; exact Hrq_eq |].
    split; [exact Hrs_neq |].
    split; [exact Hrt_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hps_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqs_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hst_neq |].
    split; [exact HRxy |].
    split; [exact HRpq |].
    split; [exact HRrq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
      [left; exact Hurp |].
    destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
      [right; left; exact Hurq |].
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [right; right; exact Hupq |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_urp |]. exact Hnot_urq.
Qed.

(** Micro-case (xviii) of the second-edge cascade inside the residual handler:
    second edge is [(s, p)] — by transitivity [R2 s q] holds, so the carrier
    admits the 3-chain [s < p < q] plus isolated [r], [t].  If no fourth
    strict edge exists, this contradicts [HnChain3].  Otherwise the
    fourth-edge expansion peels off each well-defined labeling and routes
    to the matching upstream per-class shape lemma. *)
Lemma n5_dispatcher_microcase_xviii :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}
    (Hcard : cardinal B (Full_set B) 5)
    (Hnonantichain : ~ (forall a b : B, R2 a b -> a = b))
    (Hinc_ex : exists a b : B, @Incomparable B R2 a b)
    (p q r s t : B)
    (Hpq_neq : p <> q) (Hpr_neq : p <> r) (Hps_neq : p <> s)
    (Hpt_neq : p <> t) (Hqr_neq : q <> r) (Hqs_neq : q <> s)
    (Hqt_neq : q <> t) (Hrs_neq : r <> s) (Hrt_neq : r <> t)
    (Hst_neq : s <> t)
    (Hcov5 : forall x : B, x = p \/ x = q \/ x = r \/ x = s \/ x = t)
    (HRpq : R2 p q)
    (HRxy : R2 s p)
    (Hnot_pq : ~ (s = p /\ p = q))
    (HnChain3 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    (HnCC :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
                (x = d /\ y = e)))))
    (HnC4 :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 c d /\
            R2 a c /\ R2 a d /\ R2 b d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
                (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    (HnPd :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnTopP :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = d /\ y = c) \/ (x = a /\ y = c)))))
    (HnYup :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = a /\ y = b) \/ (x = b /\ y = c) \/
                (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    (HnYdn :
       ~ (exists a b c d e : B,
            a <> b /\ a <> c /\ a <> d /\ a <> e /\
            b <> c /\ b <> d /\ b <> e /\
            c <> d /\ c <> e /\
            d <> e /\
            R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
            (forall x y : B,
               R2 x y -> x = y \/
               ((x = c /\ y = b) \/ (x = d /\ y = b) \/
                (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a))))),
  exists r' : Ensemble (B -> B -> Prop),
    IsRealizer R2 r' /\ cardinal (B -> B -> Prop) r' 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex p q r s t
         Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
         Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
         HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn.
  assert (HRsq : R2 s q) by exact (HR2.(poset_trans) s p q HRxy HRpq).
  destruct (classic (exists a b : B,
            a <> b /\ R2 a b /\
            ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
            ~ (a = s /\ b = q)))
    as [Hfourth | Hno_fourth].
  - (* A fourth strict edge exists. Peel off well-defined 4th-edge
       labelings and route to upstream per-class shapes; fall through
       to the focused admit only for residuals (none remain). *)
    (* (a) fourth edge = (q, p) — antisymmetry. *)
    destruct (classic (R2 q p)) as [HRqp | HnRqp].
    { exfalso. apply Hpq_neq.
      exact (HR2.(poset_antisym) p q HRpq HRqp). }
    (* (b) fourth edge = (p, s) — antisymmetry with HRxy : R2 s p. *)
    destruct (classic (R2 p s)) as [HRpr_fourth | HnRpr_fourth].
    { exfalso. apply Hps_neq.
      exact (HR2.(poset_antisym) p s HRpr_fourth HRxy). }
    (* (c) fourth edge = (q, s) — antisymmetry with HRsq : R2 s q. *)
    destruct (classic (R2 q s)) as [HRqs | HnRqs].
    { exfalso. apply Hqs_neq.
      exact (HR2.(poset_antisym) q s HRqs HRsq). }
    (* (d) fourth edge = (r, s): 4-chain r<s<p<q + iso t (HnC4). *)
    destruct (classic (R2 r s)) as [HRrs | HnRrs].
    { assert (HRsp_new : R2 r p) by exact (HR2.(poset_trans) r s p HRrs HRxy).
      assert (HRsq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRsp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = s) /\
                ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [exact HRrs |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnC4.
        exists r, s, p, q, t.
        split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact Hrt_neq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqt_neq |].
        split; [exact HRrs |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsp_new |].
        split; [exact HRsq_new |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
          [left; exact Hurs |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; right; right; left; exact Hurp |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urs |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (e) fourth edge = (t, s): 4-chain t<s<p<q + iso r (HnC4). *)
    destruct (classic (R2 t s)) as [HRts | HnRts].
    { assert (HRtp_new : R2 t p) by exact (HR2.(poset_trans) t s p HRts HRxy).
      assert (HRtq_new : R2 t q) by exact (HR2.(poset_trans) t p q HRtp_new HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = s) /\
                ~ (a = t /\ b = p) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, s.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [exact HRts |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnC4.
        exists t, s, p, q, r.
        split; [intro Hst_eq; apply Hst_neq; symmetry; exact Hst_eq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqr_neq |].
        split; [exact HRts |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtp_new |].
        split; [exact HRtq_new |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
          [left; exact Huts |].
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [right; left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; right; right; left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uts |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (f) fourth edge = (q, r): 4-chain s<p<q<r + iso t (HnC4). *)
    destruct (classic (R2 q r)) as [HRqr | HnRqr].
    { assert (HRps_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
      assert (HRrs_new : R2 s r) by exact (HR2.(poset_trans) s p r HRxy HRps_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = q /\ b = r) /\
                ~ (a = p /\ b = r) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqr_neq |].
        split; [exact HRqr |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqr |].
        split; [exact HRsq |].
        split; [exact HRrs_new |].
        split; [exact HRps_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
          [right; right; left; exact Huqr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; left; exact Husr |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; right; right; right; exact Hupr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqr |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (g) fourth edge = (q, t): 4-chain s<p<q<t + iso r (HnC4). *)
    destruct (classic (R2 q t)) as [HRqt | HnRqt].
    { assert (HRpt_new : R2 p t) by exact (HR2.(poset_trans) p q t HRpq HRqt).
      assert (HRrt_new : R2 s t) by exact (HR2.(poset_trans) s p t HRxy HRpt_new).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = q /\ b = t) /\
                ~ (a = p /\ b = t) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, q, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hqt_neq |].
        split; [exact HRqt |].
        intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
      - exfalso. apply HnC4.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRqt |].
        split; [exact HRsq |].
        split; [exact HRrt_new |].
        split; [exact HRpt_new |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = q /\ v = t)) as [Huqt | Hnot_uqt];
          [right; right; left; exact Huqt |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; left; exact Hust |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; right; right; right; exact Hupt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_uqt |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (h) fourth edge = (s, r): 3-chain s<p<q + pendant s<r + iso t
       (HnPd) with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 s r)) as [HRrs_fourth | HnRrs_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRrs_fourth |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrs_fourth |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; left; exact Husr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_usr. }
    (* (i) fourth edge = (s, t): 3-chain s<p<q + pendant s<t + iso r
       (HnPd) with a=s, b=p, c=q, d=t. *)
    destruct (classic (R2 s t)) as [HRrt_fourth | HnRrt_fourth].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, s, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hst_neq |].
        split; [exact HRrt_fourth |].
        intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
      - exfalso. apply HnPd.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrt_fourth |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; left; exact Hust |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_ust. }
    (* (j) fourth edge = (p, r): Y-up apex s, branch p->{q,r} (HnYup)
       with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 p r)) as [HRpr | HnRpr].
    { assert (HRsr_via : R2 s r) by exact (HR2.(poset_trans) s p r HRxy HRpr).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = p /\ b = r) /\
                ~ (a = s /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpr_neq |].
        split; [exact HRpr |].
        intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
      - exfalso. apply HnYup.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpr |].
        split; [exact HRsq |].
        split; [exact HRsr_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
          [right; right; left; exact Hupr |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
          [right; right; right; right; exact Husr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_upr |]. exact Hnot_usr. }
    (* (k) fourth edge = (p, t): Y-up apex s, branch p->{q,t} (HnYup). *)
    destruct (classic (R2 p t)) as [HRpt | HnRpt].
    { assert (HRst_via : R2 s t) by exact (HR2.(poset_trans) s p t HRxy HRpt).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = p /\ b = t) /\
                ~ (a = s /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, p, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hpt_neq |].
        split; [exact HRpt |].
        intros [_ Htq]; apply Hqt_neq; symmetry; exact Htq.
      - exfalso. apply HnYup.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRpt |].
        split; [exact HRsq |].
        split; [exact HRst_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = p /\ v = t)) as [Hupt | Hnot_upt];
          [right; right; left; exact Hupt |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
          [right; right; right; right; exact Hust |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_upt |]. exact Hnot_ust. }
    (* (l) fourth edge = (r, p): Y-down apex q, p has parents s,r
       (HnYdn) with a=q, b=p, c=s, d=r. *)
    destruct (classic (R2 r p)) as [HRrp | HnRrp].
    { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = p) /\
                ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
        split; [exact HRrp |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnYdn.
        exists q, p, s, r, t.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRrp |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
          [right; left; exact Hurp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; right; right; exact Hurq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_urp |]. exact Hnot_urq. }
    (* (m) fourth edge = (t, p): Y-down apex q, p has parents s,t
       (HnYdn) with a=q, b=p, c=s, d=t. *)
    destruct (classic (R2 t p)) as [HRtp | HnRtp].
    { assert (HRtq_via : R2 t q) by exact (HR2.(poset_trans) t p q HRtp HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, p.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [exact HRtp |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnYdn.
        exists q, p, s, t, r.
        split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
        split; [exact Hqs_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRtp |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRtq_via |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [right; left; exact Hutp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; right; right; exact Hutq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* (n) fourth edge = (r, q): 3-chain s<p<q + top pendant r<q + iso t
       (HnTopP) with a=s, b=p, c=q, d=r. *)
    destruct (classic (R2 r q)) as [HRrq | HnRrq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
        split; [exact HRrq |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnTopP.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRrq |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
          [right; right; left; exact Hurq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_urq. }
    (* (o) fourth edge = (t, q): 3-chain s<p<q + top pendant t<q + iso r
       (HnTopP). *)
    destruct (classic (R2 t q)) as [HRtq | HnRtq].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = q)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, q.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [exact HRtq |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnTopP.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        split; [exact HRsq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; right; left; exact Hutq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; right; exact Husq |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utq. }
    (* (p) fourth edge = (r, t): 3-chain s<p<q + disjoint chain r<t
       (HnCC). *)
    destruct (classic (R2 r t)) as [HRrt | HnRrt].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = r /\ b = t)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, r, t.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [exact Hrt_neq |].
        split; [exact HRrt |].
        intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
      - exfalso. apply HnCC.
        exists s, p, q, r, t.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hst_neq |].
        split; [exact Hpq_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hqr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hrt_neq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRrt |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
          [right; right; right; exact Hurt |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_urt. }
    (* (q) fourth edge = (t, r): 3-chain s<p<q + disjoint chain t<r
       (HnCC). *)
    destruct (classic (R2 t r)) as [HRtr | HnRtr].
    { destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = s /\ b = p) /\
                ~ (a = s /\ b = q) /\ ~ (a = t /\ b = r)))
        as [Hfifth | Hno_fifth].
      - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                 Hnonantichain Hinc_ex).
        exists p, q, t, r.
        split; [exact Hpq_neq |].
        split; [exact HRpq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRtr |].
        intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
      - exfalso. apply HnCC.
        exists s, p, q, t, r.
        split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
        split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
        split; [exact Hst_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hpt_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqt_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hrt_eq; apply Hrt_neq; symmetry; exact Hrt_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRsq |].
        split; [exact HRtr |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
          [left; exact Husp |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; left; exact Hupq |].
        destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
          [right; right; left; exact Husq |].
        destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
          [right; right; right; exact Hutr |].
        exfalso. apply Hno_fifth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_usp |].
        split; [exact Hnot_usq |]. exact Hnot_utr. }
    (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
    exfalso.
    destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_sp Hnot_ab_sq]]]]]].
    destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
      destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
      subst a b;
      first
        [ apply Hab_neq; reflexivity
        | apply Hnot_ab_pq; split; reflexivity
        | apply Hnot_ab_sp; split; reflexivity
        | apply Hnot_ab_sq; split; reflexivity
        | apply HnRqp; exact HRab
        | apply HnRpr_fourth; exact HRab
        | apply HnRqs; exact HRab
        | apply HnRrs; exact HRab
        | apply HnRts; exact HRab
        | apply HnRqr; exact HRab
        | apply HnRqt; exact HRab
        | apply HnRrs_fourth; exact HRab
        | apply HnRrt_fourth; exact HRab
        | apply HnRpr; exact HRab
        | apply HnRpt; exact HRab
        | apply HnRrp; exact HRab
        | apply HnRtp; exact HRab
        | apply HnRrq; exact HRab
        | apply HnRtq; exact HRab
        | apply HnRrt; exact HRab
        | apply HnRtr; exact HRab ].
  - exfalso. apply HnChain3.
    exists s, p, q, r, t.
    split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
    split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
    split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
    split; [exact Hst_neq |].
    split; [exact Hpq_neq |].
    split; [exact Hpr_neq |].
    split; [exact Hpt_neq |].
    split; [exact Hqr_neq |].
    split; [exact Hqt_neq |].
    split; [exact Hrt_neq |].
    split; [exact HRxy |].
    split; [exact HRpq |].
    split; [exact HRsq |].
    intros u v HRuv.
    destruct (classic (u = v)) as [Heq | Huv_neq];
      [left; exact Heq |].
    right.
    destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
      [left; exact Husp |].
    destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
      [right; left; exact Husq |].
    destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
      [right; right; exact Hupq |].
    exfalso. apply Hno_fourth.
    exists u, v. split; [exact Huv_neq |].
    split; [exact HRuv |].
    split; [exact Hnot_upq |].
    split; [exact Hnot_usp |]. exact Hnot_usq.
Qed.

Lemma n5_nonantichain_nonchain_two_realizer :
  forall {B : Type} (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2},
  cardinal B (Full_set B) 5 ->
  ~ (forall a b : B, R2 a b -> a = b) ->
  (exists a b : B, @Incomparable B R2 a b) ->
  exists r : Ensemble (B -> B -> Prop),
    IsRealizer R2 r /\ cardinal (B -> B -> Prop) r 2.
Proof.
  intros B R2 HR2 Hcard Hnonantichain Hinc_ex.
  (* Extract a strict edge (p, q). *)
  assert (Hedge : exists p q : B, p <> q /\ R2 p q).
  { apply Classical_Pred_Type.not_all_ex_not in Hnonantichain.
    destruct Hnonantichain as [p Hp].
    apply Classical_Pred_Type.not_all_ex_not in Hp.
    destruct Hp as [q Hq].
    exists p, q.
    split;
      [ intro Heq; apply Hq; intros HRpq_unused; exact Heq
      | destruct (classic (R2 p q)) as [HR | HnR];
          [ exact HR
          | exfalso; apply Hq; intro Hcontra; contradiction ]
      ]. }
  destruct Hedge as [p [q [Hpq_neq HRpq]]].
  (* Cascade: try each Qed-routed per-class shape, then fall through. *)
  (* (b) chain3+2isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c)))))
    as [HChain3 | HnChain3].
  { apply (@n5_chain3_plus_2isolated_two_realizer B R2 HR2 Hcard).
    exact HChain3. }
  (* (e) disjoint-chains+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c d /\
       (forall x y : B,
          R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = c /\ y = d))))
    as [HDisj | HnDisj].
  { apply (@n5_disjoint_chains_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HDisj. }
  (* (c) V+2isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\
       (forall x y : B,
          R2 x y -> x = y \/ (x = a /\ y = b) \/ (x = a /\ y = c))))
    as [HV | HnV].
  { apply (@n5_V_plus_2isolated_two_realizer B R2 HR2 Hcard).
    exact HV. }
  (* (d) inv-V+2isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\
       (forall x y : B,
          R2 x y -> x = y \/ (x = a /\ y = c) \/ (x = b /\ y = c))))
    as [HinvV | HninvV].
  { apply (@n5_inv_V_plus_2isolated_two_realizer B R2 HR2 Hcard).
    exact HinvV. }
  (* (f) N+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d)))))
    as [HN | HnN].
  { apply (@n5_N_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HN. }
  (* (g) 3claw-up+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    as [HClawUp | HnClawUp].
  { apply (@n5_3claw_up_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HClawUp. }
  (* (h) 3claw-down+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a d /\ R2 b d /\ R2 c d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d)))))
    as [HClawDn | HnClawDn].
  { apply (@n5_3claw_down_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HClawDn. }
  (* (i) disjoint chain3+chain2. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/
           (x = a /\ y = c) \/ (x = d /\ y = e)))))
    as [HCC | HnCC].
  { apply (@n5_disjoint_chain3_chain2_two_realizer B R2 HR2 Hcard).
    exact HCC. }
  (* (j) V+chain. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = e)))))
    as [HVc | HnVc].
  { apply (@n5_V_plus_chain_two_realizer B R2 HR2 Hcard).
    exact HVc. }
  (* (k) inv-V+chain. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = e)))))
    as [HinvVc | HninvVc].
  { apply (@n5_inv_V_plus_chain_two_realizer B R2 HR2 Hcard).
    exact HinvVc. }
  (* (l) 4-chain+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d)))))
    as [HC4 | HnC4].
  { apply (@n5_chain4_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HC4. }
  (* (m) bowtie+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d)))))
    as [HBt | HnBt].
  { apply (@n5_bowtie_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HBt. }
  (* (n) diamond+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = a /\ y = d)))))
    as [HDm | HnDm].
  { apply (@n5_diamond_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HDm. }
  (* (o) pendant (3-chain + pendant edge)+isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a d /\ R2 a c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/
           (x = a /\ y = d) \/ (x = a /\ y = c)))))
    as [HPd | HnPd].
  { apply (@n5_pendant_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HPd. }
  (* (p) N+pendant (N-shape extended by d<e edge). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 d e /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/
           (x = c /\ y = d) \/ (x = d /\ y = e) \/ (x = c /\ y = e)))))
    as [HNp | HnNp].
  { apply (@n5_N_plus_pendant_two_realizer B R2 HR2 Hcard).
    exact HNp. }
  (* (q) 3claw-up+pendant. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 d e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = a /\ y = d) \/ (x = d /\ y = e) \/ (x = a /\ y = e)))))
    as [HCup | HnCup].
  { apply (@n5_3claw_up_pendant_two_realizer B R2 HR2 Hcard).
    exact HCup. }
  (* (r) 3claw-down+pendant. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 c a /\ R2 d a /\ R2 e d /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = c /\ y = a) \/
           (x = d /\ y = a) \/ (x = e /\ y = d) \/ (x = e /\ y = a)))))
    as [HCdn | HnCdn].
  { apply (@n5_3claw_down_pendant_two_realizer B R2 HR2 Hcard).
    exact HCdn. }
  (* (s) Y-up + isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/
           (x = b /\ y = d) \/ (x = a /\ y = c) \/ (x = a /\ y = d)))))
    as [HYup | HnYup].
  { apply (@n5_Y_up_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HYup. }
  (* (t) 5-fence / W-shape. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/
           (x = c /\ y = d) \/ (x = e /\ y = d)))))
    as [HFen | HnFen].
  { apply (@n5_fence_two_realizer B R2 HR2 Hcard).
    exact HFen. }
  (* (u) Y-down + isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = b) \/ (x = d /\ y = b) \/
           (x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a)))))
    as [HYdn | HnYdn].
  { destruct HYdn as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRcb [HRdb [HRba [HRca [HRda HR_only]]]]]]]]]]]]]]]]]]]].
    apply (@n5_Y_down_plus_isolated_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (v) M-shape (dual of fence). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/
           (x = d /\ y = c) \/ (x = d /\ y = e)))))
    as [HM | HnM].
  { apply (@n5_M_shape_two_realizer B R2 HR2 Hcard).
    exact HM. }
  (* (w) 4-claw-up (single bottom, four tops). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = a /\ y = d) \/ (x = a /\ y = e)))))
    as [H4Up | Hn4Up].
  { apply (@n5_4claw_up_two_realizer B R2 HR2 Hcard).
    exact H4Up. }
  (* (x) 4-claw-down (four bottoms, single top). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 c a /\ R2 d a /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = c /\ y = a) \/
           (x = d /\ y = a) \/ (x = e /\ y = a)))))
    as [H4Dn | Hn4Dn].
  { apply (@n5_4claw_down_two_realizer B R2 HR2 Hcard).
    exact H4Dn. }
  (* (y) inv-N+isolated (dual of N, Z-shape). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c)))))
    as [HinvN | HninvN].
  { apply (@n5_inv_N_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HinvN. }
  (* (z) chain3 + V at top (nine edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 c d /\ R2 c e /\
       R2 a d /\ R2 a e /\ R2 b d /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = c /\ y = d) \/ (x = c /\ y = e) \/
           (x = a /\ y = d) \/ (x = a /\ y = e) \/
           (x = b /\ y = d) \/ (x = b /\ y = e)))))
    as [HCVt | HnCVt].
  { destruct HCVt as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRac [HRcd [HRce
       [HRad [HRae [HRbd [HRbe HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_chain3_plus_V_top_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (aa) chain3 + inv-V at bottom (dual of (z), nine edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d a /\ R2 e a /\
       R2 d b /\ R2 d c /\ R2 e b /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = a) \/ (x = e /\ y = a) \/
           (x = d /\ y = b) \/ (x = d /\ y = c) \/
           (x = e /\ y = b) \/ (x = e /\ y = c)))))
    as [HCVb | HnCVb].
  { destruct HCVb as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRac [HRda [HRea
       [HRdb [HRdc [HReb [HRec HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_chain3_plus_inv_V_bottom_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (bb) diamond with pendant above top (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 d e /\
       R2 a e /\ R2 b e /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = a /\ y = d) \/
           (x = d /\ y = e) \/
           (x = a /\ y = e) \/ (x = b /\ y = e) \/ (x = c /\ y = e)))))
    as [HDpa | HnDpa].
  { destruct HDpa as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRac [HRbd [HRcd [HRad [HRde
       [HRae [HRbe [HRce HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_diamond_pendant_above_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (cc) diamond with pendant below bottom (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 e a /\
       R2 e b /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = a /\ y = d) \/
           (x = e /\ y = a) \/
           (x = e /\ y = b) \/ (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HDpb | HnDpb].
  { destruct HDpb as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRac [HRbd [HRcd [HRad [HRea
       [HReb [HRec [HRed HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_diamond_pendant_below_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (dd) bowtie + pendant above one top (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\ R2 c e /\
       R2 a e /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = c /\ y = e) \/
           (x = a /\ y = e) \/ (x = b /\ y = e)))))
    as [HBpu | HnBpu].
  { destruct HBpu as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRac [HRad [HRbc [HRbd [HRce
       [HRae [HRbe HR_only]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_bowtie_pendant_up_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (ee) bowtie + pendant below one bottom (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\ R2 e a /\
       R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = e /\ y = a) \/
           (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HBpd | HnBpd].
  { destruct HBpd as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRac [HRad [HRbc [HRbd [HRea
       [HRec [HRed HR_only]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_bowtie_pendant_down_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (ff) chain3 + top pendant + isolated (dual of pendant_plus_isolated). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 d c /\ R2 a c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/
           (x = d /\ y = c) \/ (x = a /\ y = c)))))
    as [HTopP | HnTopP].
  { apply (@n5_chain3_top_pendant_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HTopP. }
  (* (gg) inv-V with pendant above the apex (6 edges, e isolated). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\ R2 c d /\ R2 a d /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = d) \/ (x = b /\ y = d)))))
    as [HIVpt | HnIVpt].
  { apply (@n5_inv_V_pendant_top_two_realizer B R2 HR2 Hcard).
    exact HIVpt. }
  (* (hh) V with pendant below the common bottom (5 edges, e isolated). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 d a /\ R2 d b /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
           (x = d /\ y = b) \/ (x = d /\ y = c)))))
    as [HVpb | HnVpb].
  { apply (@n5_V_pendant_bot_two_realizer B R2 HR2 Hcard).
    exact HVpb. }
  (* (ii) 4-chain extended with a pendant below the top (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = e /\ y = d)))))
    as [HC4tp | HnC4tp].
  { destruct HC4tp as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRcd [HRac [HRad [HRbd [HRed HR_only]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_chain4_top_pendant_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (jj) 4-chain extended with a pendant above the bottom (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = a /\ y = e)))))
    as [HC4bp | HnC4bp].
  { destruct HC4bp as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRcd [HRac [HRad [HRbd [HRae HR_only]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_chain4_bot_pendant_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (kk) Y-down with pendant below one branch (8 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
       R2 e c /\ R2 e b /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = b) \/ (x = d /\ y = b) \/ (x = b /\ y = a) \/
           (x = c /\ y = a) \/ (x = d /\ y = a) \/
           (x = e /\ y = c) \/ (x = e /\ y = b) \/ (x = e /\ y = a)))))
    as [HYdp | HnYdp].
  { destruct HYdp as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRcb [HRdb [HRba [HRca [HRda
       [HRec [HReb [HRea HR_only]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_Y_down_pendant_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (ll) Y-up with pendant below the base (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
       R2 e a /\ R2 e b /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = e /\ y = a) \/ (x = e /\ y = b) \/ (x = e /\ y = c) \/
           (x = e /\ y = d)))))
    as [HYupb | HnYupb].
  { destruct HYupb as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRbd [HRac [HRad
       [HRea [HReb [HRec [HRed HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_Y_up_pendant_below_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (mm) Y-up with pendant above one branch (8 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 b d /\ R2 a c /\ R2 a d /\
       R2 c e /\ R2 b e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = c /\ y = e) \/ (x = b /\ y = e) \/ (x = a /\ y = e)))))
    as [HYupa | HnYupa].
  { destruct HYupa as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRbd [HRac [HRad
       [HRce [HRbe [HRae HR_only]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_Y_up_pendant_above_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (nn) T-shape extended with pendant below branch tip (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 b d /\ R2 a d /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = a /\ y = d) \/ (x = e /\ y = d)))))
    as [HTSe | HnTSe].
  { destruct HTSe as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRbc [HRac [HRbd [HRad [HRed HR_only]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_T_shape_extended_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (oo) 3-claw-up with chain growing from one leaf (5 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 c e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = c /\ y = e) \/ (x = a /\ y = e)))))
    as [HCupL | HnCupL].
  { destruct HCupL as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRab [HRac [HRad [HRce [HRae HR_only]]]]]]]]]]]]]]]]]]]].
    apply (@n5_3claw_up_chain_in_leaf_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (pp) 3-claw-down with chain growing from one leaf (5 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 c a /\ R2 d a /\ R2 e c /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a) \/
           (x = e /\ y = c) \/ (x = e /\ y = a)))))
    as [HCdnL | HnCdnL].
  { destruct HCdnL as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRba [HRca [HRda [HRec [HRea HR_only]]]]]]]]]]]]]]]]]]]].
    apply (@n5_3claw_down_chain_in_leaf_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (qq) X-shape / hourglass (8 transitive edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\ R2 c d /\ R2 c e /\
       R2 a d /\ R2 a e /\ R2 b d /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = b /\ y = c) \/
           (x = c /\ y = d) \/ (x = c /\ y = e) \/
           (x = a /\ y = d) \/ (x = a /\ y = e) \/
           (x = b /\ y = d) \/ (x = b /\ y = e)))))
    as [HX | HnX].
  { destruct HX as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRac [HRbc [HRcd [HRce [HRad [HRae [HRbd [HRbe HR_only]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_X_shape_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (rr) Bowtie with top chain edge + isolated (5 edges, e isolated). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\ R2 c d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = c /\ y = d)))))
    as [HBtc | HnBtc].
  { apply (@n5_bowtie_top_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HBtc. }
  (* (ss) Bowtie with bottom chain edge + isolated (5 edges, e isolated). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d)))))
    as [HBbc | HnBbc].
  { apply (@n5_bowtie_bot_chain_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HBbc. }
  (* (tt) 4-chain with pendant below the third element (8 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
       R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HC4pmt | HnC4pmt].
  { apply (@n5_chain4_pendant_below_third_two_realizer B R2 HR2 Hcard).
    exact HC4pmt. }
  (* (uu) 4-chain with pendant above the second element (8 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
       R2 b e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = b /\ y = e) \/ (x = a /\ y = e)))))
    as [HC4pmb | HnC4pmb].
  { apply (@n5_chain4_pendant_above_second_two_realizer B R2 HR2 Hcard).
    exact HC4pmb. }
  (* (vv) 3-chain with pendant below the middle + isolated (5 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d b /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = b) \/ (x = d /\ y = c)))))
    as [HC3pm | HnC3pm].
  { apply (@n5_chain3_pendant_middle_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HC3pm. }
  (* (ww) Diamond with pendant below an intermediate node (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 e b /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = a /\ y = d) \/
           (x = e /\ y = b) \/ (x = e /\ y = d)))))
    as [HDpib | HnDpib].
  { apply (@n5_diamond_pendant_intermediate_below_two_realizer B R2 HR2 Hcard).
    exact HDpib. }
  (* (xx) Diamond with pendant above an intermediate node (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 b e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = a /\ y = d) \/
           (x = b /\ y = e) \/ (x = a /\ y = e)))))
    as [HDpia | HnDpia].
  { apply (@n5_diamond_pendant_intermediate_above_two_realizer B R2 HR2 Hcard).
    exact HDpia. }
  (* (yy) Two 3-chains sharing top element (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d e /\ R2 e c /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = e) \/ (x = e /\ y = c) \/ (x = d /\ y = c)))))
    as [HCST | HnCST].
  { apply (@n5_3chain_chain_share_top_two_realizer B R2 HR2 Hcard).
    exact HCST. }
  (* (zz) Two 3-chains sharing bottom element (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\ R2 d e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = a /\ y = d) \/ (x = d /\ y = e) \/ (x = a /\ y = e)))))
    as [HCSB | HnCSB].
  { apply (@n5_3chain_chain_share_bot_two_realizer B R2 HR2 Hcard).
    exact HCSB. }
  (* (aaa) 3-chain with pendant above the middle + isolated (5 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 b e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = b /\ y = e) \/ (x = a /\ y = e)))))
    as [HC3pam | HnC3pam].
  { apply (@n5_chain3_pendant_above_middle_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HC3pam. }
  (* (bbb) 4-chain with pendant above the third element (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
       R2 c e /\ R2 a e /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = c /\ y = e) \/ (x = a /\ y = e) \/ (x = b /\ y = e)))))
    as [HC4pat | HnC4pat].
  { apply (@n5_chain4_pendant_above_third_two_realizer B R2 HR2 Hcard).
    exact HC4pat. }
  (* (ccc) 4-chain with pendant below the second element (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 c d /\ R2 a c /\ R2 a d /\ R2 b d /\
       R2 e b /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = e /\ y = b) \/ (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HC4pbs | HnC4pbs].
  { apply (@n5_chain4_pendant_below_second_two_realizer B R2 HR2 Hcard).
    exact HC4pbs. }
  (* (ddd) V-shape with chain extending below the apex (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 d a /\ R2 e d /\
       R2 d b /\ R2 d c /\ R2 e a /\ R2 e b /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = d /\ y = a) \/
           (x = e /\ y = d) \/ (x = d /\ y = b) \/ (x = d /\ y = c) \/
           (x = e /\ y = a) \/ (x = e /\ y = b) \/ (x = e /\ y = c)))))
    as [HVcb | HnVcb].
  { apply (@n5_V_with_chain_below_apex_two_realizer B R2 HR2 Hcard).
    exact HVcb. }
  (* (eee) inv-V-shape with chain extending above the apex (9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\ R2 c d /\ R2 d e /\
       R2 a d /\ R2 b d /\ R2 a e /\ R2 b e /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = c /\ y = d) \/
           (x = d /\ y = e) \/ (x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = a /\ y = e) \/ (x = b /\ y = e) \/ (x = c /\ y = e)))))
    as [HiVca | HniVca].
  { apply (@n5_inv_V_with_chain_above_apex_two_realizer B R2 HR2 Hcard).
    exact HiVca. }
  (* (fff) Two 3-chains sharing the middle element (8 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d b /\ R2 b e /\ R2 d e /\
       R2 a e /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = b) \/ (x = b /\ y = e) \/ (x = d /\ y = e) \/
           (x = a /\ y = e) \/ (x = d /\ y = c)))))
    as [HCSM | HnCSM].
  { apply (@n5_two_3chains_share_middle_two_realizer B R2 HR2 Hcard).
    exact HCSM. }
  (* (ggg) 3-claw-up with two leaves sharing a common top (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 b e /\ R2 c e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = e) \/ (x = c /\ y = e) \/ (x = a /\ y = e)))))
    as [HCLST | HnCLST].
  { apply (@n5_3claw_up_two_leaves_share_top_two_realizer B R2 HR2 Hcard).
    exact HCLST. }
  (* (hhh) 3-claw-down with two leaves sharing a common bottom (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a d /\ R2 b d /\ R2 c d /\ R2 e b /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = d) \/ (x = b /\ y = d) \/ (x = c /\ y = d) \/
           (x = e /\ y = b) \/ (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HCLSB | HnCLSB].
  { apply (@n5_3claw_down_two_leaves_share_bot_two_realizer B R2 HR2 Hcard).
    exact HCLSB. }
  (* (iii) 3-chain + top pendant with chain extending the pendant below
     (6 edges): a<b<c plus d<c plus e<d. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d c /\ R2 e d /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = c) \/ (x = e /\ y = d) \/ (x = e /\ y = c)))))
    as [HTPCB | HnTPCB].
  { apply (@n5_chain3_top_pendant_with_chain_below_two_realizer B R2 HR2 Hcard).
    exact HTPCB. }
  (* (jjj) 3-chain + bot pendant with chain extending the pendant above
     (6 edges): a<b<c plus a<d plus d<e. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 a d /\ R2 d e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = a /\ y = d) \/ (x = d /\ y = e) \/ (x = a /\ y = e)))))
    as [HBPCA | HnBPCA].
  { apply (@n5_chain3_bot_pendant_with_chain_above_two_realizer B R2 HR2 Hcard).
    exact HBPCA. }
  (* (kkk) Inverse T-shape extended: chain [c<b<a] + branch [d<b,d<a]
     + pendant [d<e] (6 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c b /\ R2 b a /\ R2 c a /\ R2 d b /\ R2 d a /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = b) \/ (x = b /\ y = a) \/ (x = c /\ y = a) \/
           (x = d /\ y = b) \/ (x = d /\ y = a) \/ (x = d /\ y = e)))))
    as [HInvT | HnInvT].
  { apply (@n5_inv_T_shape_extended_two_realizer B R2 HR2 Hcard).
    exact HInvT. }
  (* (lll) Chain [a<b] with a 3-claw at the top: b<c, b<d, b<e
     (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 b d /\ R2 b e /\
       R2 a c /\ R2 a d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = b /\ y = e) \/
           (x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = a /\ y = e)))))
    as [HC23CT | HnC23CT].
  { apply (@n5_chain2_plus_3claw_top_two_realizer B R2 HR2 Hcard).
    exact HC23CT. }
  (* (mmm) 3-claw at the bottom with a 2-chain on top: c<a, d<a, e<a,
     and a<b (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c a /\ R2 d a /\ R2 e a /\ R2 a b /\
       R2 c b /\ R2 d b /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = a) \/ (x = d /\ y = a) \/ (x = e /\ y = a) \/
           (x = a /\ y = b) \/
           (x = c /\ y = b) \/ (x = d /\ y = b) \/ (x = e /\ y = b)))))
    as [HC23CB | HnC23CB].
  { apply (@n5_chain2_plus_3claw_bot_two_realizer B R2 HR2 Hcard).
    exact HC23CB. }
  (* (nnn) 3-claw-up with chain extending below the apex: a<b, a<c, a<d,
     e<a, plus transitively e<b, e<c, e<d (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 e a /\
       R2 e b /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = e /\ y = a) \/
           (x = e /\ y = b) \/ (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HCUCB | HnCUCB].
  { apply (@n5_3claw_up_chain_below_apex_two_realizer B R2 HR2 Hcard).
    exact HCUCB. }
  (* (ooo) 3-claw-down with chain extending above the apex: b<a, c<a, d<a,
     a<e, plus transitively b<e, c<e, d<e (7 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 c a /\ R2 d a /\ R2 a e /\
       R2 b e /\ R2 c e /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a) \/
           (x = a /\ y = e) \/
           (x = b /\ y = e) \/ (x = c /\ y = e) \/ (x = d /\ y = e)))))
    as [HCDCA | HnCDCA].
  { apply (@n5_3claw_down_chain_above_apex_two_realizer B R2 HR2 Hcard).
    exact HCDCA. }
  (* (ppp) N-shape with bottom extension: a<b, c<b, c<d, e<a (plus
     transitively e<b) (5 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 e a /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = e /\ y = a) \/ (x = e /\ y = b)))))
    as [HNBE | HnNBE].
  { apply (@n5_N_plus_bottom_extension_two_realizer B R2 HR2 Hcard).
    exact HNBE. }
  (* (qqq) N-shape + top pendant on left chain: a<b, c<b, c<d, a<e
     (4 edges, e above a only). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = a /\ y = e)))))
    as [HNTPL | HnNTPL].
  { apply (@n5_N_plus_top_pendant_on_left_two_realizer B R2 HR2 Hcard).
    exact HNTPL. }
  (* (rrr) 3-claw-up at apex [c] with extra pendant at one leaf: c<b,
     c<d, c<e, a<b (4 edges, a below leaf b only). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = c /\ y = e)))))
    as [HClawL | HnClawL].
  { apply (@n5_3claw_up_pendant_at_one_leaf_two_realizer B R2 HR2 Hcard).
    exact HClawL. }
  (* (www) Complete bipartite K_{3,2} (two bottoms, three tops):
     c<a, c<b, c<d, e<a, e<b, e<d (6 edges, no transitives).  Dual of (vvv). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c a /\ R2 c b /\ R2 c d /\ R2 e a /\ R2 e b /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = a) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = e /\ y = a) \/ (x = e /\ y = b) \/ (x = e /\ y = d)))))
    as [HK32 | HnK32].
  { apply (@n5_K_3_2_two_realizer B R2 HR2 Hcard).
    exact HK32. }
  (* (vvv) Complete bipartite K_{2,3} (two tops, three bottoms):
     c<a, c<b, d<a, d<b, e<a, e<b (6 edges, no transitives). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c a /\ R2 c b /\ R2 d a /\ R2 d b /\ R2 e a /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = a) \/ (x = c /\ y = b) \/
           (x = d /\ y = a) \/ (x = d /\ y = b) \/
           (x = e /\ y = a) \/ (x = e /\ y = b)))))
    as [HK23 | HnK23].
  { apply (@n5_K_2_3_two_realizer B R2 HR2 Hcard).
    exact HK23. }
  (* (uuu) 3-claw-up at [b] with extra parent [d] at one child [c]:
     b<a, b<c, b<e, d<c (4 edges, no transitives).  Dual of (ttt). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 b e /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = b /\ y = e) \/
           (x = d /\ y = c)))))
    as [HCUXP | HnCUXP].
  { apply (@n5_3claw_up_extra_parent_two_realizer B R2 HR2 Hcard).
    exact HCUXP. }
  (* (ttt) 3-claw-down at [b] with extra child [d] at one parent [c]:
     a<b, c<b, e<b, c<d (4 edges, no transitives). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 e b /\ R2 c d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = e /\ y = b) \/
           (x = c /\ y = d)))))
    as [HCDXL | HnCDXL].
  { apply (@n5_3claw_down_extra_leaf_two_realizer B R2 HR2 Hcard).
    exact HCDXL. }
  (* (p-d) inv-N + pendant (extended by e<d): b<a, b<c, d<c, e<d
     (plus transitively e<c) (5 edges).  Dual of (p). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 e d /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/
           (x = d /\ y = c) \/ (x = e /\ y = d) \/ (x = e /\ y = c)))))
    as [HInvNp | HnInvNp].
  { apply (@n5_inv_N_plus_pendant_two_realizer B R2 HR2 Hcard).
    exact HInvNp. }
  (* (ll-d) Y-down with pendant above the top (9 edges).  Dual of (ll). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c b /\ R2 d b /\ R2 b a /\ R2 c a /\ R2 d a /\
       R2 a e /\ R2 b e /\ R2 c e /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = b) \/ (x = d /\ y = b) \/ (x = b /\ y = a) \/
           (x = c /\ y = a) \/ (x = d /\ y = a) \/
           (x = a /\ y = e) \/ (x = b /\ y = e) \/ (x = c /\ y = e) \/
           (x = d /\ y = e)))))
    as [HYdpa | HnYdpa].
  { destruct HYdpa as [a [b [c [d [e [Hab_neq [Hac_neq [Had_neq [Hae_neq
       [Hbc_neq [Hbd_neq [Hbe_neq
       [Hcd_neq [Hce_neq
       [Hde_neq
       [HRcb [HRdb [HRba [HRca [HRda
       [HRae [HRbe [HRce [HRde HR_only]]]]]]]]]]]]]]]]]]]]]]]].
    apply (@n5_Y_down_pendant_above_two_realizer B R2 HR2 Hcard).
    exists a, b, c, d, e.
    repeat split; assumption. }
  (* (ppp-d) inv-N + top-extension on one chain: b<a, b<c, d<c, a<e
     (plus transitively b<e) (5 edges).  Dual of (ppp). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 a e /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = a /\ y = e) \/ (x = b /\ y = e)))))
    as [HInvNTE | HnInvNTE].
  { apply (@n5_inv_N_plus_top_extension_two_realizer B R2 HR2 Hcard).
    exact HInvNTE. }
  (* (rrr-d) 3-claw-down at apex [c] with extra pendant at one leaf:
     b<c, d<c, e<c, b<a (4 edges, a above leaf b only).  Dual of (rrr). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = e /\ y = c)))))
    as [HClawLD | HnClawLD].
  { apply (@n5_3claw_down_pendant_at_one_leaf_two_realizer B R2 HR2 Hcard).
    exact HClawLD. }
  (* (sss) inv-N + bot-pendant on left chain: b<a, b<c, d<c, e<a
     (4 edges, e below a only).  Dual of (qqq). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = e /\ y = a)))))
    as [HInvNBPL | HnInvNBPL].
  { apply (@n5_inv_N_plus_bot_pendant_on_left_two_realizer B R2 HR2 Hcard).
    exact HInvNBPL. }
  (* (ttt) N + top-pendant on right chain: a<b, c<b, c<d, d<e, c<e
     (5 edges, e above d).  Dual of (sss). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 d e /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = d /\ y = e) \/ (x = c /\ y = e)))))
    as [HNTPR | HnNTPR].
  { apply (@n5_N_plus_top_pendant_on_right_two_realizer B R2 HR2 Hcard).
    exact HNTPR. }
  (* (vvv) N + bot-pendant on right (c-fork) chain: a<b, c<b, c<d, e<c,
     e<b, e<d (6 edges, e below c). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 e c /\ R2 e b /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = e /\ y = c) \/ (x = e /\ y = b) \/ (x = e /\ y = d)))))
    as [HNBPR | HnNBPR].
  { apply (@n5_N_plus_bot_pendant_on_right_two_realizer B R2 HR2 Hcard).
    exact HNBPR. }
  (* (www) inv-N + top-pendant on right (c-fork) chain: b<a, b<c, d<c,
     c<e, b<e, d<e (6 edges, e above c).  Dual of (vvv). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 c e /\ R2 b e /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = c /\ y = e) \/ (x = b /\ y = e) \/ (x = d /\ y = e)))))
    as [HInvNTPR | HnInvNTPR].
  { apply (@n5_inv_N_plus_top_pendant_on_right_two_realizer B R2 HR2 Hcard).
    exact HInvNTPR. }
  (* (www.1) N + bot-pendant on left (a-chain) chain: a<b, c<b, c<d, e<a,
     e<b (5 edges, e below a). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 c b /\ R2 c d /\ R2 e a /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = c /\ y = b) \/ (x = c /\ y = d) \/
           (x = e /\ y = a) \/ (x = e /\ y = b)))))
    as [HNBPL | HnNBPL].
  { apply (@n5_N_plus_bot_pendant_on_left_two_realizer B R2 HR2 Hcard).
    exact HNBPL. }
  (* (www.2) inv-N + top-pendant on left chain: b<a, b<c, d<c, a<e, b<e
     (5 edges, e above a).  Dual of (www.1). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 a e /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = a /\ y = e) \/ (x = b /\ y = e)))))
    as [HInvNTPL | HnInvNTPL].
  { apply (@n5_inv_N_plus_top_pendant_on_left_two_realizer B R2 HR2 Hcard).
    exact HInvNTPL. }
  (* (www.3) inv-N + bot-pendant on right (d-chain) chain: b<a, b<c, d<c,
     e<d, e<c (5 edges, e below d). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 b c /\ R2 d c /\ R2 e d /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = b /\ y = c) \/ (x = d /\ y = c) \/
           (x = e /\ y = d) \/ (x = e /\ y = c)))))
    as [HInvNBPR | HnInvNBPR].
  { apply (@n5_inv_N_plus_bot_pendant_on_right_two_realizer B R2 HR2 Hcard).
    exact HInvNBPR. }
  (* (xxx) 3-fan: a<b, a<c, a<e, b<d, c<d, e<d, a<d (7 edges); common
     min [a], common max [d], three pairwise-incomparable middle
     [b], [c], [e].  Self-dual under swap [a <-> d]. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a e /\ R2 b d /\ R2 c d /\ R2 e d /\ R2 a d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = e) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/ (x = e /\ y = d) \/
           (x = a /\ y = d)))))
    as [H3fan | Hn3fan].
  { apply (@n5_3fan_two_realizer B R2 HR2 Hcard).
    exact H3fan. }
  (* (yyy) Pentagon N_5: min [a], top [e], length-2 chain [a<d<e] on one
     side, length-3 chain [a<b<c<e] on the other. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 a e /\
       R2 b c /\ R2 b e /\ R2 c e /\ R2 d e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = a /\ y = e) \/ (x = b /\ y = c) \/ (x = b /\ y = e) \/
           (x = c /\ y = e) \/ (x = d /\ y = e)))))
    as [HPent | HnPent].
  { apply (@n5_pentagon_two_realizer B R2 HR2 Hcard).
    exact HPent. }
  (* (zzz) Kite: apex [a] below three children [b], [c], [d]; [b]
     additionally below [e]; transitively [a < e].  5 edges. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 b e /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = e) \/ (x = a /\ y = e)))))
    as [HKite | HnKite].
  { apply (@n5_kite_two_realizer B R2 HR2 Hcard).
    exact HKite. }
  (* (aaaa) Inverse kite: apex [a] above three parents [b], [c], [d]; [e]
     additionally below [b]; transitively [e < a].  Dual of kite.  5
     edges. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 b a /\ R2 c a /\ R2 d a /\ R2 e b /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = b /\ y = a) \/ (x = c /\ y = a) \/ (x = d /\ y = a) \/
           (x = e /\ y = b) \/ (x = e /\ y = a)))))
    as [HInvKite | HnInvKite].
  { apply (@n5_inv_kite_two_realizer B R2 HR2 Hcard).
    exact HInvKite. }
  (* (bbbb) 3-layer diamond: bottom [a], middle pair [b], [c], top pair
     [d], [e]; both [b], [c] below both [d], [e]; 8 edges (6 covers +
     2 transitive). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 b e /\ R2 c e /\
       R2 a d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/
           (x = b /\ y = e) \/ (x = c /\ y = e) \/
           (x = a /\ y = d) \/ (x = a /\ y = e)))))
    as [H3Layer | Hn3Layer].
  { apply (@n5_3_layer_diamond_two_realizer B R2 HR2 Hcard).
    exact H3Layer. }
  (* (cccc) Bowtie + top cap: 2 bottoms [a], [b], 2 middle [c], [d], top [e];
     bowtie on [{a, b}, {c, d}] plus [c<e], [d<e] (with transitive
     [a<e], [b<e]).  8 edges. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 b c /\ R2 b d /\ R2 c e /\ R2 d e /\
       R2 a e /\ R2 b e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = b /\ y = d) \/
           (x = c /\ y = e) \/ (x = d /\ y = e) \/
           (x = a /\ y = e) \/ (x = b /\ y = e)))))
    as [HBtc' | HnBtc'].
  { apply (@n5_bowtie_top_cap_two_realizer B R2 HR2 Hcard).
    exact HBtc'. }
  (* (dddd) Bowtie + bottom cap (dual of cccc): common bottom [e],
     2 middle [c], [d], 2 tops [a], [b]; bowtie on [{c, d}, {a, b}] plus
     [e<c], [e<d] (with transitive [e<a], [e<b]).  8 edges. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 e c /\ R2 e d /\ R2 c a /\ R2 c b /\ R2 d a /\ R2 d b /\
       R2 e a /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = e /\ y = c) \/ (x = e /\ y = d) \/
           (x = c /\ y = a) \/ (x = c /\ y = b) \/
           (x = d /\ y = a) \/ (x = d /\ y = b) \/
           (x = e /\ y = a) \/ (x = e /\ y = b)))))
    as [HBbc' | HnBbc'].
  { apply (@n5_bowtie_bot_cap_two_realizer B R2 HR2 Hcard).
    exact HBbc'. }
  (* (eeee) V-shape with chain extending one leaf, plus isolated:
     a<b, a<c, b<d, a<d (4 edges); e isolated. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 a d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = d) \/
           (x = a /\ y = d)))))
    as [HVcol | HnVcol].
  { apply (@n5_V_chain_one_leaf_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HVcol. }
  (* (ffff) inv-V-shape with chain extending one bottom, plus isolated:
     a<c, b<c, d<a, d<c (4 edges); e isolated.  Dual of (eeee). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 b c /\ R2 d a /\ R2 d c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = b /\ y = c) \/ (x = d /\ y = a) \/
           (x = d /\ y = c)))))
    as [HiVcol | HniVcol].
  { apply (@n5_inv_V_chain_one_leaf_plus_isolated_two_realizer B R2 HR2 Hcard).
    exact HiVcol. }
  (* (gggg) Diamond with pendant below the top only (no transitives to
     diamond intermediates/bottom): a<b, a<c, b<d, c<d, a<d, e<d (6
     edges).  Distinct from [n5_diamond_pendant_below] (which routes
     [e<a] with full transitive closure, 9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/
           (x = a /\ y = d) \/ (x = e /\ y = d)))))
    as [HDpt | HnDpt].
  { apply (@n5_diamond_pendant_top_only_two_realizer B R2 HR2 Hcard).
    exact HDpt. }
  (* (hhhh) Diamond with pendant above the bottom only (no transitives to
     diamond intermediates/top): a<b, a<c, b<d, c<d, a<d, a<e (6 edges).
     Dual of (gggg).  Distinct from [n5_diamond_pendant_above] (which
     routes [d<e] with full transitive closure, 9 edges). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b d /\ R2 c d /\ R2 a d /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/
           (x = b /\ y = d) \/ (x = c /\ y = d) \/
           (x = a /\ y = d) \/ (x = a /\ y = e)))))
    as [HDpbo | HnDpbo].
  { apply (@n5_diamond_pendant_bot_only_two_realizer B R2 HR2 Hcard).
    exact HDpbo. }
  (* (iiii) K_{2,3} minus one edge: 5 edges
     [c < a], [c < b], [d < a], [d < b], [e < a] (the edge [e < b] of
     K_{2,3} is dropped).  Equivalently bowtie K_{2,2} on
     {a, b, c, d} plus half-pendant [e < a]. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c a /\ R2 c b /\ R2 d a /\ R2 d b /\ R2 e a /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = a) \/ (x = c /\ y = b) \/
           (x = d /\ y = a) \/ (x = d /\ y = b) \/
           (x = e /\ y = a)))))
    as [HK23m | HnK23m].
  { apply (@n5_K_2_3_minus_edge_two_realizer B R2 HR2 Hcard).
    exact HK23m. }
  (* (jjjj) K_{3,2} minus one edge: dual of (iiii).  5 edges
     [a < c], [a < d], [a < e], [b < c], [b < d] (the edge [b < e] of
     K_{3,2} is dropped).  Equivalently bowtie K_{2,2} on
     {a, b, c, d} plus half-pendant [a < e]. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a c /\ R2 a d /\ R2 a e /\ R2 b c /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = c) \/ (x = a /\ y = d) \/ (x = a /\ y = e) \/
           (x = b /\ y = c) \/ (x = b /\ y = d)))))
    as [HK32m | HnK32m].
  { apply (@n5_K_3_2_minus_edge_two_realizer B R2 HR2 Hcard).
    exact HK32m. }
  (* (kkkk) K_{2,3} minus two edges (different bottoms to different tops).
     4 edges [c < a], [c < b], [d < a], [e < b]: bottom [c] below both
     tops, bottom [d] below only [a], bottom [e] below only [b]. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 c a /\ R2 c b /\ R2 d a /\ R2 e b /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = c /\ y = a) \/ (x = c /\ y = b) \/
           (x = d /\ y = a) \/ (x = e /\ y = b)))))
    as [HK23mm | HnK23mm].
  { apply (@n5_K_2_3_minus_two_edges_two_realizer B R2 HR2 Hcard).
    exact HK23mm. }
  (* (llll) K_{3,2} minus two edges (different tops from different bottoms).
     4 edges [a < d], [b < d], [c < d], [c < e]: top [d] above all three
     bottoms, top [e] above only bottom [c].  Dual of (kkkk). *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a d /\ R2 b d /\ R2 c d /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = d) \/ (x = b /\ y = d) \/
           (x = c /\ y = d) \/ (x = c /\ y = e)))))
    as [HK32mm | HnK32mm].
  { apply (@n5_K_3_2_minus_two_edges_two_realizer B R2 HR2 Hcard).
    exact HK32mm. }
  (* (mmmm) 3-chain a<b<c with top pendant d<c and bottom pendant a<e.
     5 direct edges: [a<b], [b<c], [a<c], [d<c], [a<e]. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 b c /\ R2 a c /\ R2 d c /\ R2 a e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = b /\ y = c) \/ (x = a /\ y = c) \/
           (x = d /\ y = c) \/ (x = a /\ y = e)))))
    as [HBtP | HnBtP].
  { apply (@n5_chain3_bot_pendant_and_top_pendant_two_realizer B R2 HR2 Hcard).
    exact HBtP. }
  (* (nnnn) K_{3,2} minus a perfect matching.  4 edges [a<e], [b<d],
     [c<d], [c<e]: bipartite (a,b,c) -> (d,e) with non-adjacent edges
     a<d and b<e removed. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a e /\ R2 b d /\ R2 c d /\ R2 c e /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = e) \/ (x = b /\ y = d) \/
           (x = c /\ y = d) \/ (x = c /\ y = e)))))
    as [HK32mmatch | HnK32mmatch].
  { apply (@n5_K_3_2_minus_matching_two_realizer B R2 HR2 Hcard).
    exact HK32mmatch. }
  (* (oooo) Class 31: 6 strict edges a<b, a<c, a<d, a<e, b<c, b<d. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 a e /\ R2 b c /\ R2 b d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = a /\ y = e) \/ (x = b /\ y = c) \/ (x = b /\ y = d)))))
    as [HC31 | HnC31].
  { apply (@n5_class31_two_realizer B R2 HR2 Hcard).
    exact HC31. }
  (* (pppp) Class 38: 6 strict edges a<b, a<c, a<d, b<c, e<c, e<d. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 a d /\ R2 b c /\ R2 e c /\ R2 e d /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = a /\ y = d) \/
           (x = b /\ y = c) \/ (x = e /\ y = c) \/ (x = e /\ y = d)))))
    as [HC38 | HnC38].
  { apply (@n5_class38_two_realizer B R2 HR2 Hcard).
    exact HC38. }
  (* (qqqq) Class 40: 6 strict edges a<b, a<c, b<c, d<b, d<c, e<c. *)
  destruct (classic
    (exists a b c d e : B,
       a <> b /\ a <> c /\ a <> d /\ a <> e /\
       b <> c /\ b <> d /\ b <> e /\
       c <> d /\ c <> e /\
       d <> e /\
       R2 a b /\ R2 a c /\ R2 b c /\ R2 d b /\ R2 d c /\ R2 e c /\
       (forall x y : B,
          R2 x y -> x = y \/
          ((x = a /\ y = b) \/ (x = a /\ y = c) \/ (x = b /\ y = c) \/
           (x = d /\ y = b) \/ (x = d /\ y = c) \/ (x = e /\ y = c)))))
    as [HC40 | HnC40].
  { apply (@n5_class40_two_realizer B R2 HR2 Hcard).
    exact HC40. }
  (* Fall-through: either one_edge or residual.

     Before reaching the focused residual admit, discharge total-order
     configurations: if every pair of carrier elements is R2-comparable,
     the carrier is totally ordered (a 5-chain), contradicting the
     existence of an incomparable pair [Hinc_ex] via [n5_chain_contra_inc]. *)
  destruct (classic
    (forall a b : B, a = b \/ R2 a b \/ R2 b a))
    as [HtotalCmp | HnotTotal].
  { (* All pairs R2-comparable: derive False from Hinc_ex. *)
    destruct (@carrier_5_destructure B p q Hcard Hpq_neq)
      as [r [s [t [Hpr_neq [Hps_neq [Hpt_neq
                     [Hqr_neq [Hqs_neq [Hqt_neq
                     [Hrs_neq [Hrt_neq [Hst_neq Hcov5]]]]]]]]]]]].
    assert (Hcmp_pq : R2 p q \/ R2 q p) by (left; exact HRpq).
    assert (Hcmp_pr : R2 p r \/ R2 r p)
      by (destruct (HtotalCmp p r) as [Heq | [H | H]];
          [exfalso; apply Hpr_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_ps : R2 p s \/ R2 s p)
      by (destruct (HtotalCmp p s) as [Heq | [H | H]];
          [exfalso; apply Hps_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_pt : R2 p t \/ R2 t p)
      by (destruct (HtotalCmp p t) as [Heq | [H | H]];
          [exfalso; apply Hpt_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_qr : R2 q r \/ R2 r q)
      by (destruct (HtotalCmp q r) as [Heq | [H | H]];
          [exfalso; apply Hqr_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_qs : R2 q s \/ R2 s q)
      by (destruct (HtotalCmp q s) as [Heq | [H | H]];
          [exfalso; apply Hqs_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_qt : R2 q t \/ R2 t q)
      by (destruct (HtotalCmp q t) as [Heq | [H | H]];
          [exfalso; apply Hqt_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_rs : R2 r s \/ R2 s r)
      by (destruct (HtotalCmp r s) as [Heq | [H | H]];
          [exfalso; apply Hrs_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_rt : R2 r t \/ R2 t r)
      by (destruct (HtotalCmp r t) as [Heq | [H | H]];
          [exfalso; apply Hrt_neq; exact Heq | left; exact H | right; exact H]).
    assert (Hcmp_st : R2 s t \/ R2 t s)
      by (destruct (HtotalCmp s t) as [Heq | [H | H]];
          [exfalso; apply Hst_neq; exact Heq | left; exact H | right; exact H]).
    exact (@n5_chain_contra_inc B R2 HR2 p q r s t Hcov5 Hinc_ex
             Hcmp_pq Hcmp_pr Hcmp_ps Hcmp_pt
             Hcmp_qr Hcmp_qs Hcmp_qt
             Hcmp_rs Hcmp_rt Hcmp_st _). }
  destruct (classic (exists x y : B, x <> y /\ R2 x y /\ ~ (x = p /\ y = q)))
    as [Hother | Honly].
  - (* Some other strict edge exists.  Before routing to the residual
       admit, peel off micro-cases that can be closed Qed-style in the
       dispatcher:

         (i) [(x, y) = (q, p)] — reverse of [(p, q)] — yields
             [R2 p q /\ R2 q p], so antisymmetry gives [p = q],
             contradicting [Hpq_neq].

       Extract the remaining three carrier elements [r, s, t] up front
       via [carrier_5_destructure] so that subsequent expansions of this
       branch can label the second edge against the full 5-element
       structure. *)
    destruct (@carrier_5_destructure B p q Hcard Hpq_neq)
      as [r [s [t [Hpr_neq [Hps_neq [Hpt_neq
                     [Hqr_neq [Hqs_neq [Hqt_neq
                     [Hrs_neq [Hrt_neq [Hst_neq Hcov5]]]]]]]]]]]].
    destruct Hother as [x [y [Hxy_neq [HRxy Hnot_pq]]]].
    (* Micro-case (i): if the second edge is [(q, p)], antisymmetry kills it
       (delegated to [n5_dispatcher_microcase_i]). *)
    destruct (classic (x = q /\ y = p)) as [[Hxq Hyp] | Hnot_qp].
    { exfalso.
      subst x y.
      exact (@n5_dispatcher_microcase_i B R2 HR2 p q Hpq_neq HRpq HRxy). }
    (* Micro-case (ii): second edge is [(r, s)] — delegated to
       [n5_dispatcher_microcase_ii] (Qed-closed). *)
    destruct (classic (x = r /\ y = s)) as [[Hxr Hys] | Hnot_rs].
    { subst x y.
      apply (@n5_dispatcher_microcase_ii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
               HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP). }
    (* Micro-case (iii): second edge is [(s, r)] — delegated to
       [n5_dispatcher_microcase_iii] (Qed-closed). *)
    destruct (classic (x = s /\ y = r)) as [[Hxs Hyr] | Hnot_sr].
    { subst x y.
      apply (@n5_dispatcher_microcase_iii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj). }
    (* Micro-case (iv): if the second edge is [(r, t)] AND no third strict
       edge exists, the carrier is realized by exactly the two disjoint
       chains [(p, q)] and [(r, t)] plus isolated [s] — contradicts
       [HnDisj] with the [(c, d)] slot bound to [(r, t)].

       Third-edge expansion: parallel to Micro-case (ii) [(r, s)] with [s]
       and [t] swapped (so [s] is the isolated, [t] is the chain-top). *)
    destruct (classic (x = r /\ y = t)) as [[Hxr Hyt] | Hnot_rt].
    { subst x y.
      apply (@n5_dispatcher_microcase_iv B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
               HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP). }
    (* Micro-case (v): second edge is [(t, r)] — disjoint chains [(p, q)]
       and [(t, r)] with isolated [s].

       Third-edge expansion: parallel to Micro-case (iv) [(r, t)] with [r]
       and [t] swapped (so the second chain is [t < r] instead of [r < t]). *)
    destruct (classic (x = t /\ y = r)) as [[Hxt Hyr] | Hnot_tr].
    { subst x y.
      apply (@n5_dispatcher_microcase_v B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj
               HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP). }
    (* Micro-case (vi): second edge is [(s, t)] — disjoint chains [(p, q)]
       and [(s, t)] with isolated [r].

       Third-edge expansion: parallel to Micro-case (iv) [(r, t)] with [r]
       and [s] swapped (so the second chain is [s < t] with [r] isolated). *)
    destruct (classic (x = s /\ y = t)) as [[Hxs Hyt] | Hnot_st].
    { subst x y.
      apply (@n5_dispatcher_microcase_vi B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq HnDisj
               HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP). }
    (* Micro-case (vii): second edge is [(t, s)] — disjoint chains [(p, q)]
       and [(t, s)] with isolated [r].

       Third-edge expansion: parallel to Micro-case (v) [(t, r)] with [r]
       and [s] swapped (so the second chain is [t < s] with [r] isolated). *)
    destruct (classic (x = t /\ y = s)) as [[Hxt Hys] | Hnot_ts].
    { subst x y.
      apply (@n5_dispatcher_microcase_vii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq HRpq HRxy Hnot_pq HnDisj
               HnN HnCC HnVc HninvVc HnC4 HnPd HnTopP). }
    (* Micro-case (viii): second edge is [(p, r)] — V at [p] with leaves
       [q] and [r], plus isolated [s], [t].  Delegated to
       [n5_dispatcher_microcase_viii] (Qed-closed). *)
    destruct (classic (x = p /\ y = r)) as [[Hxp Hyr] | Hnot_pr].
    { subst x y.
      apply (@n5_dispatcher_microcase_viii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnV HnN HnClawUp HnCC HnVc HnC4 HnPd HnYup HnYdn
               HnTopP HnVpb). }
    (* Micro-case (ix): second edge is [(p, s)] — V at [p] with leaves
       [q] and [s], plus isolated [r], [t].  Delegated to
       [n5_dispatcher_microcase_ix] (Qed-closed). *)
    destruct (classic (x = p /\ y = s)) as [[Hxp Hys] | Hnot_ps].
    { subst x y.
      apply (@n5_dispatcher_microcase_ix B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnV HnN HnClawUp HnVc HnPd HnVpb). }
    (* Micro-case (x): second edge is [(p, t)] — V at [p] with leaves
       [q] and [t], plus isolated [r], [s].  Delegated to
       [n5_dispatcher_microcase_x] (Qed-closed). *)
    destruct (classic (x = p /\ y = t)) as [[Hxp Hyt] | Hnot_pt].
    { subst x y.
      apply (@n5_dispatcher_microcase_x B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnV HnN HnClawUp HnVc HnPd HnVpb). }
    (* Micro-case (xi): second edge is [(r, q)] — inv-V at [q] with
       bottoms [p] and [r], plus isolated [s], [t].  Delegated to
       [n5_dispatcher_microcase_xi] (Qed-closed). *)
    destruct (classic (x = r /\ y = q)) as [[Hxr Hyq] | Hnot_rq].
    { subst x y.
      apply (@n5_dispatcher_microcase_xi B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn). }
    (* Micro-case (xii): second edge is [(s, q)] — delegated to
       [n5_dispatcher_microcase_xii] (Qed-closed). *)
    destruct (classic (x = s /\ y = q)) as [[Hxs Hyq] | Hnot_sq].
    { subst x y.
      apply (@n5_dispatcher_microcase_xii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn). }
    (* Micro-case (xiii): second edge is [(t, q)] — delegated to
       [n5_dispatcher_microcase_xiii] (Qed-closed). *)
    destruct (classic (x = t /\ y = q)) as [[Hxt Hyq] | Hnot_tq].
    { subst x y.
      apply (@n5_dispatcher_microcase_xiii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HninvV HnN HnClawDn HninvVc HniVcol HnYdn). }
    (* Micro-case (xiv): second edge is [(q, r)] — delegated to
       [n5_dispatcher_microcase_xiv] (Qed-closed). *)
    destruct (classic (x = q /\ y = r)) as [[Hxq Hyr] | Hnot_qr].
    { subst x y.
      apply (@n5_dispatcher_microcase_xiv B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Micro-case (xv): second edge is [(q, s)] — delegated to
       [n5_dispatcher_microcase_xv] (Qed-closed). *)
    destruct (classic (x = q /\ y = s)) as [[Hxq Hys] | Hnot_qs].
    { subst x y.
      apply (@n5_dispatcher_microcase_xv B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Micro-case (xvi): second edge is [(q, t)] — delegated to
       [n5_dispatcher_microcase_xvi] (Qed-closed). *)
    destruct (classic (x = q /\ y = t)) as [[Hxq Hyt] | Hnot_qt].
    { subst x y.
      apply (@n5_dispatcher_microcase_xvi B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Micro-case (xvii): second edge is [(r, p)] — delegated to
       [n5_dispatcher_microcase_xvii] (Qed-closed). *)
    destruct (classic (x = r /\ y = p)) as [[Hxr Hyp] | Hnot_rp].
    { subst x y.
      apply (@n5_dispatcher_microcase_xvii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Micro-case (xviii): second edge is [(s, p)] — delegated to
       [n5_dispatcher_microcase_xviii] (Qed-closed). *)
    destruct (classic (x = s /\ y = p)) as [[Hxs Hyp] | Hnot_sp].
    { subst x y.
      apply (@n5_dispatcher_microcase_xviii B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Micro-case (xix): second edge is [(t, p)] — by transitivity R2 t q
       holds, so the carrier admits the 3-chain [t < p < q] plus isolated
       [r], [s]. If no fourth strict edge exists, this contradicts [HnChain3].
       Otherwise, peel off each well-defined 4th-edge labeling and route to
       the matching closed per-class shape. *)
    destruct (classic (x = t /\ y = p)) as [[Hxt Hyp] | Hnot_tp].
    { subst x y.
      assert (HRtq : R2 t q) by exact (HR2.(poset_trans) t p q HRxy HRpq).
      destruct (classic (exists a b : B,
                a <> b /\ R2 a b /\
                ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                ~ (a = t /\ b = q)))
        as [Hfourth | Hno_fourth].
      - (* A fourth strict edge exists. Peel off well-defined 4th-edge
           labelings and route to upstream per-class shapes; fall through
           to the focused admit only for residuals (none remain). *)
        (* (a) fourth edge = (q, p) — antisymmetry. *)
        destruct (classic (R2 q p)) as [HRqp | HnRqp].
        { exfalso. apply Hpq_neq.
          exact (HR2.(poset_antisym) p q HRpq HRqp). }
        (* (b) fourth edge = (p, t) — antisymmetry with HRxy : R2 t p. *)
        destruct (classic (R2 p t)) as [HRpr_fourth | HnRpr_fourth].
        { exfalso. apply Hpt_neq.
          exact (HR2.(poset_antisym) p t HRpr_fourth HRxy). }
        (* (c) fourth edge = (q, t) — antisymmetry with HRtq : R2 t q. *)
        destruct (classic (R2 q t)) as [HRqt | HnRqt].
        { exfalso. apply Hqt_neq.
          exact (HR2.(poset_antisym) q t HRqt HRtq). }
        (* (d) fourth edge = (s, t): 4-chain s<t<p<q + iso r (HnC4). *)
        destruct (classic (R2 s t)) as [HRst | HnRst].
        { assert (HRsp_new : R2 s p) by exact (HR2.(poset_trans) s t p HRst HRxy).
          assert (HRsq_new : R2 s q) by exact (HR2.(poset_trans) s p q HRsp_new HRpq).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = s /\ b = t) /\
                    ~ (a = s /\ b = p) /\ ~ (a = s /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
            split; [exact HRst |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnC4.
            exists s, t, p, q, r.
            split; [intro Hst_eq; apply Hst_neq; exact Hst_eq |].
            split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
            split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqr_neq |].
            split; [exact HRst |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRsp_new |].
            split; [exact HRsq_new |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = s /\ v = t)) as [Hust | Hnot_ust];
              [left; exact Hust |].
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [right; left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; right; left; exact Hupq |].
            destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
              [right; right; right; left; exact Husp |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; right; right; right; left; exact Husq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_ust |].
            split; [exact Hnot_usp |]. exact Hnot_usq. }
        (* (e) fourth edge = (r, t): 4-chain r<t<p<q + iso s (HnC4). *)
        destruct (classic (R2 r t)) as [HRrt | HnRrt].
        { assert (HRtp_new : R2 r p) by exact (HR2.(poset_trans) r t p HRrt HRxy).
          assert (HRtq_new : R2 r q) by exact (HR2.(poset_trans) r p q HRtp_new HRpq).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = r /\ b = t) /\
                    ~ (a = r /\ b = p) /\ ~ (a = r /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, t.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
            split; [exact HRrt |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnC4.
            exists r, t, p, q, s.
            split; [intro Hrt_eq; apply Hrt_neq; exact Hrt_eq |].
            split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
            split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqs_neq |].
            split; [exact HRrt |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRtp_new |].
            split; [exact HRtq_new |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = r /\ v = t)) as [Hurt | Hnot_urt];
              [left; exact Hurt |].
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [right; left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; right; left; exact Hupq |].
            destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
              [right; right; right; left; exact Hurp |].
            destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
              [right; right; right; right; left; exact Hurq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_urt |].
            split; [exact Hnot_urp |]. exact Hnot_urq. }
        (* (f) fourth edge = (q, s): 4-chain t<p<q<s + iso r (HnC4). *)
        destruct (classic (R2 q s)) as [HRqs | HnRqs].
        { assert (HRps_new : R2 p s) by exact (HR2.(poset_trans) p q s HRpq HRqs).
          assert (HRrs_new : R2 t s) by exact (HR2.(poset_trans) t p s HRxy HRps_new).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = q /\ b = s) /\
                    ~ (a = p /\ b = s) /\ ~ (a = t /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqs_neq |].
            split; [exact HRqs |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnC4.
            exists t, p, q, s, r.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRqs |].
            split; [exact HRtq |].
            split; [exact HRrs_new |].
            split; [exact HRps_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = s)) as [Huqs | Hnot_uqs];
              [right; right; left; exact Huqs |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
              [right; right; right; right; left; exact Huts |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; right; right; right; exact Hups |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_uqs |].
            split; [exact Hnot_ups |]. exact Hnot_uts. }
        (* (g) fourth edge = (q, r): 4-chain t<p<q<r + iso s (HnC4). *)
        destruct (classic (R2 q r)) as [HRqr | HnRqr].
        { assert (HRpt_new : R2 p r) by exact (HR2.(poset_trans) p q r HRpq HRqr).
          assert (HRrt_new : R2 t r) by exact (HR2.(poset_trans) t p r HRxy HRpt_new).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = q /\ b = r) /\
                    ~ (a = p /\ b = r) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, q, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hqr_neq |].
            split; [exact HRqr |].
            intros [Hqp _]; apply Hpq_neq; symmetry; exact Hqp.
          - exfalso. apply HnC4.
            exists t, p, q, r, s.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRqr |].
            split; [exact HRtq |].
            split; [exact HRrt_new |].
            split; [exact HRpt_new |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = q /\ v = r)) as [Huqr | Hnot_uqr];
              [right; right; left; exact Huqr |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; left; exact Hutr |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; right; right; right; exact Hupr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_uqr |].
            split; [exact Hnot_upr |]. exact Hnot_utr. }
        (* (h) fourth edge = (t, s): 3-chain t<p<q + pendant t<s + iso r
           (HnPd) with a=t, b=p, c=q, d=s. *)
        destruct (classic (R2 t s)) as [HRrs_fourth | HnRrs_fourth].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = t /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact HRrs_fourth |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnPd.
            exists t, p, q, s, r.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRrs_fourth |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
              [right; right; left; exact Huts |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_uts. }
        (* (i) fourth edge = (t, r): 3-chain t<p<q + pendant t<r + iso s
           (HnPd) with a=t, b=p, c=q, d=r. *)
        destruct (classic (R2 t r)) as [HRrt_fourth | HnRrt_fourth].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, t, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact HRrt_fourth |].
            intros [Htp _]; apply Hpt_neq; symmetry; exact Htp.
          - exfalso. apply HnPd.
            exists t, p, q, r, s.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRrt_fourth |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; left; exact Hutr |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_utr. }
        (* (j) fourth edge = (p, s): Y-up apex t, branch p->{q,s} (HnYup)
           with a=t, b=p, c=q, d=s. *)
        destruct (classic (R2 p s)) as [HRps | HnRps].
        { assert (HRts_via : R2 t s) by exact (HR2.(poset_trans) t p s HRxy HRps).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = p /\ b = s) /\
                    ~ (a = t /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hps_neq |].
            split; [exact HRps |].
            intros [_ Hsq]; apply Hqs_neq; symmetry; exact Hsq.
          - exfalso. apply HnYup.
            exists t, p, q, s, r.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRps |].
            split; [exact HRtq |].
            split; [exact HRts_via |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = p /\ v = s)) as [Hups | Hnot_ups];
              [right; right; left; exact Hups |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = s)) as [Huts | Hnot_uts];
              [right; right; right; right; exact Huts |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_ups |]. exact Hnot_uts. }
        (* (k) fourth edge = (p, r): Y-up apex t, branch p->{q,r} (HnYup). *)
        destruct (classic (R2 p r)) as [HRpr | HnRpr].
        { assert (HRtr_via : R2 t r) by exact (HR2.(poset_trans) t p r HRxy HRpr).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = p /\ b = r) /\
                    ~ (a = t /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, p, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [exact Hpr_neq |].
            split; [exact HRpr |].
            intros [_ Hrq]; apply Hqr_neq; symmetry; exact Hrq.
          - exfalso. apply HnYup.
            exists t, p, q, r, s.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRpr |].
            split; [exact HRtq |].
            split; [exact HRtr_via |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = p /\ v = r)) as [Hupr | Hnot_upr];
              [right; right; left; exact Hupr |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = t /\ v = r)) as [Hutr | Hnot_utr];
              [right; right; right; right; exact Hutr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_upr |]. exact Hnot_utr. }
        (* (l) fourth edge = (s, p): Y-down apex q, p has parents t,s
           (HnYdn) with a=q, b=p, c=t, d=s. *)
        destruct (classic (R2 s p)) as [HRsp | HnRsp].
        { assert (HRsq_via : R2 s q) by exact (HR2.(poset_trans) s p q HRsp HRpq).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = s /\ b = p) /\
                    ~ (a = s /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hps_eq; apply Hps_neq; symmetry; exact Hps_eq |].
            split; [exact HRsp |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnYdn.
            exists q, p, t, s, r.
            split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
            split; [exact Hqt_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRsp |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRsq_via |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = s /\ v = p)) as [Husp | Hnot_usp];
              [right; left; exact Husp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; right; left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; right; right; right; exact Husq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_usp |]. exact Hnot_usq. }
        (* (m) fourth edge = (r, p): Y-down apex q, p has parents t,r
           (HnYdn) with a=q, b=p, c=t, d=r. *)
        destruct (classic (R2 r p)) as [HRrp | HnRrp].
        { assert (HRrq_via : R2 r q) by exact (HR2.(poset_trans) r p q HRrp HRpq).
          destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = r /\ b = p) /\
                    ~ (a = r /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, p.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hpr_eq; apply Hpr_neq; symmetry; exact Hpr_eq |].
            split; [exact HRrp |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnYdn.
            exists q, p, t, r, s.
            split; [intro Hpq_eq; apply Hpq_neq; symmetry; exact Hpq_eq |].
            split; [exact Hqt_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hpt_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRrp |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRrq_via |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = r /\ v = p)) as [Hurp | Hnot_urp];
              [right; left; exact Hurp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; right; left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; left; exact Hutq |].
            destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
              [right; right; right; right; exact Hurq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |].
            split; [exact Hnot_urp |]. exact Hnot_urq. }
        (* (n) fourth edge = (s, q): 3-chain t<p<q + top pendant s<q + iso r
           (HnTopP) with a=t, b=p, c=q, d=s. *)
        destruct (classic (R2 s q)) as [HRsq | HnRsq].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = s /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hqs_eq; apply Hqs_neq; symmetry; exact Hqs_eq |].
            split; [exact HRsq |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnTopP.
            exists t, p, q, s, r.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRsq |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = s /\ v = q)) as [Husq | Hnot_usq];
              [right; right; left; exact Husq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_usq. }
        (* (o) fourth edge = (r, q): 3-chain t<p<q + top pendant r<q + iso s
           (HnTopP). *)
        destruct (classic (R2 r q)) as [HRrq | HnRrq].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = r /\ b = q)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, q.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hqr_eq; apply Hqr_neq; symmetry; exact Hqr_eq |].
            split; [exact HRrq |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnTopP.
            exists t, p, q, r, s.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRrq |].
            split; [exact HRtq |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = r /\ v = q)) as [Hurq | Hnot_urq];
              [right; right; left; exact Hurq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; right; exact Hutq |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_urq. }
        (* (p) fourth edge = (s, r): 3-chain t<p<q + disjoint chain s<r
           (HnCC). *)
        destruct (classic (R2 s r)) as [HRsr | HnRsr].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = s /\ b = r)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, s, r.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRsr |].
            intros [Hsp _]; apply Hps_neq; symmetry; exact Hsp.
          - exfalso. apply HnCC.
            exists t, p, q, s, r.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hps_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hqs_neq |].
            split; [exact Hqr_neq |].
            split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRsr |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; left; exact Hutq |].
            destruct (classic (u = s /\ v = r)) as [Husr | Hnot_usr];
              [right; right; right; exact Husr |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_usr. }
        (* (q) fourth edge = (r, s): 3-chain t<p<q + disjoint chain r<s
           (HnCC). *)
        destruct (classic (R2 r s)) as [HRrs | HnRrs].
        { destruct (classic (exists a b : B,
                    a <> b /\ R2 a b /\
                    ~ (a = p /\ b = q) /\ ~ (a = t /\ b = p) /\
                    ~ (a = t /\ b = q) /\ ~ (a = r /\ b = s)))
            as [Hfifth | Hno_fifth].
          - apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
                     Hnonantichain Hinc_ex).
            exists p, q, r, s.
            split; [exact Hpq_neq |].
            split; [exact HRpq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRrs |].
            intros [Hrp _]; apply Hpr_neq; symmetry; exact Hrp.
          - exfalso. apply HnCC.
            exists t, p, q, r, s.
            split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
            split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
            split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
            split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
            split; [exact Hpq_neq |].
            split; [exact Hpr_neq |].
            split; [exact Hps_neq |].
            split; [exact Hqr_neq |].
            split; [exact Hqs_neq |].
            split; [intro Hrs_eq; apply Hrs_neq; exact Hrs_eq |].
            split; [exact HRxy |].
            split; [exact HRpq |].
            split; [exact HRtq |].
            split; [exact HRrs |].
            intros u v HRuv.
            destruct (classic (u = v)) as [Heq | Huv_neq];
              [left; exact Heq |].
            right.
            destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
              [left; exact Hutp |].
            destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
              [right; left; exact Hupq |].
            destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
              [right; right; left; exact Hutq |].
            destruct (classic (u = r /\ v = s)) as [Hurs | Hnot_urs];
              [right; right; right; exact Hurs |].
            exfalso. apply Hno_fifth.
            exists u, v. split; [exact Huv_neq |].
            split; [exact HRuv |].
            split; [exact Hnot_upq |].
            split; [exact Hnot_utp |].
            split; [exact Hnot_utq |]. exact Hnot_urs. }
        (* All 17 possible 4th-edge labelings ruled out: dispatch via Hcov5. *)
        exfalso.
        destruct Hfourth as [a [b [Hab_neq [HRab [Hnot_ab_pq [Hnot_ab_tp Hnot_ab_tq]]]]]].
        destruct (Hcov5 a) as [Hap | [Haq | [Har | [Has | Hat]]]];
          destruct (Hcov5 b) as [Hbp | [Hbq | [Hbr | [Hbs | Hbt]]]];
          subst a b;
          first
            [ apply Hab_neq; reflexivity
            | apply Hnot_ab_pq; split; reflexivity
            | apply Hnot_ab_tp; split; reflexivity
            | apply Hnot_ab_tq; split; reflexivity
            | apply HnRqp; exact HRab
            | apply HnRpr_fourth; exact HRab
            | apply HnRqt; exact HRab
            | apply HnRst; exact HRab
            | apply HnRrt; exact HRab
            | apply HnRqs; exact HRab
            | apply HnRqr; exact HRab
            | apply HnRrs_fourth; exact HRab
            | apply HnRrt_fourth; exact HRab
            | apply HnRps; exact HRab
            | apply HnRpr; exact HRab
            | apply HnRsp; exact HRab
            | apply HnRrp; exact HRab
            | apply HnRsq; exact HRab
            | apply HnRrq; exact HRab
            | apply HnRsr; exact HRab
            | apply HnRrs; exact HRab ].
      - exfalso. apply HnChain3.
        exists t, p, q, s, r.
        split; [intro Hpt_eq; apply Hpt_neq; symmetry; exact Hpt_eq |].
        split; [intro Hqt_eq; apply Hqt_neq; symmetry; exact Hqt_eq |].
        split; [intro Hts_eq; apply Hst_neq; symmetry; exact Hts_eq |].
        split; [intro Htr_eq; apply Hrt_neq; symmetry; exact Htr_eq |].
        split; [exact Hpq_neq |].
        split; [exact Hps_neq |].
        split; [exact Hpr_neq |].
        split; [exact Hqs_neq |].
        split; [exact Hqr_neq |].
        split; [intro Hsr_eq; apply Hrs_neq; symmetry; exact Hsr_eq |].
        split; [exact HRxy |].
        split; [exact HRpq |].
        split; [exact HRtq |].
        intros u v HRuv.
        destruct (classic (u = v)) as [Heq | Huv_neq];
          [left; exact Heq |].
        right.
        destruct (classic (u = t /\ v = p)) as [Hutp | Hnot_utp];
          [left; exact Hutp |].
        destruct (classic (u = t /\ v = q)) as [Hutq | Hnot_utq];
          [right; left; exact Hutq |].
        destruct (classic (u = p /\ v = q)) as [Hupq | Hnot_upq];
          [right; right; exact Hupq |].
        exfalso. apply Hno_fourth.
        exists u, v. split; [exact Huv_neq |].
        split; [exact HRuv |].
        split; [exact Hnot_upq |].
        split; [exact Hnot_utp |]. exact Hnot_utq. }
    (* Otherwise, route the residual configuration to the focused admit. *)
    apply (@n5_residual_classes_two_realizer B R2 HR2 Hcard
             Hnonantichain Hinc_ex).
    exists p, q, x, y.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    split; [exact Hxy_neq |].
    split; [exact HRxy |].
    exact Hnot_pq.
  - (* Only (p, q) is a non-trivial relation: class (a). *)
    apply (@n5_one_edge_two_realizer B R2 HR2 Hcard).
    exists p, q.
    split; [exact Hpq_neq |].
    split; [exact HRpq |].
    intros a b HRab.
    destruct (classic (a = b)) as [Heq | Hneq]; [left; exact Heq |].
    right.
    destruct (classic (a = p /\ b = q)) as [Hpq_match | Hnot_pq].
    + exact Hpq_match.
    + exfalso. apply Honly.
      exists a, b. split; [exact Hneq |]. split; [exact HRab |]. exact Hnot_pq.
Qed.
