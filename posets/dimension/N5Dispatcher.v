(** n = 5 dispatcher cascade — top-level wrapper.

    The per-class isomorphism lemmas live in N5Realizers.v; the
    Qed-closed micro-case handlers live in N5Dispatcher_i.v ..
    N5Dispatcher_xix.v; the focused admit lives in
    N5DispatcherShapes.v.  This file only contains the cascade
    that dispatches to those lemmas. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance.
From Stdlib Require Import IndefiniteDescription ClassicalDescription.
From Stdlib Require Import Relations.Relation_Operators.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Szpilrajn Theorems.
From Dimension Require Import N5Realizers N5DispatcherShapes.
From Dimension Require Import
  N5Dispatcher_i N5Dispatcher_ii N5Dispatcher_iii N5Dispatcher_iv
  N5Dispatcher_v N5Dispatcher_vi N5Dispatcher_vii N5Dispatcher_viii
  N5Dispatcher_ix N5Dispatcher_x N5Dispatcher_xi N5Dispatcher_xii
  N5Dispatcher_xiii N5Dispatcher_xiv N5Dispatcher_xv N5Dispatcher_xvi
  N5Dispatcher_xvii N5Dispatcher_xviii N5Dispatcher_xix.
From ZornsLemma Require Import FiniteTypes EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

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
    (* Micro-case (xix): second edge is [(t, p)] — delegated to
       [n5_dispatcher_microcase_xix] (Qed-closed). *)
    destruct (classic (x = t /\ y = p)) as [[Hxt Hyp] | Hnot_tp].
    { subst x y.
      apply (@n5_dispatcher_microcase_xix B R2 HR2 Hcard Hnonantichain
               Hinc_ex p q r s t
               Hpq_neq Hpr_neq Hps_neq Hpt_neq Hqr_neq Hqs_neq Hqt_neq
               Hrs_neq Hrt_neq Hst_neq Hcov5 HRpq HRxy Hnot_pq
               HnChain3 HnCC HnC4 HnPd HnTopP HnYup HnYdn). }
    (* Catch-all: the cascade above has tested every ordered pair of
       distinct elements from the 5-element carrier {p, q, r, s, t}.
       Concretely, [Hcov5] forces [x, y ∈ {p, q, r, s, t}], [Hxy_neq]
       rules out the 5 diagonal pairs, and [Hnot_pq] plus the 19
       per-case [Hnot_*] hypotheses rule out all 20 distinct ordered
       pairs.  Hence this branch is unreachable; we close it by [False]
       (avoiding the focused admit). *)
    exfalso.
    destruct (Hcov5 x) as [Hxp | [Hxq | [Hxr | [Hxs | Hxt]]]];
      destruct (Hcov5 y) as [Hyp | [Hyq | [Hyr | [Hys | Hyt]]]];
      subst;
      first
        [ exact (Hxy_neq eq_refl)
        | exact (Hnot_pq (conj eq_refl eq_refl))
        | exact (Hnot_pr (conj eq_refl eq_refl))
        | exact (Hnot_ps (conj eq_refl eq_refl))
        | exact (Hnot_pt (conj eq_refl eq_refl))
        | exact (Hnot_qp (conj eq_refl eq_refl))
        | exact (Hnot_qr (conj eq_refl eq_refl))
        | exact (Hnot_qs (conj eq_refl eq_refl))
        | exact (Hnot_qt (conj eq_refl eq_refl))
        | exact (Hnot_rp (conj eq_refl eq_refl))
        | exact (Hnot_rq (conj eq_refl eq_refl))
        | exact (Hnot_rs (conj eq_refl eq_refl))
        | exact (Hnot_rt (conj eq_refl eq_refl))
        | exact (Hnot_sp (conj eq_refl eq_refl))
        | exact (Hnot_sq (conj eq_refl eq_refl))
        | exact (Hnot_sr (conj eq_refl eq_refl))
        | exact (Hnot_st (conj eq_refl eq_refl))
        | exact (Hnot_tp (conj eq_refl eq_refl))
        | exact (Hnot_tq (conj eq_refl eq_refl))
        | exact (Hnot_tr (conj eq_refl eq_refl))
        | exact (Hnot_ts (conj eq_refl eq_refl)) ].
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
