(* A disjoint union of chains has dimension <= 2; hence every frontier block of a
   well-formed schedule has dim <= 2 (closes critical-review finding 2). *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                           ProofIrrelevance Relation_Operators Operators_Properties.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape
                              ConnSync.
Import ListNotations.
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma disjoint_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (comp : A -> nat),
    (forall x y, R x y -> comp x = comp y) ->
    (forall x y, comp x = comp y -> R x y \/ R y x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR comp Hrel Hchain d Hdim.
  set (L1 := fun x y : A => comp x < comp y \/ (comp x = comp y /\ R x y)).
  set (L2 := fun x y : A => comp y < comp x \/ (comp x = comp y /\ R x y)).
  assert (HL1 : IsLinearExtension R L1).
  { constructor.
    - constructor.
      + constructor.
        * (* poset_refl *) intro x. right. split; [reflexivity | apply poset_refl].
        * (* poset_antisym *) intros x y Hxy Hyx. unfold L1 in Hxy, Hyx.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
            try lia. apply (poset_antisym _ _ Hr1 Hr2).
        * (* poset_trans *) intros x y z Hxy Hyz. unfold L1 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]];
            try (left; lia).
          right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
      + (* total_comparable *) intros x y. unfold L1.
        destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hlt|Heq]|Hgt].
        * left; left; exact Hlt.
        * destruct (Hchain x y Heq) as [Hr|Hr];
            [ left; right; split; [exact Heq | exact Hr]
            | right; right; split; [symmetry; exact Heq | exact Hr] ].
        * right; left; exact Hgt.
    - (* linear_extends *) intros x y Hr. unfold L1. right.
      split; [apply Hrel; exact Hr | exact Hr]. }
  assert (HL2 : IsLinearExtension R L2).
  { constructor.
    - constructor.
      + constructor.
        * intro x. right. split; [reflexivity | apply poset_refl].
        * intros x y Hxy Hyx. unfold L2 in Hxy, Hyx.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
            try lia. apply (poset_antisym _ _ Hr1 Hr2).
        * intros x y z Hxy Hyz. unfold L2 in *.
          destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]];
            try (left; lia).
          right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
      + intros x y. unfold L2.
        destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hlt|Heq]|Hgt].
        * right; left; exact Hlt.
        * destruct (Hchain x y Heq) as [Hr|Hr];
            [ left; right; split; [exact Heq | exact Hr]
            | right; right; split; [symmetry; exact Heq | exact Hr] ].
        * left; left; exact Hgt.
    - intros x y Hr. unfold L2. right.
      split; [apply Hrel; exact Hr | exact Hr]. }
  assert (Hcap : forall x y, R x y <-> (L1 x y /\ L2 x y)).
  { intros x y. split.
    - intro Hr. assert (Hc : comp x = comp y) by (apply Hrel; exact Hr).
      split; (right; split; [exact Hc | exact Hr]).
    - intros [H1 H2]. unfold L1, L2 in H1, H2.
      destruct H1 as [Hlt1|[He1 Hr1]]; [ destruct H2 as [Hlt2|[He2 Hr2]]; lia | exact Hr1 ]. }
  assert (HReal : IsRealizer R (fun L => L = L1 \/ L = L2)).
  { constructor.
    - intros L [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HA HB].
        intros L [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split;
          [ apply (Hall L1); left; reflexivity | apply (Hall L2); right; reflexivity ]. }
  assert (Hcard : exists nc, cardinal (A -> A -> Prop) (fun L => L = L1 \/ L = L2) nc /\ nc <= 2).
  { destruct (classic (L1 = L2)) as [Heq | Hne].
    - exists 1. split; [|lia].
      replace (fun L => L = L1 \/ L = L2)
        with (Ensembles.Add (A -> A -> Prop) (Ensembles.Empty_set (A -> A -> Prop)) L1).
      + apply card_add; [apply card_empty | intro Hb; destruct Hb].
      + apply Extensionality_Ensembles; split; intros L HL.
        * destruct HL as [L' HL'|L' HL']; [destruct HL' | apply Singleton_inv in HL'; left; symmetry; exact HL'].
        * destruct HL as [-> | ->]; [right; constructor | rewrite <- Heq; right; constructor].
    - exists 2. split; [|lia].
      replace (fun L => L = L1 \/ L = L2)
        with (Ensembles.Add (A -> A -> Prop) (Ensembles.Add (A -> A -> Prop) (Ensembles.Empty_set (A -> A -> Prop)) L1) L2).
      + apply card_add; [ apply card_add; [apply card_empty | intro Hb; destruct Hb]
                        | intro Hb; destruct Hb as [L' Hb|L' Hb]; [destruct Hb | apply Singleton_inv in Hb; apply Hne; exact Hb] ].
      + apply Extensionality_Ensembles; split; intros L HL.
        * destruct HL as [L' [L'' HL''|L'' HL'']|L' HL'];
            [ destruct HL'' | apply Singleton_inv in HL''; left; symmetry; exact HL''
            | apply Singleton_inv in HL'; right; symmetry; exact HL' ].
        * destruct HL as [He | He]; subst L; [left; right; constructor | right; constructor]. }
  destruct Hcard as [nc [Hnc Hnc2]].
  pose proof (dimension_is_minimum Hdim (fun L => L = L1 \/ L = L2) nc HReal Hnc) as Hle. lia.
Qed.

(* ================================================================== *)
(* Frontier blocks are disjoint unions of chains, hence dim <= 2.     *)
(* ================================================================== *)

(* within one frontier, hb between two distinct events is a direct
   sender->receiver message *)
Lemma hb_same_index_msg :
  forall s, wf_schedule s ->
  forall (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = snd (proj1_sig y) ->
    ep_order (exec_of_schedule s) x y -> x <> y ->
    List.In (fst (proj1_sig x), fst (proj1_sig y))
            (nth (snd (proj1_sig x)) (sch_frontiers s) []).
Proof.
  intros s Hwf x y Hidx Hhb Hneq.
  (* Notation. *)
  set (k := snd (proj1_sig x)).
  (* Ranks pin the roles: rank x < rank y, with rank x = 2k, rank y = 2k+1. *)
  assert (Hrlt : rp_rank (desugar s) (proj1_sig x) < rp_rank (desugar s) (proj1_sig y)).
  { apply (hb_neq_rank_lt (desugar s) x y Hhb Hneq). }
  (* Step to a single edge then back. *)
  pose proof (clos_rt_rt1n _ _ _ _ Hhb) as Hrt1.
  inversion Hrt1 as [Heqxy | z yend Hedge Hrest Hye]; clear Hrt1.
  - exfalso. apply Hneq. exact Heqxy.
  - (* we have edge (desugar s) x z and clos_refl_trans_1n .. z y *)
    subst yend.
    (* rank z > rank x via the edge *)
    assert (Hedge' : edge (desugar s) x z) by exact Hedge.
    pose proof (rp_rank_mono (desugar s) x z Hedge') as Hxz.
    (* hb z y *)
    assert (Hzy : hb (desugar s) z y) by (apply clos_rt1n_rt; exact Hrest).
    pose proof (rank_hb_le (desugar s) z y Hzy) as Hzyle.
    (* rank x = 2k, rank y = 2k + cy with cy <= 1, so rank y <= 2k+1 *)
    destruct (desugar_rank_form s (proj1_sig x)) as [cx [Hcx Ex]].
    destruct (desugar_rank_form s (proj1_sig y)) as [cy [Hcy Ey]].
    (* All ranks are syntactically [desugar_rank s _] (record projection on a
       constructor reduces), so the following hypotheses share lia atoms. *)
    change (rp_rank (desugar s) (proj1_sig x)) with (desugar_rank s (proj1_sig x)) in Hxz, Hzyle, Hrlt.
    change (rp_rank (desugar s) (proj1_sig z)) with (desugar_rank s (proj1_sig z)) in Hxz, Hzyle.
    change (rp_rank (desugar s) (proj1_sig y)) with (desugar_rank s (proj1_sig y)) in Hzyle, Hrlt.
    assert (Hidx' : snd (proj1_sig y) = k) by (symmetry; exact Hidx).
    rewrite Hidx' in Ey.
    fold k in Ex.
    (* now 2k+cx < 2k+cy, so cx=0, cy=1, rank x = 2k, rank y = 2k+1 *)
    assert (Hcx0 : cx = 0) by lia.
    assert (Hcy1 : cy = 1) by lia.
    subst cx cy.
    (* rank x = 2k, rank y = 2k+1; rank x < rank z <= rank y = 2k+1, so rank z = 2k+1 = rank y *)
    assert (Hzeq : desugar_rank s (proj1_sig z) = desugar_rank s (proj1_sig y)) by lia.
    (* z = y: if z <> y, hb z y would give strict rank lt *)
    assert (Hzy_eq : z = y).
    { destruct (event_eq_dec (desugar s) z y) as [He | Hne]; [exact He|].
      exfalso. pose proof (hb_neq_rank_lt (desugar s) z y Hzy Hne) as Hc.
      change (rp_rank (desugar s) (proj1_sig z)) with (desugar_rank s (proj1_sig z)) in Hc.
      change (rp_rank (desugar s) (proj1_sig y)) with (desugar_rank s (proj1_sig y)) in Hc.
      lia. }
    subst z.
    (* So edge (desugar s) x y. *)
    clear Hrest Hzy Hzyle Hxz Hzeq.
    unfold edge in Hedge'.
    destruct x as [[px ix] Hx]. destruct y as [[py iy] Hy].
    simpl in *.
    destruct Hedge' as [[Hpeq HSeq] | [t [Hsend Hrecv]]].
    + (* program order: iy = S ix, but ix = iy = k, impossible *)
      exfalso. lia.
    + (* message disjunct *)
      change (op_at (desugar_prog s) px ix = Some (Send py t)) in Hsend.
      change (op_at (desugar_prog s) py iy = Some (Recv px t)) in Hrecv.
      apply op_at_desugar_inv in Hsend as [Hpx [Hix Hof]].
      pose proof (op_for_tag (nth ix (sch_frontiers s) []) px ix py t) as [Htag _].
      symmetry in Hof. specialize (Htag Hof). subst t.
      assert (Hfr : wf_frontier (sch_nprocs s) (nth ix (sch_frontiers s) []))
        by (apply Hwf; apply nth_In; exact Hix).
      pose proof (proj1 (op_for_send_iff (sch_nprocs s) _ px py ix Hfr) Hof) as Hin.
      (* ix = k = snd (px,ix) *)
      exact Hin.
Qed.

Definition fb_comp (s : Schedule) (pi : nat * nat) : nat :=
  match op_at (desugar_prog s) (fst pi) (snd pi) with
  | Some (Recv src _) => src
  | _ => fst pi
  end.

(* fb_comp of a Send/Local event is its own pid; of a Recv event is its source. *)
Lemma fb_comp_send :
  forall s p q k, p < sch_nprocs s -> k < length (sch_frontiers s) ->
    op_for (nth k (sch_frontiers s) []) p k = Send q k ->
    fb_comp s (p, k) = p.
Proof.
  intros s p q k Hp Hk Hof. unfold fb_comp. simpl.
  rewrite (op_at_desugar s p k Hp Hk). rewrite Hof. reflexivity.
Qed.

Lemma fb_comp_recv :
  forall s src p k, p < sch_nprocs s -> k < length (sch_frontiers s) ->
    op_for (nth k (sch_frontiers s) []) p k = Recv src k ->
    fb_comp s (p, k) = src.
Proof.
  intros s src p k Hp Hk Hof. unfold fb_comp. simpl.
  rewrite (op_at_desugar s p k Hp Hk). rewrite Hof. reflexivity.
Qed.

Lemma fb_comp_local :
  forall s p k, p < sch_nprocs s -> k < length (sch_frontiers s) ->
    op_for (nth k (sch_frontiers s) []) p k = Local ->
    fb_comp s (p, k) = p.
Proof.
  intros s p k Hp Hk Hof. unfold fb_comp. simpl.
  rewrite (op_at_desugar s p k Hp Hk). rewrite Hof. reflexivity.
Qed.

(* pid of a valid event is in range *)
Lemma event_pid_lt :
  forall s (x : ep_carrier (exec_of_schedule s)),
    fst (proj1_sig x) < sch_nprocs s.
Proof.
  intros s x. pose proof (proj2_sig x) as Hv.
  unfold Ensembles.In, ValidSet, Valid in Hv. destruct Hv as [Hfst _].
  rewrite <- nprocs_desugar. exact Hfst.
Qed.

(* The op of a within-block event, read back via op_for. *)
Lemma block_op_for :
  forall s (x : ep_carrier (exec_of_schedule s)),
    op_at (desugar_prog s) (fst (proj1_sig x)) (snd (proj1_sig x))
      = Some (op_for (nth (snd (proj1_sig x)) (sch_frontiers s) [])
                     (fst (proj1_sig x)) (snd (proj1_sig x))).
Proof.
  intros s x.
  apply (op_at_desugar s _ _ (event_pid_lt s x) (event_index_lt s x)).
Qed.

(* A frontier message [In (p,q)] orders the two index-k events carrying p and q. *)
Lemma msg_hb_events :
  forall s, wf_schedule s -> forall k
    (x y : ep_carrier (exec_of_schedule s)),
    snd (proj1_sig x) = k -> snd (proj1_sig y) = k ->
    List.In (fst (proj1_sig x), fst (proj1_sig y)) (nth k (sch_frontiers s) []) ->
    ep_order (exec_of_schedule s) x y.
Proof.
  intros s Hwf k x y Hkx Hky Hin.
  assert (Hpx : fst (proj1_sig x) < sch_nprocs s) by apply event_pid_lt.
  assert (Hpy : fst (proj1_sig y) < sch_nprocs s) by apply event_pid_lt.
  assert (Hk : k < length (sch_frontiers s)) by (rewrite <- Hkx; apply event_index_lt).
  pose proof (msg_step s Hwf (fst (proj1_sig x)) (fst (proj1_sig y)) k Hpx Hpy Hk Hin) as Hms.
  assert (Hex : x = mk_event s (fst (proj1_sig x)) k Hpx Hk).
  { apply event_eq_of_proj. rewrite mk_event_proj.
    rewrite (surjective_pairing (proj1_sig x)). rewrite Hkx. reflexivity. }
  assert (Hey : y = mk_event s (fst (proj1_sig y)) k Hpy Hk).
  { apply event_eq_of_proj. rewrite mk_event_proj.
    rewrite (surjective_pairing (proj1_sig y)). rewrite Hky. reflexivity. }
  rewrite Hex, Hey. exact Hms.
Qed.
