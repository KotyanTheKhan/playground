(* True N-way barriers: the fully-synchronized execution order `blo` (every index a
   full barrier) has dimension <= 2 for ANY process count -- addresses review finding 1. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 Schedule ScheduleWf SyncShape
                              DisjointChainsDim DimTwoGeneric.
Import ListNotations.
#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Lemma layered_chains_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (lay comp : A -> nat),
    (forall x y, lay x < lay y -> R x y) ->
    (forall x y, R x y -> lay x <= lay y) ->
    (forall x y, R x y -> lay x = lay y -> comp x = comp y) ->
    (forall x y, lay x = lay y -> comp x = comp y -> R x y \/ R y x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR lay comp Hbar Hresp Hrcomp Hchain d Hdim.
  set (L1 := fun x y : A => lay x < lay y \/
               (lay x = lay y /\ (comp x < comp y \/ (comp x = comp y /\ R x y)))).
  set (L2 := fun x y : A => lay x < lay y \/
               (lay x = lay y /\ (comp y < comp x \/ (comp x = comp y /\ R x y)))).
  assert (HL1 : IsLinearExtension R L1).
  { constructor.
    - constructor.
      + constructor.
        * (* poset_refl *) intro x. right. split; [reflexivity | right; split; [reflexivity | apply poset_refl]].
        * (* poset_antisym *) intros x y Hxy Hyx. unfold L1 in Hxy, Hyx.
          destruct Hxy as [Hl1|[Hle1 Hc1]]; destruct Hyx as [Hl2|[Hle2 Hc2]]; try lia.
          destruct Hc1 as [Hcl1|[Hce1 Hr1]]; destruct Hc2 as [Hcl2|[Hce2 Hr2]]; try lia.
          apply (poset_antisym _ _ Hr1 Hr2).
        * (* poset_trans *) intros x y z Hxy Hyz. unfold L1 in *.
          destruct Hxy as [Hl1|[Hle1 Hc1]]; destruct Hyz as [Hl2|[Hle2 Hc2]];
            try (left; lia).
          right. split; [lia|].
          destruct Hc1 as [Hcl1|[Hce1 Hr1]]; destruct Hc2 as [Hcl2|[Hce2 Hr2]];
            try (left; lia).
          right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
      + (* total_comparable *) intros x y. unfold L1.
        destruct (lt_eq_lt_dec (lay x) (lay y)) as [[Hlt|Heq]|Hgt].
        * left; left; exact Hlt.
        * destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hclt|Hceq]|Hcgt].
          -- left; right; split; [exact Heq | left; exact Hclt].
          -- destruct (Hchain x y Heq Hceq) as [Hr|Hr];
               [ left; right; split; [exact Heq | right; split; [exact Hceq | exact Hr]]
               | right; right; split; [symmetry; exact Heq | right; split; [symmetry; exact Hceq | exact Hr]] ].
          -- right; right; split; [symmetry; exact Heq | left; exact Hcgt].
        * right; left; exact Hgt.
    - (* linear_extends *) intros x y Hr. unfold L1.
      pose proof (Hresp x y Hr) as Hle. destruct (le_lt_eq_dec _ _ Hle) as [Hlt|Heq].
      + left; exact Hlt.
      + right. split; [exact Heq|]. right. split; [apply (Hrcomp x y Hr Heq) | exact Hr]. }
  assert (HL2 : IsLinearExtension R L2).
  { constructor.
    - constructor.
      + constructor.
        * (* poset_refl *) intro x. right. split; [reflexivity | right; split; [reflexivity | apply poset_refl]].
        * (* poset_antisym *) intros x y Hxy Hyx. unfold L2 in Hxy, Hyx.
          destruct Hxy as [Hl1|[Hle1 Hc1]]; destruct Hyx as [Hl2|[Hle2 Hc2]]; try lia.
          destruct Hc1 as [Hcl1|[Hce1 Hr1]]; destruct Hc2 as [Hcl2|[Hce2 Hr2]]; try lia.
          apply (poset_antisym _ _ Hr1 Hr2).
        * (* poset_trans *) intros x y z Hxy Hyz. unfold L2 in *.
          destruct Hxy as [Hl1|[Hle1 Hc1]]; destruct Hyz as [Hl2|[Hle2 Hc2]];
            try (left; lia).
          right. split; [lia|].
          destruct Hc1 as [Hcl1|[Hce1 Hr1]]; destruct Hc2 as [Hcl2|[Hce2 Hr2]];
            try (left; lia).
          right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
      + (* total_comparable *) intros x y. unfold L2.
        destruct (lt_eq_lt_dec (lay x) (lay y)) as [[Hlt|Heq]|Hgt].
        * left; left; exact Hlt.
        * destruct (lt_eq_lt_dec (comp x) (comp y)) as [[Hclt|Hceq]|Hcgt].
          -- right; right; split; [symmetry; exact Heq | left; exact Hclt].
          -- destruct (Hchain x y Heq Hceq) as [Hr|Hr];
               [ left; right; split; [exact Heq | right; split; [exact Hceq | exact Hr]]
               | right; right; split; [symmetry; exact Heq | right; split; [symmetry; exact Hceq | exact Hr]] ].
          -- left; right; split; [exact Heq | left; exact Hcgt].
        * right; left; exact Hgt.
    - (* linear_extends *) intros x y Hr. unfold L2.
      pose proof (Hresp x y Hr) as Hle. destruct (le_lt_eq_dec _ _ Hle) as [Hlt|Heq].
      + left; exact Hlt.
      + right. split; [exact Heq|]. right. split; [apply (Hrcomp x y Hr Heq) | exact Hr]. }
  assert (Hcap : forall x y, R x y <-> (L1 x y /\ L2 x y)).
  { intros x y. split.
    - intro Hr. pose proof (Hresp x y Hr) as Hle. destruct (le_lt_eq_dec _ _ Hle) as [Hlt|Heq].
      + split; left; exact Hlt.
      + assert (Hc : comp x = comp y) by (apply (Hrcomp x y Hr Heq)).
        split; right; split; try exact Heq; right; split; assumption.
    - intros [H1 H2]. unfold L1, L2 in H1, H2.
      destruct (lt_eq_lt_dec (lay x) (lay y)) as [[Hlt|Heq]|Hgt].
      + apply (Hbar x y Hlt).
      + destruct H1 as [Hl1|[_ Hc1]]; [lia|]. destruct H2 as [Hl2|[_ Hc2]]; [lia|].
        destruct Hc1 as [Hcl1|[Hce1 Hr1]]; [ destruct Hc2 as [Hcl2|[Hce2 Hr2]]; lia | exact Hr1 ].
      + exfalso. destruct H1 as [Hl1|[Hle1 _]]; lia. }
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

(* hb respects the index, via the rank 2*idx + c *)
Lemma hb_idx_le :
  forall s (x y : ep_carrier (exec_of_schedule s)),
    ep_order (exec_of_schedule s) x y ->
    snd (proj1_sig x) <= snd (proj1_sig y).
Proof.
  intros s x y H.
  pose proof (rank_hb_le (desugar s) x y H) as Hr.
  change (rp_rank (desugar s) (proj1_sig x)) with (desugar_rank s (proj1_sig x)) in Hr.
  change (rp_rank (desugar s) (proj1_sig y)) with (desugar_rank s (proj1_sig y)) in Hr.
  destruct (desugar_rank_form s (proj1_sig x)) as [cx [Hcx Ex]].
  destruct (desugar_rank_form s (proj1_sig y)) as [cy [Hcy Ey]].
  rewrite Ex, Ey in Hr. lia.
Qed.

(* the fully-synchronized (true-barrier) order: every index a full barrier,
   real intra-layer message order as the within-layer tiebreak *)
Definition blo (s : Schedule)
  : ep_carrier (exec_of_schedule s) -> ep_carrier (exec_of_schedule s) -> Prop :=
  fun x y => snd (proj1_sig x) < snd (proj1_sig y)
          \/ (snd (proj1_sig x) = snd (proj1_sig y) /\ ep_order (exec_of_schedule s) x y).

#[export] Instance blo_IsPoset : forall s, IsPoset (ep_carrier (exec_of_schedule s)) (blo s).
Proof.
  intro s. constructor.
  - intro x. right. split; [reflexivity | apply poset_refl].
  - intros x y Hxy Hyx. unfold blo in Hxy, Hyx.
    destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyx as [Hlt2|[He2 Hr2]];
      try lia. apply (poset_antisym _ _ Hr1 Hr2).
  - intros x y z Hxy Hyz. unfold blo in *.
    destruct Hxy as [Hlt1|[He1 Hr1]]; destruct Hyz as [Hlt2|[He2 Hr2]].
    + left; lia.
    + left; lia.
    + left; lia.
    + right; split; [lia | apply (poset_trans _ _ _ Hr1 Hr2)].
Qed.

Theorem barrier_execution_dim_le2 :
  forall s, wf_schedule s -> forall d, PosetDimension (blo s) d -> d <= 2.
Proof.
  intros s Hwf d Hdim.
  refine (layered_chains_dim_le2 (blo s)
           (fun x => snd (proj1_sig x))
           (fun x => fb_comp s (proj1_sig x))
           _ _ _ _ d Hdim).
  - (* full barrier *) intros x y Hlt. left. exact Hlt.
  - (* respects layers *) intros x y [Hlt|[He _]]; lia.
  - (* respects comp within layer *) intros x y Hblo Heq. unfold blo in Hblo.
    destruct Hblo as [Hlt|[_ Hhb]]; [lia|].
    exact (fb_comp_eq_of_hb s Hwf x y Heq Hhb).
  - (* within-layer chain *) intros x y Heq Hcomp.
    destruct (hb_or_of_fb_comp_eq s Hwf x y Heq Hcomp) as [Hhb|Hhb].
    + left. right. split; [exact Heq | exact Hhb].
    + right. right. split; [symmetry; exact Heq | exact Hhb].
Qed.

(* exact dimension: a barrier execution that is not a chain has dimension exactly 2 *)
Theorem blo_dim_eq_2 :
  forall s, wf_schedule s ->
    (exists x y : ep_carrier (exec_of_schedule s), Incomparable (blo s) x y) ->
    forall d, PosetDimension (blo s) d -> d = 2.
Proof.
  intros s Hwf [x [y Hinc]] d Hdim.
  pose proof (barrier_execution_dim_le2 s Hwf d Hdim) as Hle.
  pose proof (dim_ge_2_of_incomparable (blo s) x y Hinc d Hdim) as Hge.
  lia.
Qed.
