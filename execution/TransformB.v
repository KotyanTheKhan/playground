(* Transformation B: a 2-process (2-chain-covered) block has dimension <= 2;
   block replacement preserves the fully-sync execution's dim <= 2. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                           ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems WidthBound WidthExists.
From Dilworth Require Import Definitions WidthLowerBound.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDim2 DimTwoGeneric ChainDim.

(** A finite poset whose carrier is covered by two chains has dimension <= 2.

    Route: dim <= width (dimension_le_width); and width <= 2 because the
    two chains form a chain cover of cardinality <= 2, so by the
    chain/antichain pigeonhole no antichain can have 3 distinct elements. *)
Lemma two_chain_cover_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (C0 C1 : Ensemble A) (n : nat),
    cardinal A (Full_set A) n -> Inhabited A (Full_set A) ->
    IsChain R C0 -> IsChain R C1 ->
    (forall x, Ensembles.In A (Full_set A) x ->
        Ensembles.In A C0 x \/ Ensembles.In A C1 x) ->
    forall d, PosetDimension R d -> d <= 2.
Proof.
  intros A R HR C0 C1 n Hcard Hinhab HC0 HC1 Hcov d Hdim.
  destruct (width_exists R n Hcard Hinhab) as [w [HW]].
  pose proof (@dimension_le_width A R HR n d w Hcard Hdim HW) as Hdw.
  assert (Hw2 : w <= 2).
  { (* the two chains form a chain cover of the full carrier *)
    set (cover := fun c : Ensemble A => c = C0 \/ c = C1).
    assert (Hcc : IsChainCover R (Full_set A) cover).
    { constructor.
      - intros c [-> | ->]; assumption.
      - intros c _ x _. constructor.
      - intros x _. destruct (Hcov x (Full_intro _ _)) as [H0 | H1];
          [ exists C0; split; [left; reflexivity | exact H0]
          | exists C1; split; [right; reflexivity | exact H1] ]. }
    destruct (le_lt_dec w 2) as [Hle | Hgt]; [exact Hle | exfalso].
    (* unpack the maximum antichain [la] of size w *)
    destruct HW as [la Hla].
    destruct Hla as [Hla_anti Hla_incl Hla_card Hla_max].
    (* the cover has cardinality at most 2 *)
    assert (Hcov_card : exists ncov, cardinal (Ensemble A) cover ncov /\ ncov <= 2).
    { destruct (classic (C0 = C1)) as [Heq | Hne].
      - exists 1. split; [|lia].
        replace cover with (Add (Ensemble A) (Empty_set _) C0).
        + apply card_add; [apply card_empty | intro Hb; destruct Hb].
        + apply Extensionality_Ensembles; split; intros c Hc.
          * destruct Hc as [c' Hc' | c' Hc'];
              [destruct Hc' | apply Singleton_inv in Hc'; left; symmetry; exact Hc'].
          * change (c = C0 \/ c = C1) in Hc; destruct Hc as [-> | ->];
              [right; constructor | rewrite <- Heq; right; constructor].
      - exists 2. split; [|lia].
        replace cover with (Add (Ensemble A) (Add (Ensemble A) (Empty_set _) C0) C1).
        + apply card_add.
          * apply card_add; [apply card_empty | intro Hb; destruct Hb].
          * intro Hb. destruct Hb as [c Hb | c Hb];
              [destruct Hb | apply Singleton_inv in Hb; apply Hne; exact Hb].
        + apply Extensionality_Ensembles; split; intros c Hc.
          * destruct Hc as [c' Hc' | c' Hc'];
              [ destruct Hc' as [c'' Hc'' | c'' Hc''];
                [destruct Hc'' | apply Singleton_inv in Hc''; left; symmetry; exact Hc'']
              | apply Singleton_inv in Hc'; right; symmetry; exact Hc' ].
          * change (c = C0 \/ c = C1) in Hc; destruct Hc as [-> | ->];
              [left; right; constructor | right; constructor]. }
    destruct Hcov_card as [ncov [Hncov Hncov2]].
    (* pigeonhole: w > ncov antichain elements into <= 2 chains => two in one chain *)
    destruct (pigeonhole_chains_antichains R (Full_set A) cover la ncov w
                Hcc Hla_anti Hla_incl Hncov Hla_card ltac:(lia))
      as [x [y [c [Hx [Hy [Hc [Hcx [Hcy Hxy]]]]]]]].
    (* c is a chain; x,y in c are comparable; x,y in the antichain are equal: contra *)
    pose proof (chain_cover_chains R (IsChainCover:=Hcc) c Hc) as Hchain.
    pose proof (chain_comparable R (IsChain:=Hchain) x y Hcx Hcy) as Hcomp.
    pose proof (antichain_incomparable R (IsAntichain:=Hla_anti) x y Hx Hy Hcomp) as Heqxy.
    exact (Hxy Heqxy). }
  lia.
Qed.

(* concrete 2-process block: process 0 chain a0<a1, process 1 chain b0<b1, a's || b's *)
Inductive B2 : Set := a0 | a1 | b0 | b1.

Definition B2_R (x y : B2) : Prop :=
  x = y \/ (x = a0 /\ y = a1) \/ (x = b0 /\ y = b1).

#[export] Instance B2_poset : IsPoset B2 B2_R.
Proof.
  constructor.
  - intro x. left. reflexivity.
  - intros x y Hxy Hyx.
    unfold B2_R in *.
    destruct Hxy as [E|[[E1 E2]|[E1 E2]]]; subst; try reflexivity;
      destruct Hyx as [E'|[[E1' E2']|[E1' E2']]]; subst; try reflexivity;
      try discriminate.
  - intros x y z Hxy Hyz.
    unfold B2_R in *.
    destruct Hxy as [E|[[E1 E2]|[E1 E2]]]; subst;
      [ assumption | | ];
      (destruct Hyz as [E'|[[E1' E2']|[E1' E2']]]; subst; try discriminate);
      [ right; left; split; reflexivity | right; right; split; reflexivity ].
Qed.

Definition B2_C0 : Ensemble B2 := fun z => z = a0 \/ z = a1.
Definition B2_C1 : Ensemble B2 := fun z => z = b0 \/ z = b1.

Lemma B2_C0_chain : IsChain B2_R B2_C0.
Proof.
  constructor.
  - exists a0. left. reflexivity.
  - intros x y Hx Hy.
    unfold Ensembles.In, B2_C0 in Hx, Hy.
    destruct Hx as [-> | ->]; destruct Hy as [-> | ->];
      (left; left; reflexivity) || (left; right; left; split; reflexivity)
      || (right; right; left; split; reflexivity).
Qed.

Lemma B2_C1_chain : IsChain B2_R B2_C1.
Proof.
  constructor.
  - exists b0. left. reflexivity.
  - intros x y Hx Hy.
    unfold Ensembles.In, B2_C1 in Hx, Hy.
    destruct Hx as [-> | ->]; destruct Hy as [-> | ->];
      (left; left; reflexivity) || (left; right; right; split; reflexivity)
      || (right; right; right; split; reflexivity).
Qed.

Lemma B2_Hfin : cardinal B2 (Full_set B2) 4.
Proof.
  replace (Full_set B2)
    with (Add B2 (Add B2 (Add B2 (Add B2 (Empty_set B2) a0) a1) b0) b1).
  - apply card_add; [ apply card_add; [ apply card_add; [ apply card_add;
      [ apply card_empty | intro Hb; destruct Hb ]
      | intro Hb; repeat (apply Add_inv in Hb; destruct Hb as [Hb|Hb]); try discriminate; try (destruct Hb) ]
      | intro Hb; repeat (apply Add_inv in Hb; destruct Hb as [Hb|Hb]); try discriminate; try (destruct Hb) ]
      | intro Hb; repeat (apply Add_inv in Hb; destruct Hb as [Hb|Hb]); try discriminate; try (destruct Hb) ].
  - apply Extensionality_Ensembles; split; intros x _.
    + constructor.
    + destruct x; [ left;left;left;right;constructor | left;left;right;constructor
                  | left;right;constructor | right;constructor ].
Qed.

Lemma B2_inhab : Inhabited B2 (Full_set B2).
Proof. exists a0. constructor. Qed.

Lemma B2_cover : forall x, Ensembles.In B2 (Full_set B2) x ->
  Ensembles.In B2 B2_C0 x \/ Ensembles.In B2 B2_C1 x.
Proof.
  intros x _. destruct x;
    [ left; left; reflexivity | left; right; reflexivity
    | right; left; reflexivity | right; right; reflexivity ].
Qed.

Lemma B2_dim_le2 : forall d, PosetDimension B2_R d -> d <= 2.
Proof.
  apply (two_chain_cover_dim_le2 B2_R B2_C0 B2_C1 4
           B2_Hfin B2_inhab B2_C0_chain B2_C1_chain B2_cover).
Qed.

(* Transformation B's "one local modification": the simplified block is a single chain.
   Modelled as a 2-chain cover whose second chain is the singleton {p1} (IsChain
   requires nonemptiness, so an empty second chain is not permitted). *)
Inductive B2s : Set := p0 | p1.
Definition B2s_R (x y : B2s) : Prop := x = y \/ (x = p0 /\ y = p1).

#[export] Instance B2s_poset : IsPoset B2s B2s_R.
Proof.
  constructor.
  - intro x. left. reflexivity.
  - intros x y Hxy Hyx. unfold B2s_R in *.
    destruct Hxy as [E|[E1 E2]]; subst; try reflexivity;
      destruct Hyx as [E'|[E1' E2']]; subst; try reflexivity; try discriminate.
  - intros x y z Hxy Hyz. unfold B2s_R in *.
    destruct Hxy as [E|[E1 E2]]; subst;
      [ assumption | ].
    destruct Hyz as [E'|[E1' E2']]; subst; try discriminate.
    right; split; reflexivity.
Qed.

Definition B2s_C0 : Ensemble B2s := fun z => z = p0 \/ z = p1.
Definition B2s_C1 : Ensemble B2s := fun z => z = p1.

Lemma B2s_C0_chain : IsChain B2s_R B2s_C0.
Proof.
  constructor.
  - exists p0. left. reflexivity.
  - intros x y Hx Hy. unfold Ensembles.In, B2s_C0 in Hx, Hy.
    destruct Hx as [-> | ->]; destruct Hy as [-> | ->];
      (left; left; reflexivity) || (left; right; split; reflexivity)
      || (right; right; split; reflexivity).
Qed.

Lemma B2s_C1_chain : IsChain B2s_R B2s_C1.
Proof.
  constructor.
  - exists p1. reflexivity.
  - intros x y Hx Hy. unfold Ensembles.In, B2s_C1 in Hx, Hy.
    subst. left. left. reflexivity.
Qed.

Lemma B2s_Hfin : cardinal B2s (Full_set B2s) 2.
Proof.
  replace (Full_set B2s) with (Add B2s (Add B2s (Empty_set B2s) p0) p1).
  - apply card_add; [ apply card_add; [ apply card_empty | intro Hb; destruct Hb ]
                    | intro Hb; repeat (apply Add_inv in Hb; destruct Hb as [Hb|Hb]); try discriminate; try (destruct Hb) ].
  - apply Extensionality_Ensembles; split; intros x _;
      [ constructor | destruct x; [ left;right;constructor | right;constructor ] ].
Qed.

Lemma B2s_inhab : Inhabited B2s (Full_set B2s).
Proof. exists p0. constructor. Qed.

Lemma B2s_cover : forall x, Ensembles.In B2s (Full_set B2s) x ->
  Ensembles.In B2s B2s_C0 x \/ Ensembles.In B2s B2s_C1 x.
Proof.
  intros x _. left. destruct x; [ left | right ]; reflexivity.
Qed.

Lemma B2s_dim_le2 : forall d, PosetDimension B2s_R d -> d <= 2.
Proof.
  apply (two_chain_cover_dim_le2 B2s_R B2s_C0 B2s_C1 2
           B2s_Hfin B2s_inhab B2s_C0_chain B2s_C1_chain B2s_cover).
Qed.

Lemma transform_B_preserves_dim2 :
  forall E blocks,
    IsFullySync E blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (sub_order E blk) d) /\ d <= 2) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof. intros E blocks Hfs Hblk. exact (fully_sync_dim_le2 E blocks Hfs Hblk). Qed.
