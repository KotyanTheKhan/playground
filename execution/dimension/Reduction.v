(* dimension-preserving / reducing maps between posets *)

From Stdlib Require Import Ensembles Finite_sets Arith Lia Classical Description Image ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimIso Ordinal.

(** * Reduction relations between posets

    [PosetDimension R d] is a typeclass (lives in [Type]), so to embed it in
    [Prop]-valued definitions and statements we wrap it with [inhabited].

    Notation: [dim_at R d] abbreviates [inhabited (PosetDimension R d)]. *)

Local Notation dim_at R d := (inhabited (PosetDimension R d)).

(** [PreservesDim A R B S]: the two posets share the same Dushnik–Miller
    dimension (every [d] is a dimension of [R] iff it is a dimension of [S]). *)
Definition PreservesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall d, dim_at R d <-> dim_at S d.

(** [ReducesDim A R B S]: dim R ≤ dim S.  The witnesses are term-level
    instances so [PosetDimension] stays in [Type]. *)
Definition ReducesDim
  (A : Type) (R : A -> A -> Prop) (B : Type) (S : B -> B -> Prop) : Prop :=
  forall dR dS, PosetDimension R dR -> PosetDimension S dS -> dR <= dS.

(** ** Basic algebra of [PreservesDim] *)

Lemma preserves_dim_refl : forall A (R : A -> A -> Prop), PreservesDim A R A R.
Proof.
  intros A R. unfold PreservesDim. intro d. tauto.
Qed.

Lemma preserves_dim_sym :
  forall A R B S, PreservesDim A R B S -> PreservesDim B S A R.
Proof.
  intros A R B S Hpres. unfold PreservesDim in *. intro d. rewrite Hpres. tauto.
Qed.

Lemma preserves_dim_trans :
  forall A R B S C T,
    PreservesDim A R B S -> PreservesDim B S C T -> PreservesDim A R C T.
Proof.
  intros A R B S C T H1 H2. unfold PreservesDim in *. intro d.
  rewrite H1. rewrite H2. tauto.
Qed.

(** ** Basic algebra of [ReducesDim] *)

Lemma reduces_dim_refl :
  forall A (R : A -> A -> Prop) `{IsPoset A R}, ReducesDim A R A R.
Proof.
  intros A R HPos. unfold ReducesDim.
  intros dR dS HdR HdS.
  pose proof (posdim_unique A R dR dS HdR HdS) as Heq.
  lia.
Qed.

Lemma reduces_dim_trans :
  forall A R B S C T `{IsPoset B S},
    (exists dS, dim_at S dS) ->
    ReducesDim A R B S -> ReducesDim B S C T -> ReducesDim A R C T.
Proof.
  intros A R B S C T HSPos Hex H1 H2.
  destruct Hex as [dS [HdS]].
  unfold ReducesDim in *.
  intros dR dT HdR HdT.
  specialize (H1 dR dS HdR HdS).
  specialize (H2 dS dT HdS HdT).
  lia.
Qed.

(** ** Relationship between [PreservesDim] and [ReducesDim] *)

Lemma preserves_dim_reduces :
  forall A R B S `{IsPoset A R} `{IsPoset B S},
    (exists dS, dim_at S dS) ->
    PreservesDim A R B S -> ReducesDim A R B S.
Proof.
  intros A R B S HRA HSB Hex Hpres.
  destruct Hex as [dS [HdS]].
  unfold ReducesDim. intros dR dS' HdR HdS'.
  assert (HinhR : dim_at R dR) by exact (inhabits HdR).
  assert (HinhS_dR : dim_at S dR) by (apply (Hpres dR); exact HinhR).
  destruct HinhS_dR as [HdR_S].
  pose proof (posdim_unique B S dR dS' HdR_S HdS') as Heq.
  lia.
Qed.

(** ** Dim ≤ 2 corollaries *)

Lemma preserves_dim2 :
  forall A R B S,
    PreservesDim A R B S ->
    ((exists d, dim_at R d /\ d <= 2) <-> (exists d, dim_at S d /\ d <= 2)).
Proof.
  intros A R B S Hpres. split.
  - intros [d [Hd Hle]].
    exists d. split.
    + apply (Hpres d). exact Hd.
    + exact Hle.
  - intros [d [Hd Hle]].
    exists d. split.
    + apply (Hpres d). exact Hd.
    + exact Hle.
Qed.

Lemma reduces_dim2 :
  forall A R B S,
    ReducesDim A R B S ->
    (exists dR, dim_at R dR) ->
    (exists d, dim_at S d /\ d <= 2) ->
    (exists d, dim_at R d /\ d <= 2).
Proof.
  intros A R B S Hred Hex [dS [HdS Hle]].
  destruct Hex as [dR [HdR]].
  destruct HdS as [HdS].
  pose proof (Hred dR dS HdR HdS) as Hle2.
  exists dR. split.
  - exact (inhabits HdR).
  - lia.
Qed.

(** ** Reduction instances *)

(** An order-isomorphism preserves dimension exactly. *)
Lemma iso_preserves_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B) (g : B -> A),
    (forall a, g (f a) = a) -> (forall b, f (g b) = b) ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    PreservesDim A R B S.
Proof.
  unfold PreservesDim.
  intros A B R S HA HB f g Hgf Hfg Hiso d.
  split.
  - intros [HR]. apply inhabits.
    exact (dimension_iso A B R S f g Hgf Hfg Hiso d HR).
  - intros [HS]. apply inhabits.
    assert (Hiso' : forall b b', S b b' <-> R (g b) (g b')).
    { intros b b'. split.
      - intro Hb. apply (proj2 (Hiso (g b) (g b'))).
        rewrite Hfg, Hfg. exact Hb.
      - intro Hb. apply (proj1 (Hiso (g b) (g b'))) in Hb.
        rewrite Hfg, Hfg in Hb. exact Hb. }
    exact (dimension_iso B A S R g f Hfg Hgf Hiso' d HS).
Qed.

(** Restricting a poset to a subset can only lower (or preserve) dimension. *)
Lemma subposet_reduces_dim :
  forall (B : Type) (S : B -> B -> Prop) `{IsPoset B S} (Sub : Ensemble B),
    ReducesDim {z | Ensembles.In _ Sub z}
               (fun x y => S (proj1_sig x) (proj1_sig y)) B S.
Proof.
  unfold ReducesDim.
  intros B S HS Sub dR dS HdR HdS.
  destruct (subposet_dimension_le S Sub dS HdS) as [d_q [Hinh Hle]].
  destruct Hinh as [Hq].
  pose proof (subtype_is_poset S Sub) as Hsub_pos.
  pose proof (posdim_unique {z | Ensembles.In _ Sub z}
                (fun x y => S (proj1_sig x) (proj1_sig y))
                dR d_q HdR Hq) as Heq.
  lia.
Qed.

(** An order-embedding (injective, order-reflecting/preserving map) can only
    lower (or preserve) dimension: dim R ≤ dim S.

    We factor [f] through its image subposet.  On
    [Img := Im A B (Full_set A) f] the carrier [{b | In B Img b}] is order-iso
    to [A] (via [f] and the unique preimage of each image point), so
    [iso_preserves_dim] transports a dimension of [R] to the image subposet;
    then [subposet_reduces_dim] bounds it by dim S. *)
Lemma embedding_reduces_dim :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         `{IsPoset A R} `{IsPoset B S} (f : A -> B),
    (forall a a', a <> a' -> f a <> f a') ->
    (forall a a', R a a' <-> S (f a) (f a')) ->
    ReducesDim A R B S.
Proof.
  intros A B R S HA HB f Hinj Hmono.
  (* injectivity in the usual (contrapositive) form *)
  assert (Hinj' : forall a a', f a = f a' -> a = a').
  { intros a a' Heq. destruct (classic (a = a')) as [E | NE]; [exact E |].
    exfalso. apply (Hinj a a' NE Heq). }
  set (Img := Im A B (Full_set A) f).
  set (Sub := {b : B | Ensembles.In B Img b}).
  set (Ssub := fun x y : Sub => S (proj1_sig x) (proj1_sig y)).
  (* image membership of every f a *)
  assert (Hmem : forall a, Ensembles.In B Img (f a)).
  { intro a. apply Im_intro with (x := a); [constructor | reflexivity]. }
  (* forward iso map A -> Sub *)
  set (toSub := fun a : A => exist (fun b => Ensembles.In B Img b) (f a) (Hmem a)).
  (* unique preimage of an image point *)
  assert (Hpre : forall b : B, Ensembles.In B Img b ->
                   exists! a : A, f a = b).
  { intros b Hb. destruct Hb as [a _ b' Hfa]. subst b'.
    exists a. split; [reflexivity |]. intros a' Hf'. apply Hinj'. symmetry. exact Hf'. }
  (* recovery map Sub -> A via constructive definite description *)
  set (fromSub := fun s : Sub =>
        proj1_sig (constructive_definite_description _
                     (Hpre (proj1_sig s) (proj2_sig s)))).
  (* the recovered a satisfies f (fromSub s) = proj1_sig s *)
  assert (Hfrom : forall s : Sub, f (fromSub s) = proj1_sig s).
  { intro s. unfold fromSub.
    exact (proj2_sig (constructive_definite_description _
                        (Hpre (proj1_sig s) (proj2_sig s)))). }
  (* round-trip 1: fromSub (toSub a) = a *)
  assert (Hgf : forall a : A, fromSub (toSub a) = a).
  { intro a. apply Hinj'.
    change (f (fromSub (toSub a)) = f a).
    rewrite (Hfrom (toSub a)). reflexivity. }
  (* round-trip 2: toSub (fromSub s) = s *)
  assert (Hfg : forall s : Sub, toSub (fromSub s) = s).
  { intro s. unfold toSub.
    pose proof (Hfrom s) as Heq.
    destruct s as [b Hb]. simpl in Heq.
    generalize (Hmem (fromSub (exist (fun b0 => Ensembles.In B Img b0) b Hb))).
    rewrite Heq. intro Hb'. f_equal. apply proof_irrelevance. }
  (* order correspondence R a a' <-> Ssub (toSub a) (toSub a') *)
  assert (Hord : forall a a', R a a' <-> Ssub (toSub a) (toSub a')).
  { intros a a'. unfold Ssub, toSub. simpl. exact (Hmono a a'). }
  (* the subtype poset instance *)
  pose proof (subtype_is_poset S Img) as HsubPos.
  (* now bound any dR by dS *)
  unfold ReducesDim. intros dR dS HdR HdS.
  (* transport dR to the image subposet at the [Type] level (via dimension_iso),
     so the result can feed the [Type]-valued subposet reduction. *)
  assert (HdR_sub : PosetDimension Ssub dR).
  { exact (@dimension_iso A Sub R Ssub HA HsubPos toSub fromSub Hgf Hfg Hord dR HdR). }
  (* subposet reduction: Ssub is the subtype restriction of S to Img *)
  exact (subposet_reduces_dim B S Img dR dS HdR_sub HdS).
Qed.
