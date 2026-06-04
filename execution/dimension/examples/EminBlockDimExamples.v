(* #66: the E_min {b,c,d} block has dimension exactly 2 (this file: the block
   dimension via a bare 3-element poset + dimension_iso). Test-only. *)
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Finite Edges Rank Poset Schedule
                              FinPosetDimSurgery FinPosetDim FinExtremumDim
                              DimIso DimBridge DimTwoGeneric
                              DimExamples FrontierExamples.

(* hb poset instance on E_min's carrier (needed for poset_refl on ep_order). *)
#[local] Existing Instance hb_IsPoset.

Inductive T3 : Set := B3 | C3 | D3.
Definition bcd_R (x y : T3) : Prop := x = y \/ (x = C3 /\ y = D3).

#[export] Instance bcd_poset : IsPoset T3 bcd_R.
Proof.
  constructor.
  - intro x. left. reflexivity.
  - intros x y [Hxy|[Hx Hy]] [Hyx|[Hy' Hx']]; subst; try reflexivity; try discriminate.
  - intros x y z [Hxy|[Hx Hy]] [Hyz|[Hy' Hz]]; subst; try (left; reflexivity);
      try (right; split; reflexivity); try discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Two linear extensions + dim 2 (BARE record via dim2_record)         *)
(* ------------------------------------------------------------------ *)

Definition kB (x : T3) : nat := match x with B3 => 0 | C3 => 1 | D3 => 2 end.
Definition kC (x : T3) : nat := match x with C3 => 0 | D3 => 1 | B3 => 2 end.
Definition M1 (x y : T3) : Prop := kB x <= kB y.
Definition M2 (x y : T3) : Prop := kC x <= kC y.

Lemma M1_linext : IsLinearExtension bcd_R M1.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold M1. lia.
      * intros x y Hxy Hyx. unfold M1 in *.
        destruct x, y; simpl in *; try reflexivity; lia.
      * intros x y z Hxy Hyz. unfold M1 in *. lia.
    + intros x y. unfold M1. destruct x, y; simpl; lia.
  - intros x y [->|[Hx Hy]]; subst; unfold M1; simpl; lia.
Qed.

Lemma M2_linext : IsLinearExtension bcd_R M2.
Proof.
  constructor.
  - constructor.
    + constructor.
      * intro x. unfold M2. lia.
      * intros x y Hxy Hyx. unfold M2 in *.
        destruct x, y; simpl in *; try reflexivity; lia.
      * intros x y z Hxy Hyz. unfold M2 in *. lia.
    + intros x y. unfold M2. destruct x, y; simpl; lia.
  - intros x y [->|[Hx Hy]]; subst; unfold M2; simpl; lia.
Qed.

Lemma bcd_cap : forall x y, bcd_R x y <-> (M1 x y /\ M2 x y).
Proof.
  intros x y. split.
  - intros [->|[Hx Hy]]; subst; unfold M1, M2; simpl; lia.
  - intros [H1 H2]. unfold M1, M2 in *.
    destruct x, y; simpl in *;
      try (left; reflexivity);
      try (right; split; reflexivity);
      try lia.
Qed.

Lemma bcd_incomp : Incomparable bcd_R B3 C3.
Proof.
  unfold Incomparable, bcd_R.
  intros [H|H].
  - destruct H as [H|[H1 H2]]; discriminate.
  - destruct H as [H|[H1 H2]]; discriminate.
Qed.

Definition bcd_dim2 : PosetDimension bcd_R 2 :=
  dim2_record bcd_R M1 M2 B3 C3 M1_linext M2_linext bcd_cap bcd_incomp.

(* ------------------------------------------------------------------ *)
(* Transport onto the Umin subtype                                     *)
(* ------------------------------------------------------------------ *)

Lemma inU_b : Ensembles.In _ Umin ev_b.
Proof. unfold Ensembles.In, Umin, ev_b. simpl. discriminate. Qed.
Lemma inU_c : Ensembles.In _ Umin ev_c.
Proof. unfold Ensembles.In, Umin, ev_c. simpl. discriminate. Qed.
Lemma inU_d : Ensembles.In _ Umin ev_d.
Proof. unfold Ensembles.In, Umin, ev_d. simpl. discriminate. Qed.

Definition UU := {z : ep_carrier E_min | Ensembles.In _ Umin z}.

(* IsPoset instance on the subtype carrier (needed by dimension_iso / poset_refl). *)
#[local] Instance UU_poset : IsPoset UU (fin_sub_order (ep_order E_min) Umin) :=
  fin_sub_order_poset (ep_order E_min) Umin.
Definition f3 (t : T3) : UU :=
  match t with
  | B3 => exist _ ev_b inU_b
  | C3 => exist _ ev_c inU_c
  | D3 => exist _ ev_d inU_d
  end.
Definition g3 (u : UU) : T3 :=
  match proj1_sig (proj1_sig u) with
  | (0,1) => B3
  | (1,0) => C3
  | _ => D3
  end.

Lemma g3_f3 : forall t, g3 (f3 t) = t.
Proof. intro t; destruct t; vm_compute; reflexivity. Qed.

Lemma f3_g3 : forall u, f3 (g3 u) = u.
Proof.
  intros [z Hz].
  pose proof (valid_event_min_cases z) as Hcases. simpl in Hcases.
  unfold Ensembles.In, Umin in Hz.
  (* Reduce g3 (exist _ z Hz): its result depends only on proj1_sig z.
     In each surviving case g3 = B3/C3/D3 and f3 of that is exist _ ev_? inU_?,
     so the goal becomes a subtype equality exist _ ev_? _ = exist _ z Hz,
     discharged by subset_eq_compat with ev_? = z. *)
  destruct Hcases as [H00 | [H01 | [H10 | H11]]].
  - exfalso. apply Hz. exact H00.
  - assert (Hg : g3 (exist _ z Hz) = B3).
    { unfold g3. simpl. rewrite H01. reflexivity. }
    rewrite Hg. unfold f3. apply subset_eq_compat.
    symmetry. exact (eq_ev_b z H01).
  - assert (Hg : g3 (exist _ z Hz) = C3).
    { unfold g3. simpl. rewrite H10. reflexivity. }
    rewrite Hg. unfold f3. apply subset_eq_compat.
    symmetry. exact (eq_ev_c z H10).
  - assert (Hg : g3 (exist _ z Hz) = D3).
    { unfold g3. simpl. rewrite H11. reflexivity. }
    rewrite Hg. unfold f3. apply subset_eq_compat.
    symmetry. exact (eq_ev_d z H11).
Qed.

(* ------------------------------------------------------------------ *)
(* The three needed refutations of ep_order on off-diagonal pairs.     *)
(* incomp_b_c already gives (B3,C3)/(C3,B3); prove the other three.    *)
(* ------------------------------------------------------------------ *)

Lemma not_hb_b_d : ~ ep_order E_min ev_b ev_d.
Proof.
  intro H. apply hb_min_realizer in H. destruct H as [_ H2].
  unfold L2_min in H2. vm_compute in H2. lia.
Qed.

Lemma not_hb_d_b : ~ ep_order E_min ev_d ev_b.
Proof.
  intro H. apply hb_min_realizer in H. destruct H as [H1 _].
  unfold L1_min in H1. vm_compute in H1. lia.
Qed.

Lemma not_hb_d_c : ~ ep_order E_min ev_d ev_c.
Proof.
  intro H. apply hb_min_realizer in H. destruct H as [H1 _].
  unfold L1_min in H1. vm_compute in H1. lia.
Qed.

Lemma f3_iso :
  forall t t', bcd_R t t' <-> fin_sub_order (ep_order E_min) Umin (f3 t) (f3 t').
Proof.
  intros t t'. unfold fin_sub_order. destruct t, t'; simpl proj1_sig.
  (* B3 B3 *)
  - split; intro H; [ apply poset_refl | left; reflexivity ].
  (* B3 C3 *)
  - split.
    + intro H. exfalso. destruct H as [H|[??]]; discriminate.
    + intro H. exfalso. apply incomp_b_c. left. exact H.
  (* B3 D3 *)
  - split.
    + intro H. exfalso. destruct H as [H|[??]]; discriminate.
    + intro H. exfalso. apply not_hb_b_d. exact H.
  (* C3 B3 *)
  - split.
    + intro H. exfalso. destruct H as [H|[??]]; discriminate.
    + intro H. exfalso. apply incomp_b_c. right. exact H.
  (* C3 C3 *)
  - split; intro H; [ apply poset_refl | left; reflexivity ].
  (* C3 D3 *)
  - split.
    + intro H. exact hb_c_d.
    + intro H. right. split; reflexivity.
  (* D3 B3 *)
  - split.
    + intro H. exfalso. destruct H as [H|[??]]; discriminate.
    + intro H. exfalso. apply not_hb_d_b. exact H.
  (* D3 C3 *)
  - split.
    + intro H. exfalso. destruct H as [H|[??]]; discriminate.
    + intro H. exfalso. apply not_hb_d_c. exact H.
  (* D3 D3 *)
  - split; intro H; [ apply poset_refl | left; reflexivity ].
Qed.

Lemma dim_block_bcd_2 : PosetDimension (fin_sub_order (ep_order E_min) Umin) 2.
Proof.
  exact (dimension_iso T3 UU bcd_R (fin_sub_order (ep_order E_min) Umin)
           f3 g3 g3_f3 f3_g3 f3_iso 2 bcd_dim2).
Qed.

(* ------------------------------------------------------------------ *)
(* Barrier assembly: dim E_min = max 1 (max (dim Lmin) (dim Umin)) = 2 *)
(* cross-checking the existing E_min_dim_2. (#66)                       *)
(* ------------------------------------------------------------------ *)

(* Lmin = {a} singleton -> dimension 0 *)
Lemma dim_block_a_0 : PosetDimension (fin_sub_order (ep_order E_min) Lmin) 0.
Proof.
  apply (@fin_singleton_dim0 _ (fin_sub_order (ep_order E_min) Lmin)
                              (fin_sub_order_poset (ep_order E_min) Lmin)).
  intros [x Hx] [y Hy].
  unfold Lmin, Ensembles.In in Hx, Hy.
  assert (Hxy : x = y).
  { rewrite (eq_ev_a x Hx). rewrite (eq_ev_a y Hy). reflexivity. }
  subst y.
  assert (Hx = Hy) by apply proof_irrelevance. subst Hy. reflexivity.
Qed.

(* E_min carrier is finite (same route as E_min_carrier_finite). *)
Lemma E_min_Hfin : Finite (ep_carrier E_min) (Full_set (ep_carrier E_min)).
Proof.
  apply (cardinal_finite _ _ (total (ep_ranked E_min))).
  exact (event_cardinal (ep_ranked E_min)).
Qed.

(* IsBarrier and fin_is_barrier coincide on E_min. *)
Lemma E_min_fin_barrier : fin_is_barrier (ep_order E_min) Lmin Umin.
Proof.
  exact E_min_barrier.
Qed.

Example E_min_exact_dim_via_barrier :
  exists dW, inhabited (PosetDimension (ep_order E_min) dW) /\ dW = 2.
Proof.
  destruct E_min_dim_2 as [HdW].
  pose proof (fin_barrier_dimension_full (ep_order E_min) E_min_Hfin Lmin Umin
                E_min_fin_barrier 0 2 2 dim_block_a_0 dim_block_bcd_2 HdW) as Heq.
  exists 2. split; [ exact (inhabits HdW) | reflexivity ].
Qed.
