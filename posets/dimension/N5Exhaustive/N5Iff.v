(** N5Iff.v — 10 pattern iff lemmas (incremental development). *)
From Stdlib Require Import List Classical ClassicalDescription Arith Lia Bool.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount N5Reflect N5Transport.

Section Iff.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.
  Variables a b c d e : B.
  Hypothesis Hab : a <> b. Hypothesis Hac : a <> c.
  Hypothesis Had : a <> d. Hypothesis Hae : a <> e.
  Hypothesis Hbc : b <> c. Hypothesis Hbd : b <> d.
  Hypothesis Hbe : b <> e. Hypothesis Hcd : c <> d.
  Hypothesis Hce : c <> e. Hypothesis Hde : d <> e.
  Hypothesis Hcov : forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e.

  Lemma abcde_NoDup : NoDup [a; b; c; d; e].
  Proof.
    repeat constructor; simpl.
    - intros [E|[E|[E|[E|[]]]]]; congruence.
    - intros [E|[E|[E|[]]]]; congruence.
    - intros [E|[E|[]]]; congruence.
    - intros [E|[]]; congruence.
    - intros [].
  Qed.

  Lemma make_NoDup5 :
    forall w1 w2 w3 w4 w5 : B,
      w1 <> w2 -> w1 <> w3 -> w1 <> w4 -> w1 <> w5 ->
      w2 <> w3 -> w2 <> w4 -> w2 <> w5 ->
      w3 <> w4 -> w3 <> w5 -> w4 <> w5 ->
      NoDup [w1; w2; w3; w4; w5].
  Proof.
    intros w1 w2 w3 w4 w5 D12 D13 D14 D15 D23 D24 D25 D34 D35 D45.
    repeat constructor; simpl.
    - intros [E|[E|[E|[E|[]]]]]; congruence.
    - intros [E|[E|[E|[]]]]; congruence.
    - intros [E|[E|[]]]; congruence.
    - intros [E|[]]; congruence.
    - intros [].
  Qed.

  (** [In pi all_perms5] ⇒ NoDup pi. *)
  Lemma perm_in_all_perms5_nodup :
    forall pi : list (Fin.t 5), In pi all_perms5 -> NoDup pi.
  Proof.
    intros pi Hin.
    pose proof (permutations_perm _ _ _ Hin) as Hperm.
    apply (Permutation_NoDup (Permutation_sym Hperm)).
    exact all5_NoDup.
  Qed.

  (** Extract 10 pairwise inequalities from NoDup of 5 elements. *)
  Lemma NoDup5_pairwise :
    forall w1 w2 w3 w4 w5 : B,
      NoDup [w1; w2; w3; w4; w5] ->
      w1 <> w2 /\ w1 <> w3 /\ w1 <> w4 /\ w1 <> w5 /\
      w2 <> w3 /\ w2 <> w4 /\ w2 <> w5 /\
      w3 <> w4 /\ w3 <> w5 /\ w4 <> w5.
  Proof.
    intros w1 w2 w3 w4 w5 Hnd.
    inversion Hnd as [|x1 l1 Hin1 Hnd1 [Eq1a Eq1b]]; subst.
    inversion Hnd1 as [|x2 l2 Hin2 Hnd2 [Eq2a Eq2b]]; subst.
    inversion Hnd2 as [|x3 l3 Hin3 Hnd3 [Eq3a Eq3b]]; subst.
    inversion Hnd3 as [|x4 l4 Hin4 Hnd4 [Eq4a Eq4b]]; subst.
    simpl in Hin1, Hin2, Hin3, Hin4.
    repeat split; intro Heq.
    - apply Hin1. left. symmetry; exact Heq.
    - apply Hin1. right. left. symmetry; exact Heq.
    - apply Hin1. right. right. left. symmetry; exact Heq.
    - apply Hin1. right. right. right. left. symmetry; exact Heq.
    - apply Hin2. left. symmetry; exact Heq.
    - apply Hin2. right. left. symmetry; exact Heq.
    - apply Hin2. right. right. left. symmetry; exact Heq.
    - apply Hin3. left. symmetry; exact Heq.
    - apply Hin3. right. left. symmetry; exact Heq.
    - apply Hin4. left. symmetry; exact Heq.
  Qed.

  Lemma find_fifth_distinct :
    forall w1 w2 w3 w4 : B,
      w1 <> w2 -> w1 <> w3 -> w1 <> w4 ->
      w2 <> w3 -> w2 <> w4 -> w3 <> w4 ->
      exists w5 : B, w5 <> w1 /\ w5 <> w2 /\ w5 <> w3 /\ w5 <> w4.
  Proof.
    intros w1 w2 w3 w4 D12 D13 D14 D23 D24 D34.
    apply NNPP. intro Hno5.
    (* Hno5 : ~ exists w5, w5 <> w1 /\ ... /\ w5 <> w4. *)
    assert (Hall : forall x : B, x = w1 \/ x = w2 \/ x = w3 \/ x = w4).
    { intro x.
      destruct (classic (x = w1)) as [|N1]; [tauto|].
      destruct (classic (x = w2)) as [|N2]; [tauto|].
      destruct (classic (x = w3)) as [|N3]; [tauto|].
      destruct (classic (x = w4)) as [|N4]; [tauto|].
      exfalso. apply Hno5. exists x. tauto. }
    assert (Hincl : incl [a;b;c;d;e] [w1;w2;w3;w4]).
    { intros x _. destruct (Hall x) as [Hx|[Hx|[Hx|Hx]]]; subst x; simpl; tauto. }
    pose proof (NoDup_incl_length abcde_NoDup Hincl) as Hlen.
    simpl in Hlen. lia.
  Qed.

  Local Notation M := (R2_matrix R2 a b c d e).
  Local Notation ff := (from_fin a b c d e).
  Local Notation tf := (to_fin a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov).

  (** Class 11: 4-claw up. *)
  Lemma is_4claw_up_b_to_exists :
    is_4claw_up_b M = true ->
    exists r l1 l2 l3 l4 : B,
      r <> l1 /\ r <> l2 /\ r <> l3 /\ r <> l4 /\
      l1 <> l2 /\ l1 <> l3 /\ l1 <> l4 /\
      l2 <> l3 /\ l2 <> l4 /\ l3 <> l4 /\
      R2 r l1 /\ R2 r l2 /\ R2 r l3 /\ R2 r l4.
  Proof.
    unfold is_4claw_up_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 20: 4-claw down. *)
  Lemma is_4claw_down_b_to_exists :
    is_4claw_down_b M = true ->
    exists r l1 l2 l3 l4 : B,
      r <> l1 /\ r <> l2 /\ r <> l3 /\ r <> l4 /\
      l1 <> l2 /\ l1 <> l3 /\ l1 <> l4 /\
      l2 <> l3 /\ l2 <> l4 /\ l3 <> l4 /\
      R2 l1 r /\ R2 l2 r /\ R2 l3 r /\ R2 l4 r.
  Proof.
    unfold is_4claw_down_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 16: Bowtie K_{2,2} + isolated. *)
  Lemma is_bowtie_b_to_exists :
    is_bowtie_b M = true ->
    exists p1 p2 q1 q2 : B,
      p1 <> p2 /\ p1 <> q1 /\ p1 <> q2 /\
      p2 <> q1 /\ p2 <> q2 /\ q1 <> q2 /\
      R2 p1 q1 /\ R2 p1 q2 /\ R2 p2 q1 /\ R2 p2 q2.
  Proof.
    unfold is_bowtie_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [_ [N23 [N24 [_ [N34 _]]]]]]]].
    (* bowtie: p1=v1, q1=v2, p2=v3, q2=v4.  Mapping:
       p1<>p2 = v1<>v3 = N13;  p1<>q1 = v1<>v2 = N12;  p1<>q2 = v1<>v4 = N14
       p2<>q1 = v3<>v2 = N23 (sym); p2<>q2 = v3<>v4 = N34; q1<>q2 = v2<>v4 = N24. *)
    assert (N32 : ff v3 <> ff v2)
      by (intro Heq; apply N23; symmetry; exact Heq).
    exists (ff v1). exists (ff v3). exists (ff v2). exists (ff v4).
    repeat split; try assumption.
    all: try assumption.
  Qed.

  (** Class 15: Disjoint chain3 + chain2. *)
  Lemma is_disjoint_b_to_exists :
    is_disjoint_b M = true ->
    exists alpha beta gamma delta eps : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
      beta <> gamma /\ beta <> delta /\ beta <> eps /\
      gamma <> delta /\ gamma <> eps /\ delta <> eps /\
      R2 alpha beta /\ R2 beta gamma /\ R2 alpha gamma /\ R2 delta eps.
  Proof.
    unfold is_disjoint_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 12: Chain3 + below pendant.  α=v1, β=v2, γ=v3, δ=v4. *)
  Lemma is_chain3_below_b_to_exists :
    is_chain3_below_b M = true ->
    exists alpha beta gamma delta : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\
      beta <> gamma /\ beta <> delta /\ gamma <> delta /\
      R2 alpha beta /\ R2 beta gamma /\ R2 alpha gamma /\ R2 alpha delta.
  Proof.
    unfold is_chain3_below_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [_ [N23 [N24 [_ [N34 _]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4).
    repeat split; try assumption. all: try assumption.
  Qed.

  (** Class 14: Chain3 + above pendant.  α=v1, β=v2, γ=v3, δ=v4. *)
  Lemma is_chain3_above_b_to_exists :
    is_chain3_above_b M = true ->
    exists alpha beta gamma delta : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\
      beta <> gamma /\ beta <> delta /\ gamma <> delta /\
      R2 alpha beta /\ R2 beta gamma /\ R2 delta gamma /\ R2 alpha gamma.
  Proof.
    unfold is_chain3_above_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [_ [N23 [N24 [_ [N34 _]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4).
    repeat split; try assumption. all: try assumption.
  Qed.

  (** Class 17: M-shape.  α=v1, β=v2, γ=v3, δ=v4, ε=v5. *)
  Lemma is_M_shape_b_to_exists :
    is_M_shape_b M = true ->
    exists alpha beta gamma delta eps : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
      beta <> gamma /\ beta <> delta /\ beta <> eps /\
      gamma <> delta /\ gamma <> eps /\ delta <> eps /\
      R2 beta alpha /\ R2 beta gamma /\ R2 delta gamma /\ R2 delta eps.
  Proof.
    unfold is_M_shape_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 19: K_{3,2} minus a matching.  α=v1, β=v2, γ=v3, δ=v4, ε=v5. *)
  Lemma is_K32mm_b_to_exists :
    is_K32mm_b M = true ->
    exists alpha beta gamma delta eps : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
      beta <> gamma /\ beta <> delta /\ beta <> eps /\
      gamma <> delta /\ gamma <> eps /\ delta <> eps /\
      R2 alpha eps /\ R2 beta delta /\ R2 gamma delta /\ R2 gamma eps.
  Proof.
    unfold is_K32mm_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 13: 3-claw up with extra parent.  α=v1, β=v2, γ=v3, δ=v4, ε=v5. *)
  Lemma is_3claw_up_xp_b_to_exists :
    is_3claw_up_xp_b M = true ->
    exists alpha beta gamma delta eps : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
      beta <> gamma /\ beta <> delta /\ beta <> eps /\
      gamma <> delta /\ gamma <> eps /\ delta <> eps /\
      R2 beta alpha /\ R2 beta gamma /\ R2 beta eps /\ R2 delta gamma.
  Proof.
    unfold is_3claw_up_xp_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

  (** Class 18: 3-claw down with extra leaf.  α=v1, β=v2, γ=v3, δ=v4, ε=v5. *)
  Lemma is_3claw_down_xl_b_to_exists :
    is_3claw_down_xl_b M = true ->
    exists alpha beta gamma delta eps : B,
      alpha <> beta /\ alpha <> gamma /\ alpha <> delta /\ alpha <> eps /\
      beta <> gamma /\ beta <> delta /\ beta <> eps /\
      gamma <> delta /\ gamma <> eps /\ delta <> eps /\
      R2 alpha beta /\ R2 gamma beta /\ R2 eps beta /\ R2 gamma delta.
  Proof.
    unfold is_3claw_down_xl_b, has_edges_of_shape.
    intro Hex. apply existsb_exists in Hex.
    destruct Hex as [pi [Hpi_in Hpi_forall]].
    destruct pi as [|v1 [|v2 [|v3 [|v4 [|v5 [|? ?]]]]]]; try discriminate.
    simpl in Hpi_forall.
    rewrite !andb_true_iff in Hpi_forall.
    destruct Hpi_forall as [H1 [H2 [H3 [H4 _]]]].
    apply strict_b_R2_matrix_iff in H1, H2, H3, H4.
    destruct H1 as [HR1 _]; destruct H2 as [HRm2 _]; destruct H3 as [HR3 _]; destruct H4 as [HR4 _].
    pose proof (perm_in_all_perms5_nodup _ Hpi_in) as Hnd.
    pose proof (NoDup_from_fin (B:=B) a b c d e Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde v1 v2 v3 v4 v5 Hnd) as HndB.
    pose proof (NoDup5_pairwise _ _ _ _ _ HndB) as Hpairwise.
    destruct Hpairwise as [N12 [N13 [N14 [N15 [N23 [N24 [N25 [N34 [N35 N45]]]]]]]]].
    exists (ff v1), (ff v2), (ff v3), (ff v4), (ff v5).
    repeat split; try assumption.
    all: assumption.
  Qed.

End Iff.
