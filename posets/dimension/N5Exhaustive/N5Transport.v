(** N5Transport.v — Bijection bridge between abstract B-posets and Fin.t 5
    boolean reflection.

    Given 5 pairwise-distinct elements a, b, c, d, e covering the carrier B,
    we set up a bijection Fin.t 5 <-> B and lift R2 to a boolean matrix
    R2_matrix : M5.  We then prove:

      - R2_matrix is a boolean poset (is_poset_b R2_matrix = true),
      - edge_count_b R2_matrix = edge_count_5 R2 a b c d e,
      - is_<pattern>_b R2_matrix = true <-> <abstract exists shape>
        for the 10 patterns of EdgeCount4.v.
*)

From Stdlib Require Import Fin Bool List Arith Lia Classical
  ClassicalDescription IndefiniteDescription FunctionalExtensionality.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs.
From Dimension.N5Exhaustive Require Import EdgeCount N5Reflect.

Section Transport.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.
  Variables a b c d e : B.
  Hypothesis Hab : a <> b. Hypothesis Hac : a <> c.
  Hypothesis Had : a <> d. Hypothesis Hae : a <> e.
  Hypothesis Hbc : b <> c. Hypothesis Hbd : b <> d.
  Hypothesis Hbe : b <> e. Hypothesis Hcd : c <> d.
  Hypothesis Hce : c <> e. Hypothesis Hde : d <> e.
  Hypothesis Hcov : forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e.

  (* ---------------------------------------------------------------- *)
  (** * Bijection Fin.t 5 <-> B *)

  Definition from_fin (i : Fin.t 5) : B :=
    if fin5_eqb i f0 then a
    else if fin5_eqb i f1 then b
    else if fin5_eqb i f2 then c
    else if fin5_eqb i f3 then d
    else e.

  Definition to_fin (x : B) : Fin.t 5 :=
    match excluded_middle_informative (x = a) with
    | left _ => f0
    | right _ =>
      match excluded_middle_informative (x = b) with
      | left _ => f1
      | right _ =>
        match excluded_middle_informative (x = c) with
        | left _ => f2
        | right _ =>
          match excluded_middle_informative (x = d) with
          | left _ => f3
          | right _ => f4
          end
        end
      end
    end.

  (** Boolean matrix lifting [R2] through the bijection. *)
  Definition R2_matrix : M5 :=
    fun i j =>
      if excluded_middle_informative (R2 (from_fin i) (from_fin j))
      then true else false.

  (* ---------------------------------------------------------------- *)
  (** * Computing from_fin on the named indices *)

  Lemma from_fin_f0 : from_fin f0 = a.
  Proof. unfold from_fin. rewrite fin5_eqb_refl. reflexivity. Qed.

  Lemma from_fin_f1 : from_fin f1 = b.
  Proof.
    unfold from_fin.
    destruct (fin5_eqb f1 f0) eqn:E0.
    - apply fin5_eqb_true_iff in E0. discriminate.
    - rewrite fin5_eqb_refl. reflexivity.
  Qed.

  Lemma from_fin_f2 : from_fin f2 = c.
  Proof.
    unfold from_fin.
    destruct (fin5_eqb f2 f0) eqn:E0;
      [apply fin5_eqb_true_iff in E0; discriminate|].
    destruct (fin5_eqb f2 f1) eqn:E1;
      [apply fin5_eqb_true_iff in E1; discriminate|].
    rewrite fin5_eqb_refl. reflexivity.
  Qed.

  Lemma from_fin_f3 : from_fin f3 = d.
  Proof.
    unfold from_fin.
    destruct (fin5_eqb f3 f0) eqn:E0;
      [apply fin5_eqb_true_iff in E0; discriminate|].
    destruct (fin5_eqb f3 f1) eqn:E1;
      [apply fin5_eqb_true_iff in E1; discriminate|].
    destruct (fin5_eqb f3 f2) eqn:E2;
      [apply fin5_eqb_true_iff in E2; discriminate|].
    rewrite fin5_eqb_refl. reflexivity.
  Qed.

  Lemma from_fin_f4 : from_fin f4 = e.
  Proof.
    unfold from_fin.
    destruct (fin5_eqb f4 f0) eqn:E0;
      [apply fin5_eqb_true_iff in E0; discriminate|].
    destruct (fin5_eqb f4 f1) eqn:E1;
      [apply fin5_eqb_true_iff in E1; discriminate|].
    destruct (fin5_eqb f4 f2) eqn:E2;
      [apply fin5_eqb_true_iff in E2; discriminate|].
    destruct (fin5_eqb f4 f3) eqn:E3;
      [apply fin5_eqb_true_iff in E3; discriminate|].
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * from_fin is injective *)

  (** A finite case analysis on j in Fin.t 5. *)
  Lemma fin5_case : forall (P : Fin.t 5 -> Prop),
    P f0 -> P f1 -> P f2 -> P f3 -> P f4 -> forall j, P j.
  Proof.
    intros P H0 H1 H2 H3 H4 j.
    pattern j; apply Fin.caseS'; [exact H0|intros j1].
    pattern j1; apply Fin.caseS'; [exact H1|intros j2].
    pattern j2; apply Fin.caseS'; [exact H2|intros j3].
    pattern j3; apply Fin.caseS'; [exact H3|intros j4].
    pattern j4; apply Fin.caseS'; [exact H4|intros j5].
    inversion j5.
  Qed.

  Lemma from_fin_injective :
    forall i j : Fin.t 5, from_fin i = from_fin j -> i = j.
  Proof.
    intros i j.
    pattern i; apply fin5_case; pattern j; apply fin5_case;
      rewrite ?from_fin_f0, ?from_fin_f1, ?from_fin_f2, ?from_fin_f3,
              ?from_fin_f4;
      intro Hc; try reflexivity.
    (* Now 20 remaining off-diagonal cases. Dispatch each. *)
    - exfalso; apply Hab; exact Hc.
    - exfalso; apply Hac; exact Hc.
    - exfalso; apply Had; exact Hc.
    - exfalso; apply Hae; exact Hc.
    - exfalso; apply Hab; symmetry; exact Hc.
    - exfalso; apply Hbc; exact Hc.
    - exfalso; apply Hbd; exact Hc.
    - exfalso; apply Hbe; exact Hc.
    - exfalso; apply Hac; symmetry; exact Hc.
    - exfalso; apply Hbc; symmetry; exact Hc.
    - exfalso; apply Hcd; exact Hc.
    - exfalso; apply Hce; exact Hc.
    - exfalso; apply Had; symmetry; exact Hc.
    - exfalso; apply Hbd; symmetry; exact Hc.
    - exfalso; apply Hcd; symmetry; exact Hc.
    - exfalso; apply Hde; exact Hc.
    - exfalso; apply Hae; symmetry; exact Hc.
    - exfalso; apply Hbe; symmetry; exact Hc.
    - exfalso; apply Hce; symmetry; exact Hc.
    - exfalso; apply Hde; symmetry; exact Hc.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * Round trips *)

  Lemma from_to_fin : forall x : B, from_fin (to_fin x) = x.
  Proof.
    intros x. unfold to_fin.
    destruct (Hcov x) as [Hx | [Hx | [Hx | [Hx | Hx]]]]; subst x.
    - destruct (excluded_middle_informative (a = a)) as [_|Hne];
        [apply from_fin_f0|contradiction Hne; reflexivity].
    - destruct (excluded_middle_informative (b = a)) as [Heq|_];
        [contradiction (Hab (eq_sym Heq))|].
      destruct (excluded_middle_informative (b = b)) as [_|Hne];
        [apply from_fin_f1|contradiction Hne; reflexivity].
    - destruct (excluded_middle_informative (c = a)) as [Heq|_];
        [contradiction (Hac (eq_sym Heq))|].
      destruct (excluded_middle_informative (c = b)) as [Heq|_];
        [contradiction (Hbc (eq_sym Heq))|].
      destruct (excluded_middle_informative (c = c)) as [_|Hne];
        [apply from_fin_f2|contradiction Hne; reflexivity].
    - destruct (excluded_middle_informative (d = a)) as [Heq|_];
        [contradiction (Had (eq_sym Heq))|].
      destruct (excluded_middle_informative (d = b)) as [Heq|_];
        [contradiction (Hbd (eq_sym Heq))|].
      destruct (excluded_middle_informative (d = c)) as [Heq|_];
        [contradiction (Hcd (eq_sym Heq))|].
      destruct (excluded_middle_informative (d = d)) as [_|Hne];
        [apply from_fin_f3|contradiction Hne; reflexivity].
    - destruct (excluded_middle_informative (e = a)) as [Heq|_];
        [contradiction (Hae (eq_sym Heq))|].
      destruct (excluded_middle_informative (e = b)) as [Heq|_];
        [contradiction (Hbe (eq_sym Heq))|].
      destruct (excluded_middle_informative (e = c)) as [Heq|_];
        [contradiction (Hce (eq_sym Heq))|].
      destruct (excluded_middle_informative (e = d)) as [Heq|_];
        [contradiction (Hde (eq_sym Heq))|].
      apply from_fin_f4.
  Qed.

  Lemma to_from_fin : forall i : Fin.t 5, to_fin (from_fin i) = i.
  Proof.
    intros i. apply from_fin_injective.
    rewrite from_to_fin. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * R2_matrix is a boolean poset *)

  Lemma R2_matrix_true_iff : forall i j,
    R2_matrix i j = true <-> R2 (from_fin i) (from_fin j).
  Proof.
    intros i j. unfold R2_matrix.
    destruct (excluded_middle_informative (R2 (from_fin i) (from_fin j)));
      split; intros; congruence.
  Qed.

  Lemma R2_matrix_false_iff : forall i j,
    R2_matrix i j = false <-> ~ R2 (from_fin i) (from_fin j).
  Proof.
    intros i j. unfold R2_matrix.
    destruct (excluded_middle_informative (R2 (from_fin i) (from_fin j)));
      split; intros; congruence.
  Qed.

  Lemma R2_matrix_refl_b : is_refl_b R2_matrix = true.
  Proof.
    unfold is_refl_b. apply forallb_forall. intros i _.
    apply R2_matrix_true_iff. apply (poset_refl (R := R2)).
  Qed.

  Lemma R2_matrix_antisym_b : is_antisym_b R2_matrix = true.
  Proof.
    unfold is_antisym_b. apply forallb_forall. intros [i j] _.
    simpl.
    destruct (R2_matrix i j) eqn:Hij; simpl; [|reflexivity].
    destruct (R2_matrix j i) eqn:Hji; simpl; [|reflexivity].
    apply R2_matrix_true_iff in Hij.
    apply R2_matrix_true_iff in Hji.
    pose proof (poset_antisym (R := R2) _ _ Hij Hji) as Heq.
    apply fin5_eqb_true_iff.
    apply from_fin_injective. exact Heq.
  Qed.

  Lemma R2_matrix_trans_b : is_trans_b R2_matrix = true.
  Proof.
    unfold is_trans_b.
    apply forallb_forall. intros i _.
    apply forallb_forall. intros j _.
    apply forallb_forall. intros k _.
    destruct (R2_matrix i j) eqn:Hij; simpl; [|reflexivity].
    destruct (R2_matrix j k) eqn:Hjk; simpl; [|reflexivity].
    apply R2_matrix_true_iff in Hij.
    apply R2_matrix_true_iff in Hjk.
    apply R2_matrix_true_iff.
    apply (poset_trans (R := R2)) with (y := from_fin j); assumption.
  Qed.

  Lemma R2_matrix_is_poset : is_poset_b R2_matrix = true.
  Proof.
    unfold is_poset_b.
    rewrite R2_matrix_refl_b, R2_matrix_antisym_b, R2_matrix_trans_b.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * Boolean edge count equals the abstract edge count. *)

  Lemma strict_b_nat_eq : forall i j,
    (if strict_b R2_matrix i j then 1 else 0)
    = strict_indicator R2 (from_fin i) (from_fin j).
  Proof.
    intros i j. unfold strict_b, strict_indicator.
    destruct (R2_matrix i j) eqn:HM; simpl.
    - apply R2_matrix_true_iff in HM.
      destruct (fin5_eqb i j) eqn:Heq; simpl.
      + (* i = j ⇒ from_fin i = from_fin j ⇒ ind = 0 *)
        apply fin5_eqb_true_iff in Heq. subst j.
        destruct (excluded_middle_informative
                    (R2 (from_fin i) (from_fin i) /\ from_fin i <> from_fin i))
          as [[_ Hne]|_]; [contradiction Hne; reflexivity|reflexivity].
      + apply fin5_eqb_false_iff in Heq.
        destruct (excluded_middle_informative
                    (R2 (from_fin i) (from_fin j) /\ from_fin i <> from_fin j))
          as [_|Hn]; [reflexivity|].
        exfalso. apply Hn. split; [exact HM|].
        intro Heq2. apply Heq. apply from_fin_injective. exact Heq2.
    - apply R2_matrix_false_iff in HM.
      destruct (excluded_middle_informative
                  (R2 (from_fin i) (from_fin j) /\ from_fin i <> from_fin j))
        as [[Hr _]|_]; [contradiction|reflexivity].
  Qed.

  Lemma R2_matrix_edge_count_eq :
    edge_count_b R2_matrix = edge_count_5 R2 a b c d e.
  Proof.
    unfold edge_count_b, edge_count_5, all_pairs, all5.
    simpl.
    rewrite !strict_b_nat_eq.
    rewrite !from_fin_f0, !from_fin_f1, !from_fin_f2, !from_fin_f3,
            !from_fin_f4.
    assert (Hdiag : forall x : B, strict_indicator R2 x x = 0).
    { intro x. unfold strict_indicator.
      destruct (excluded_middle_informative (R2 x x /\ x <> x))
        as [[_ Hne]|_]; [contradiction Hne; reflexivity|reflexivity]. }
    rewrite !Hdiag. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * Permutation helpers for the iff direction. *)

  (** strict_b on R2_matrix corresponds to a strict R2 edge. *)
  Lemma strict_b_R2_matrix_iff : forall i j,
    strict_b R2_matrix i j = true <->
    R2 (from_fin i) (from_fin j) /\ from_fin i <> from_fin j.
  Proof.
    intros i j. unfold strict_b. rewrite andb_true_iff.
    rewrite negb_true_iff. rewrite fin5_eqb_false_iff.
    rewrite R2_matrix_true_iff. split.
    - intros [HR Hne]. split; [exact HR|]. intro Heq.
      apply Hne. apply from_fin_injective. exact Heq.
    - intros [HR Hne]. split; [exact HR|]. intro Heq.
      apply Hne. subst. reflexivity.
  Qed.

  (** Insert preserves permutation. *)
  Lemma insert_everywhere_perm :
    forall (A : Type) (x : A) (l m : list A),
      In m (insert_everywhere x l) -> Permutation m (x :: l).
  Proof.
    intros A x l. induction l as [|y ys IH]; intros m Hin; simpl in Hin.
    - destruct Hin as [Heq|[]]. subst. apply Permutation_refl.
    - destruct Hin as [Heq|Hin].
      + subst. apply Permutation_refl.
      + apply in_map_iff in Hin. destruct Hin as [m' [Heq Hm']].
        subst m. specialize (IH _ Hm').
        transitivity (y :: x :: ys).
        * apply perm_skip. exact IH.
        * apply perm_swap.
  Qed.

  Lemma permutations_perm :
    forall (A : Type) (l m : list A),
      In m (permutations l) -> Permutation m l.
  Proof.
    intros A l. induction l as [|x xs IH]; intros m Hin; simpl in Hin.
    - destruct Hin as [Heq|[]]. subst. apply Permutation_refl.
    - apply in_flat_map in Hin. destruct Hin as [m' [Hm' Him]].
      apply insert_everywhere_perm in Him.
      specialize (IH _ Hm').
      transitivity (x :: m'); [exact Him|]. apply perm_skip. exact IH.
  Qed.

  (** insert_everywhere x l: the resulting lists are exactly those obtained
      by inserting x at some position in l. For our [In m (insert_everywhere x l)]
      we use the alternative characterization: m = u ++ x :: v with u ++ v = l. *)
  Lemma insert_everywhere_split :
    forall (A : Type) (x : A) (l : list A) u v,
      l = u ++ v -> In (u ++ x :: v) (insert_everywhere x l).
  Proof.
    intros A x l. induction l as [|y ys IH]; intros u v Heq.
    - destruct u; destruct v; simpl in Heq; try discriminate.
      simpl. left. reflexivity.
    - destruct u as [|u0 us]; simpl in Heq.
      + subst v. simpl. left. reflexivity.
      + injection Heq as Hu0 Heqys. subst u0.
        simpl. right. apply in_map. apply IH. exact Heqys.
  Qed.

  Lemma permutations_in :
    forall (A : Type) (l m : list A),
      Permutation l m -> In m (permutations l).
  Proof.
    intros A l. induction l as [|x xs IH]; intros m Hp.
    - apply Permutation_nil in Hp. subst. simpl. left. reflexivity.
    - simpl. apply in_flat_map.
      assert (In x m) as Hxm.
      { apply Permutation_in with (l := x :: xs); [exact Hp|left; reflexivity]. }
      apply in_split in Hxm. destruct Hxm as [u [v Hmeq]]. subst m.
      (* Permutation (x :: xs) (u ++ x :: v) ⇒ Permutation xs (u ++ v). *)
      assert (Hperm : Permutation xs (u ++ v)).
      { apply Permutation_cons_inv with (a := x).
        transitivity (u ++ x :: v); [exact Hp|].
        symmetry. apply Permutation_middle. }
      exists (u ++ v). split.
      + apply IH. exact Hperm.
      + apply insert_everywhere_split. reflexivity.
  Qed.

  Lemma all5_NoDup : NoDup all5.
  Proof.
    unfold all5, f0, f1, f2, f3, f4.
    constructor; [simpl; intros [E|[E|[E|[E|[]]]]]; discriminate|].
    constructor; [simpl; intros [E|[E|[E|[]]]]; discriminate|].
    constructor; [simpl; intros [E|[E|[]]]; discriminate|].
    constructor; [simpl; intros [E|[]]; discriminate|].
    constructor; [simpl; intros []|].
    constructor.
  Qed.

  (** Every Fin.t 5 list with 5 distinct elements is a permutation of all5
      and hence is in all_perms5. *)
  Lemma five_distinct_in_perms :
    forall v1 v2 v3 v4 v5 : Fin.t 5,
      NoDup [v1; v2; v3; v4; v5] ->
      In [v1; v2; v3; v4; v5] all_perms5.
  Proof.
    intros v1 v2 v3 v4 v5 Hnd.
    apply permutations_in.
    apply NoDup_Permutation.
    - exact all5_NoDup.
    - exact Hnd.
    - intros x. split; intros _.
      + (* x ∈ all5 (always true). Show x ∈ [v1..v5] by incl + length. *)
        assert (Hincl : incl [v1;v2;v3;v4;v5] all5).
        { intros y _. apply in_all5_v. }
        (* Use NoDup_length_incl: NoDup [v1..v5] /\ length all5 <= length [...] /\ incl ⇒ incl all5 [v1..v5]. *)
        assert (Hincl2 : incl all5 [v1;v2;v3;v4;v5]).
        { apply (@NoDup_length_incl _ [v1;v2;v3;v4;v5] all5 Hnd);
            [simpl; lia|exact Hincl]. }
        apply Hincl2. apply in_all5_v.
      + apply in_all5_v.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** * Generic pattern iff. *)

  (** Key: from a [NoDup [v1..v5]] of Fin.t 5 we get 5 distinct B
      elements [from_fin vi], for free. *)
  Lemma NoDup_from_fin :
    forall v1 v2 v3 v4 v5 : Fin.t 5,
      NoDup [v1; v2; v3; v4; v5] ->
      NoDup [from_fin v1; from_fin v2; from_fin v3; from_fin v4; from_fin v5].
  Proof.
    intros v1 v2 v3 v4 v5 Hnd.
    inversion Hnd as [|x1 l1 Hin1 Hnd1 [Eq1a Eq1b]]; subst.
    inversion Hnd1 as [|x2 l2 Hin2 Hnd2 [Eq2a Eq2b]]; subst.
    inversion Hnd2 as [|x3 l3 Hin3 Hnd3 [Eq3a Eq3b]]; subst.
    inversion Hnd3 as [|x4 l4 Hin4 Hnd4 [Eq4a Eq4b]]; subst.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor;[|constructor]]]]];
      simpl in *.
    - intros [E|[E|[E|[E|[]]]]];
        try (apply from_fin_injective in E; subst);
        try (apply Hin1; simpl; tauto).
    - intros [E|[E|[E|[]]]];
        try (apply from_fin_injective in E; subst);
        try (apply Hin2; simpl; tauto).
    - intros [E|[E|[]]];
        try (apply from_fin_injective in E; subst);
        try (apply Hin3; simpl; tauto).
    - intros [E|[]];
        try (apply from_fin_injective in E; subst);
        try (apply Hin4; simpl; tauto).
    - intros [].
  Qed.

  (** Dually, from 5 distinct B's we get 5 distinct Fin.t 5 indices via to_fin. *)
  Lemma NoDup_to_fin :
    forall w1 w2 w3 w4 w5 : B,
      NoDup [w1; w2; w3; w4; w5] ->
      NoDup [to_fin w1; to_fin w2; to_fin w3; to_fin w4; to_fin w5].
  Proof.
    intros w1 w2 w3 w4 w5 Hnd.
    assert (Hinj : forall x y, to_fin x = to_fin y -> x = y).
    { intros x y Heq. rewrite <- (from_to_fin x), <- (from_to_fin y), Heq.
      reflexivity. }
    inversion Hnd as [|x1 l1 Hin1 Hnd1 [Eq1a Eq1b]]; subst.
    inversion Hnd1 as [|x2 l2 Hin2 Hnd2 [Eq2a Eq2b]]; subst.
    inversion Hnd2 as [|x3 l3 Hin3 Hnd3 [Eq3a Eq3b]]; subst.
    inversion Hnd3 as [|x4 l4 Hin4 Hnd4 [Eq4a Eq4b]]; subst.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor;[|constructor]]]]];
      simpl in *.
    - intros [E|[E|[E|[E|[]]]]];
        try (apply Hinj in E; subst);
        try (apply Hin1; simpl; tauto).
    - intros [E|[E|[E|[]]]];
        try (apply Hinj in E; subst);
        try (apply Hin2; simpl; tauto).
    - intros [E|[E|[]]];
        try (apply Hinj in E; subst);
        try (apply Hin3; simpl; tauto).
    - intros [E|[]];
        try (apply Hinj in E; subst);
        try (apply Hin4; simpl; tauto).
    - intros [].
  Qed.

End Transport.
