(** N5Reflect_Exhaustive.v — vm_compute Qed for the 4-edge exhaustiveness.

    Isolated from N5Reflect.v so the slow vm_compute reduction is
    cached separately and does not block iteration on the definitions
    in the parent file. *)
From Stdlib Require Import Bool List Arith Lia FunctionalExtensionality.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect.

(** The decidable enumeration: every 4-edge poset matches one of the
    10 patterns.  Proved by [vm_cast_no_check] over the 12650 size-4
    sublists of all 25 ordered pairs of [Fin.t 5]. *)
Lemma exhaustive_4edge_decidable :
  forallb (fun es =>
    let M := from_edges es in
    implb (is_poset_b M && Nat.eqb (edge_count_b M) 4)
          (any_pattern_b M))
    (sublists 4 all_pairs) = true.
Proof.
  native_cast_no_check (eq_refl true).
Qed.

(** Filtered sublists are in [sublists (length filtered) original]. *)
Lemma filter_in_sublists : forall {A} (f : A -> bool) (l : list A),
  In (filter f l) (sublists (length (filter f l)) l).
Proof.
  intros A f l. induction l as [|x xs IH]; simpl.
  - left. reflexivity.
  - destruct (f x) eqn:Hfx; simpl.
    + apply in_or_app. left. apply in_map. exact IH.
    + destruct (length (filter f xs)) as [|n] eqn:Hlen.
      * apply length_zero_iff_nil in Hlen. rewrite Hlen.
        simpl. left. reflexivity.
      * simpl. apply in_or_app. right.
        exact IH.
Qed.

(** [edge_count_b] equals the length of [M_edges]. *)
Lemma edge_count_b_length : forall M,
  edge_count_b M = length (M_edges M).
Proof.
  intros M. unfold edge_count_b, M_edges.
  induction all_pairs as [|p ps IH]; simpl; [reflexivity|].
  destruct (strict_b M (fst p) (snd p)); simpl; rewrite IH; reflexivity.
Qed.

(** Final exhaustive lemma. *)
Lemma exhaustive_4edge :
  forall M, is_poset_b M = true -> edge_count_b M = 4 ->
    is_4claw_up_b M = true \/ is_4claw_down_b M = true \/
    is_bowtie_b M = true \/ is_disjoint_b M = true \/
    is_chain3_below_b M = true \/ is_chain3_above_b M = true \/
    is_M_shape_b M = true \/ is_K32mm_b M = true \/
    is_3claw_up_xp_b M = true \/ is_3claw_down_xl_b M = true.
Proof.
  intros M Hp Hec.
  rewrite edge_count_b_length in Hec.
  pose proof (filter_in_sublists
                (fun p : Fin.t 5 * Fin.t 5 => strict_b M (fst p) (snd p))
                all_pairs) as HinSub.
  fold (M_edges M) in HinSub.
  rewrite Hec in HinSub.
  pose proof exhaustive_4edge_decidable as Hdec.
  rewrite forallb_forall in Hdec.
  specialize (Hdec (M_edges M) HinSub).
  cbv zeta in Hdec.
  assert (Hpw : forall i j, from_edges (M_edges M) i j = M i j).
  { intros i j. symmetry. apply poset_eq_from_edges. exact Hp. }
  assert (Hext : from_edges (M_edges M) = M).
  { apply functional_extensionality. intros i.
    apply functional_extensionality. intros j. apply Hpw. }
  assert (Hpre : is_poset_b (from_edges (M_edges M))
                 && Nat.eqb (edge_count_b (from_edges (M_edges M))) 4 = true).
  { rewrite Hext. rewrite Hp. simpl.
    rewrite edge_count_b_length. rewrite Hec. reflexivity. }
  rewrite Hpre in Hdec. simpl in Hdec.
  rewrite Hext in Hdec.
  unfold any_pattern_b in Hdec.
  repeat rewrite orb_true_iff in Hdec.
  tauto.
Qed.
