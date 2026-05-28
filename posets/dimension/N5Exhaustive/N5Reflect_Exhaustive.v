(** N5Reflect_Exhaustive.v — combiner for 4-edge exhaustiveness.

    Composes the 5 parallel-compiled chunk lemmas (chunk_1 .. chunk_5)
    into the full [exhaustive_4edge_decidable] and derives
    [exhaustive_4edge].  Each chunk file does its own [native_cast]
    over ~2530 sublists; dune compiles them in parallel, dropping
    wall-clock from ~150s monolithic to ~30-60s. *)
From Stdlib Require Import Bool List Arith Lia FunctionalExtensionality.
Import ListNotations.
From Dimension.N5Exhaustive Require Import
  N5Reflect
  N5Reflect_Exhaustive_1 N5Reflect_Exhaustive_2 N5Reflect_Exhaustive_3
  N5Reflect_Exhaustive_4 N5Reflect_Exhaustive_5.

(** [sublists 4 all_pairs] splits into the 5 chunks in order.

    Symbolic proof using only [firstn_skipn] and [skipn_skipn].
    No [vm_compute] over the 12650-item list. *)
Lemma sublists_chunks_eq :
  sublists 4 all_pairs =
    exhaustive_4edge_chunk_1 ++ exhaustive_4edge_chunk_2 ++
    exhaustive_4edge_chunk_3 ++ exhaustive_4edge_chunk_4 ++
    exhaustive_4edge_chunk_5.
Proof.
  unfold exhaustive_4edge_chunk_1, exhaustive_4edge_chunk_2,
         exhaustive_4edge_chunk_3, exhaustive_4edge_chunk_4,
         exhaustive_4edge_chunk_5.
  (* Fold up from the right: at each level, replace skipn (m+n) with
     skipn n (skipn m), pairing with the preceding firstn to make
     [firstn n (skipn m) ++ skipn n (skipn m) = skipn m] via firstn_skipn. *)
  replace (skipn 10120 (sublists 4 all_pairs))
    with (skipn 2530 (skipn 7590 (sublists 4 all_pairs)))
    by (rewrite skipn_skipn; f_equal).
  rewrite (firstn_skipn 2530 (skipn 7590 (sublists 4 all_pairs))).
  replace (skipn 7590 (sublists 4 all_pairs))
    with (skipn 2530 (skipn 5060 (sublists 4 all_pairs)))
    by (rewrite skipn_skipn; f_equal).
  rewrite (firstn_skipn 2530 (skipn 5060 (sublists 4 all_pairs))).
  replace (skipn 5060 (sublists 4 all_pairs))
    with (skipn 2530 (skipn 2530 (sublists 4 all_pairs)))
    by (rewrite skipn_skipn; f_equal).
  rewrite (firstn_skipn 2530 (skipn 2530 (sublists 4 all_pairs))).
  rewrite (firstn_skipn 2530 (sublists 4 all_pairs)).
  reflexivity.
Qed.

(** Combine the 5 chunk Qed's into the full forallb. *)
Lemma exhaustive_4edge_decidable :
  forallb (fun es =>
    let M := from_edges es in
    implb (is_poset_b M && Nat.eqb (edge_count_b M) 4)
          (any_pattern_b M))
    (sublists 4 all_pairs) = true.
Proof.
  rewrite sublists_chunks_eq.
  rewrite !forallb_app.
  rewrite exhaustive_4edge_chunk_1_holds.
  rewrite exhaustive_4edge_chunk_2_holds.
  rewrite exhaustive_4edge_chunk_3_holds.
  rewrite exhaustive_4edge_chunk_4_holds.
  rewrite exhaustive_4edge_chunk_5_holds.
  reflexivity.
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
