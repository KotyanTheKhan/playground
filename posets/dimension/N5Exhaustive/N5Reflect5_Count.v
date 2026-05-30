(** exhaustive_5edge. *)
From Stdlib Require Import List Arith Lia Bool FunctionalExtensionality.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8
  N5Reflect8_Exhaustive N5Reflect8_Bridge N5Reflect8_Count
  N5Reflect5 N5Reflect5_Exhaustive.
Lemma num_none_M_assign_5 : forall M, is_poset_b M = true ->
  edge_count_b M = 5 -> num_none (M_assign M) = 5.
Proof. intros M Hp He. pose proof (edge_plus_none M Hp). lia. Qed.
Lemma exhaustive_5edge : forall M, is_poset_b M = true ->
  edge_count_b M = 5 -> any_pattern_5_b M = true.
Proof.
  intros M Hp He.
  assert (Hin : In (M_assign M) count5_assigns).
  { unfold count5_assigns. apply enum_k_none_complete.
    - apply length_M_assign. - apply num_none_M_assign_5; assumption. }
  pose proof coverage_5 as Hcov. rewrite forallb_forall in Hcov.
  specialize (Hcov _ Hin). unfold chk5 in Hcov.
  rewrite (mat_of_M_assign_eq M Hp) in Hcov.
  rewrite Hp in Hcov. cbn in Hcov. exact Hcov.
Qed.
