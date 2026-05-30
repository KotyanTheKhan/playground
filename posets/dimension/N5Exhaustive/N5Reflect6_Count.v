(** exhaustive_6edge: every 6-edge poset matches one of the 12 count-6 patterns. *)
From Stdlib Require Import List Arith Lia Bool FunctionalExtensionality.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8
  N5Reflect8_Exhaustive N5Reflect8_Bridge N5Reflect8_Count
  N5Reflect6 N5Reflect6_Exhaustive.

Lemma num_none_M_assign_6 : forall M, is_poset_b M = true ->
  edge_count_b M = 6 -> num_none (M_assign M) = 4.
Proof. intros M Hp He. pose proof (edge_plus_none M Hp). lia. Qed.

Lemma exhaustive_6edge : forall M, is_poset_b M = true ->
  edge_count_b M = 6 -> any_pattern_6_b M = true.
Proof.
  intros M Hp He.
  assert (Hin : In (M_assign M) count6_assigns).
  { unfold count6_assigns. apply enum_k_none_complete.
    - apply length_M_assign.
    - apply num_none_M_assign_6; assumption. }
  pose proof coverage_6 as Hcov. rewrite forallb_forall in Hcov.
  specialize (Hcov _ Hin). unfold chk6 in Hcov.
  rewrite (mat_of_M_assign_eq M Hp) in Hcov.
  rewrite Hp in Hcov. cbn in Hcov. exact Hcov.
Qed.
