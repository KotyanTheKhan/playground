(** exhaustive_7edge: every 7-edge poset matches one of the 9 count-7 patterns.
    Reuses the count-8 bridge apparatus (M_assign / mat_of_M_assign_eq /
    enum_k_none_complete / edge_plus_none); only the edge count (7) and None
    count (3) change. *)

From Stdlib Require Import List Arith Lia Bool FunctionalExtensionality.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8
  N5Reflect8_Exhaustive N5Reflect8_Bridge N5Reflect8_Count
  N5Reflect7 N5Reflect7_Exhaustive.

Lemma num_none_M_assign_7 : forall M, is_poset_b M = true ->
  edge_count_b M = 7 -> num_none (M_assign M) = 3.
Proof. intros M Hp He. pose proof (edge_plus_none M Hp). lia. Qed.

Lemma exhaustive_7edge : forall M, is_poset_b M = true ->
  edge_count_b M = 7 -> any_pattern_7_b M = true.
Proof.
  intros M Hp He.
  assert (Hin : In (M_assign M) count7_assigns).
  { unfold count7_assigns. apply enum_k_none_complete.
    - apply length_M_assign.
    - apply num_none_M_assign_7; assumption. }
  pose proof coverage_7 as Hcov. rewrite forallb_forall in Hcov.
  specialize (Hcov _ Hin). unfold chk7 in Hcov.
  rewrite (mat_of_M_assign_eq M Hp) in Hcov.
  rewrite Hp in Hcov. cbn in Hcov. exact Hcov.
Qed.
