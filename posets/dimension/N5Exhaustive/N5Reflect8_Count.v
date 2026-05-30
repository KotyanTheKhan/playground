(** Counting bridge: an 8-edge poset has exactly 2 incomparable canonical
    pairs, i.e. [num_none (M_assign M) = 2]. Combined with [length_M_assign]
    and [enum_k_none_complete], this places [M_assign M] in [count8_assigns]. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8 N5Reflect8_Exhaustive N5Reflect8_Bridge.

Lemma fold_add_eq : forall (A : Type) (g : A -> nat) (l : list A),
  (forall x, In x l -> g x = 1) ->
  fold_right (fun p acc => g p + acc) 0 l = length l.
Proof.
  induction l as [|x l IH]; intro H; cbn.
  - reflexivity.
  - rewrite (H x (or_introl eq_refl)).
    rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma fold_combine : forall (A : Type) (f g : A -> nat) (l : list A),
  fold_right (fun p acc => f p + acc) 0 l
  + fold_right (fun p acc => g p + acc) 0 l
  = fold_right (fun p acc => (f p + g p) + acc) 0 l.
Proof. induction l as [|x l IH]; cbn; [ reflexivity | rewrite <- IH; lia ]. Qed.

Lemma length_filter_map_isnone : forall (M : M5) (l : list (Fin.t 5 * Fin.t 5)),
  length (filter (fun o => match o with None => true | _ => false end)
                 (map (assign_of M) l))
  = fold_right (fun p acc =>
      (if (match assign_of M p with None => true | _ => false end) then 1 else 0)
      + acc) 0 l.
Proof.
  intros M l. induction l as [|x l IH]; cbn; [ reflexivity | ].
  destruct (assign_of M x) as [b|] eqn:E; cbn; rewrite IH; reflexivity.
Qed.

Lemma edge_count_pairs10 : forall M,
  edge_count_b M =
  fold_right (fun p acc => (if strict_b M (fst p) (snd p) then 1 else 0)
    + (if strict_b M (snd p) (fst p) then 1 else 0) + acc) 0 pairs10.
Proof.
  intro M. unfold edge_count_b, strict_b. cbn.
  rewrite ?andb_false_r, ?andb_true_r. cbn. ring.
Qed.

Lemma num_none_pairs10 : forall M,
  num_none (M_assign M) =
  fold_right (fun p acc =>
    (if (match assign_of M p with None => true | _ => false end) then 1 else 0)
    + acc) 0 pairs10.
Proof. intro M. unfold num_none, M_assign. apply length_filter_map_isnone. Qed.

Lemma pair_sum_1 : forall M, is_poset_b M = true ->
  forall p, In p pairs10 ->
  (if strict_b M (fst p) (snd p) then 1 else 0)
  + (if strict_b M (snd p) (fst p) then 1 else 0)
  + (if (match assign_of M p with None => true | _ => false end) then 1 else 0) = 1.
Proof.
  intros M Hp p Hin.
  pose proof (pairs10_neq p Hin) as Hne.
  pose proof (poset_antisym_b _ Hp _ _ Hne) as Hanti.
  unfold strict_b, assign_of.
  assert (E1 : fin5_eqb (fst p) (snd p) = false) by (apply fin5_eqb_false_iff; exact Hne).
  assert (E2 : fin5_eqb (snd p) (fst p) = false)
    by (apply fin5_eqb_false_iff; intro Hc; apply Hne; symmetry; exact Hc).
  rewrite E1, E2.
  destruct (M (fst p) (snd p)) eqn:Mab; destruct (M (snd p) (fst p)) eqn:Mba;
    cbn; try reflexivity.
  cbn in Hanti; discriminate.
Qed.

Lemma edge_plus_none : forall M, is_poset_b M = true ->
  edge_count_b M + num_none (M_assign M) = 10.
Proof.
  intros M Hp.
  rewrite edge_count_pairs10, num_none_pairs10.
  rewrite (fold_combine _
    (fun p => (if strict_b M (fst p) (snd p) then 1 else 0)
            + (if strict_b M (snd p) (fst p) then 1 else 0))
    (fun p => (if (match assign_of M p with None => true | _ => false end) then 1 else 0))
    pairs10).
  rewrite (fold_add_eq _ _ pairs10) by (intros p Hin; apply (pair_sum_1 M Hp p Hin)).
  reflexivity.
Qed.

Lemma num_none_M_assign : forall M, is_poset_b M = true ->
  edge_count_b M = 8 -> num_none (M_assign M) = 2.
Proof. intros M Hp He. pose proof (edge_plus_none M Hp). lia. Qed.
