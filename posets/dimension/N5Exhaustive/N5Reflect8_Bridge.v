(** Bridge from the count-8 enumeration (coverage_8) to an arbitrary 8-edge
    poset M: every poset matrix is reconstructed by [mat_of (M_assign M)],
    where [M_assign M] records the canonical orientation of each of the 10
    unordered pairs. Together with [num_none (M_assign M) = 2] (next file)
    this lets [enum_k_none_complete] place [M_assign M] in [count8_assigns]. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

(* Destruct the leading [forall (_ : Fin.t 5)] of the goal into 5 concrete
   cases. Operates before any hypothesis mentions the variable. *)
Ltac fin5 :=
  let x := fresh "x" in intro x; pattern x; apply Fin.caseS';
  [ | let y := fresh "x" in intro y; pattern y; apply Fin.caseS';
  [ | let y := fresh "x" in intro y; pattern y; apply Fin.caseS';
  [ | let y := fresh "x" in intro y; pattern y; apply Fin.caseS';
  [ | let y := fresh "x" in intro y; pattern y; apply Fin.caseS';
  [ | let y := fresh "x" in intro y; pattern y; apply Fin.case0 ]]]]].

(* ----- the canonical orientation assignment of a matrix ----- *)
Definition assign_of (M : M5) (p : Fin.t 5 * Fin.t 5) : option bool :=
  if M (fst p) (snd p) then Some true
  else if M (snd p) (fst p) then Some false else None.

Definition M_assign (M : M5) : list (option bool) := map (assign_of M) pairs10.

Lemma length_M_assign : forall M, length (M_assign M) = 10.
Proof. intro M. unfold M_assign. rewrite length_map. reflexivity. Qed.

(* ----- poset facts in pointwise form ----- *)
Lemma poset_refl : forall M, is_poset_b M = true -> forall i, M i i = true.
Proof.
  intros M Hp i. unfold is_poset_b in Hp. rewrite !andb_true_iff in Hp.
  destruct Hp as [[Hr _] _]. unfold is_refl_b in Hr.
  rewrite forallb_forall in Hr. apply Hr. apply in_all5_v.
Qed.

Lemma poset_antisym_b : forall M, is_poset_b M = true ->
  forall i j, i <> j -> M i j && M j i = false.
Proof.
  intros M Hp i j Hij. unfold is_poset_b in Hp. rewrite !andb_true_iff in Hp.
  destruct Hp as [[_ Has] _]. unfold is_antisym_b in Has.
  rewrite forallb_forall in Has.
  specialize (Has (i,j) (in_all_pairs i j)). cbn in Has.
  destruct (M i j && M j i) eqn:E.
  - cbn in Has. apply fin5_eqb_true_iff in Has. contradiction.
  - reflexivity.
Qed.

(* ----- combinatorial facts about pairs10 ----- *)
Lemma pairs10_neq : forall p, In p pairs10 -> fst p <> snd p.
Proof.
  intros p Hin. unfold pairs10 in Hin; cbn in Hin.
  repeat (destruct Hin as [Hin|Hin]); try contradiction;
    try (subst p; cbn; intro Hc; discriminate).
Qed.

Lemma pairs10_cover : forall i j, i <> j ->
  In (i,j) pairs10 \/ In (j,i) pairs10.
Proof.
  fin5; fin5; intro Hij;
    first [ solve [ exfalso; apply Hij; reflexivity ]
          | solve [ left; cbn; repeat (first [ left; reflexivity | right ]) ]
          | solve [ right; cbn; repeat (first [ left; reflexivity | right ]) ] ].
Qed.

(* ----- combine l (map f l) membership ----- *)
Lemma in_combine_map_self :
  forall (A B : Type) (f : A -> B) (l : list A) p o,
    In (p, o) (combine l (map f l)) <-> (In p l /\ o = f p).
Proof.
  induction l as [|x l IH]; intros p o; cbn.
  - split; [ contradiction | intros [[] _] ].
  - split.
    + intros [Heq | Hin].
      * injection Heq as Hp Ho. subst p o. split; [ left; reflexivity | reflexivity ].
      * apply IH in Hin. destruct Hin as [Hl Ho]. split; [ right; exact Hl | exact Ho ].
    + intros [[Heq | Hl] Ho].
      * subst p. left. rewrite Ho. reflexivity.
      * right. apply IH. split; [ exact Hl | exact Ho ].
Qed.

(* ----- the key membership characterisation ----- *)
Lemma in_assign_edges_M_assign : forall M i j,
  is_poset_b M = true ->
  (In (i,j) (assign_edges (M_assign M)) <-> i <> j /\ M i j = true).
Proof.
  intros M i j Hp.
  pose proof (poset_antisym_b _ Hp) as Ha.
  unfold assign_edges, M_assign. rewrite in_flat_map.
  split.
  - intros [[p o] [Hcomb Hin]].
    apply in_combine_map_self in Hcomb. destruct Hcomb as [Hppair Ho].
    pose proof (pairs10_neq p Hppair) as Hpneq.
    subst o. cbn in Hin. unfold assign_of in Hin.
    destruct (M (fst p) (snd p)) eqn:E1.
    + cbn in Hin. destruct Hin as [Heq | []].
      injection Heq as Hi Hj. subst i j. split; [ exact Hpneq | exact E1 ].
    + destruct (M (snd p) (fst p)) eqn:E2.
      * cbn in Hin. destruct Hin as [Heq | []].
        injection Heq as Hi Hj. subst i j.
        split; [ intro Hc; apply Hpneq; symmetry; exact Hc | exact E2 ].
      * cbn in Hin. contradiction.
  - intros [Hne HM].
    assert (Hji : M j i = false).
    { specialize (Ha i j Hne). rewrite HM in Ha. cbn in Ha. exact Ha. }
    destruct (pairs10_cover i j Hne) as [Hin10 | Hin10].
    + exists (i, j, Some true). split.
      * apply in_combine_map_self. split; [ exact Hin10 | ].
        unfold assign_of; cbn. rewrite HM. reflexivity.
      * cbn. left. reflexivity.
    + exists (j, i, Some false). split.
      * apply in_combine_map_self. split; [ exact Hin10 | ].
        unfold assign_of; cbn. rewrite Hji, HM. reflexivity.
      * cbn. left. reflexivity.
Qed.

(* ----- reconstruction: a poset is its own canonical orientation ----- *)
Lemma mat_of_M_assign : forall M, is_poset_b M = true ->
  forall i j, mat_of (M_assign M) i j = M i j.
Proof.
  intros M Hp i j.
  pose proof (poset_refl _ Hp) as Hr.
  unfold mat_of.
  destruct (Fin.eq_dec i j) as [Heq | Hne].
  - subst j. rewrite (Hr i). rewrite from_edges_spec. right. reflexivity.
  - destruct (M i j) eqn:HM.
    + rewrite from_edges_spec. left.
      apply (in_assign_edges_M_assign M i j Hp). split; [ exact Hne | exact HM ].
    + destruct (from_edges (assign_edges (M_assign M)) i j) eqn:HF; [ | reflexivity ].
      exfalso. apply from_edges_spec in HF. destruct HF as [Hin | Heq].
      * apply (in_assign_edges_M_assign M i j Hp) in Hin.
        destruct Hin as [_ HM']. rewrite HM' in HM; discriminate.
      * contradiction.
Qed.
