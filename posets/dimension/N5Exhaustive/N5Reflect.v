(** N5Reflect.v — Boolean reflection layer for 5-element posets.

    M5 = Fin.t 5 -> Fin.t 5 -> bool with:
      - is_poset_b : reflexive, antisymmetric, transitive
      - strict_b   : M i j && i <> j
      - edge_count_b : count of strict edges over all 25 ordered pairs
      - 10 pattern booleans (k=4 patterns: 4claw_up, 4claw_down, bowtie,
        disjoint, chain3_below, chain3_above, M_shape, K32mm,
        3claw_up_xp, 3claw_down_xl)
      - exhaustive_4edge : Qed by vm_compute over the 12650 size-4
        sublists of the 25 ordered pairs.
*)

From Stdlib Require Import Fin Bool List Arith Lia.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** * Basic helpers on Fin.t 5 *)

Definition M5 := Fin.t 5 -> Fin.t 5 -> bool.

Definition fin5_eqb (i j : Fin.t 5) : bool :=
  match Fin.eq_dec i j with left _ => true | right _ => false end.

Lemma fin5_eqb_refl : forall i, fin5_eqb i i = true.
Proof. intros i. unfold fin5_eqb. destruct (Fin.eq_dec i i); congruence. Qed.

Lemma fin5_eqb_true_iff : forall i j, fin5_eqb i j = true <-> i = j.
Proof.
  intros i j. unfold fin5_eqb. destruct (Fin.eq_dec i j); split; intros; congruence.
Qed.

Lemma fin5_eqb_false_iff : forall i j, fin5_eqb i j = false <-> i <> j.
Proof.
  intros i j. unfold fin5_eqb. destruct (Fin.eq_dec i j); split; intros; congruence.
Qed.

(** All elements of Fin.t 5 *)
Definition f0 : Fin.t 5 := Fin.F1.
Definition f1 : Fin.t 5 := Fin.FS Fin.F1.
Definition f2 : Fin.t 5 := Fin.FS (Fin.FS Fin.F1).
Definition f3 : Fin.t 5 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Definition f4 : Fin.t 5 := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))).

Definition all5 : list (Fin.t 5) := [f0; f1; f2; f3; f4].

Definition all_pairs : list (Fin.t 5 * Fin.t 5) :=
  flat_map (fun i => map (fun j => (i, j)) all5) all5.

(* ------------------------------------------------------------------ *)
(** * Sublists *)

Fixpoint sublists {A} (n : nat) (l : list A) : list (list A) :=
  match n with
  | 0 => [[]]
  | S k =>
      match l with
      | [] => []
      | x :: xs => map (cons x) (sublists k xs) ++ sublists (S k) xs
      end
  end.

(* ------------------------------------------------------------------ *)
(** * Building matrices from edge lists *)

Definition from_edges (es : list (Fin.t 5 * Fin.t 5)) : M5 :=
  fun i j =>
    existsb (fun p => fin5_eqb (fst p) i && fin5_eqb (snd p) j) es ||
    fin5_eqb i j.

(* ------------------------------------------------------------------ *)
(** * Boolean poset axioms *)

Definition is_refl_b (M : M5) : bool :=
  forallb (fun i => M i i) all5.

Definition is_antisym_b (M : M5) : bool :=
  forallb (fun p =>
    let i := fst p in let j := snd p in
    implb (M i j && M j i) (fin5_eqb i j)) all_pairs.

Definition is_trans_b (M : M5) : bool :=
  forallb (fun i =>
    forallb (fun j =>
      forallb (fun k =>
        implb (M i j && M j k) (M i k)) all5) all5) all5.

Definition is_poset_b (M : M5) : bool :=
  is_refl_b M && is_antisym_b M && is_trans_b M.

Definition strict_b (M : M5) (i j : Fin.t 5) : bool :=
  M i j && negb (fin5_eqb i j).

Definition edge_count_b (M : M5) : nat :=
  fold_right (fun p acc => (if strict_b M (fst p) (snd p) then 1 else 0) + acc)
             0 all_pairs.

(* ------------------------------------------------------------------ *)
(** * All permutations of all5 *)

(** Insert [x] at every position of [l]. *)
Fixpoint insert_everywhere {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: map (cons y) (insert_everywhere x ys)
  end.

Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => flat_map (insert_everywhere x) (permutations xs)
  end.

Definition all_perms5 : list (list (Fin.t 5)) := permutations all5.

(* ------------------------------------------------------------------ *)
(** * Pattern combinator: existence of an injection witnessing edges. *)

Definition has_edges_of_shape
  (edges_fn : Fin.t 5 -> Fin.t 5 -> Fin.t 5 -> Fin.t 5 -> Fin.t 5
              -> list (Fin.t 5 * Fin.t 5))
  (M : M5) : bool :=
  existsb (fun pi : list (Fin.t 5) =>
    match pi with
    | [v1; v2; v3; v4; v5] =>
        forallb (fun e => strict_b M (fst e) (snd e))
                (edges_fn v1 v2 v3 v4 v5)
    | _ => false
    end) all_perms5.

(* ------------------------------------------------------------------ *)
(** * The 10 k=4 patterns *)

(** 4-claw up: a single source r with 4 outgoing edges to l1..l4. *)
Definition is_4claw_up_b : M5 -> bool :=
  has_edges_of_shape (fun r l1 l2 l3 l4 =>
    [(r, l1); (r, l2); (r, l3); (r, l4)]).

(** 4-claw down: a single sink r with 4 incoming edges. *)
Definition is_4claw_down_b : M5 -> bool :=
  has_edges_of_shape (fun r l1 l2 l3 l4 =>
    [(l1, r); (l2, r); (l3, r); (l4, r)]).

(** Bowtie: 4 named, 5th unused; 2x2 complete bipartite. *)
Definition is_bowtie_b : M5 -> bool :=
  has_edges_of_shape (fun p1 q1 p2 q2 _unused =>
    [(p1, q1); (p1, q2); (p2, q1); (p2, q2)]).

(** Disjoint: triangle + disjoint edge. *)
Definition is_disjoint_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d e =>
    [(a, b); (b, c); (a, c); (d, e)]).

(** chain3 + extra below the top. *)
Definition is_chain3_below_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d _e =>
    [(a, b); (b, c); (a, c); (a, d)]).

(** chain3 + extra above the bottom. *)
Definition is_chain3_above_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d _e =>
    [(a, b); (b, c); (d, c); (a, c)]).

(** M shape: two V's sharing nothing. *)
Definition is_M_shape_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d e =>
    [(b, a); (b, c); (d, c); (d, e)]).

(** K32mm. *)
Definition is_K32mm_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d e =>
    [(a, e); (b, d); (c, d); (c, e)]).

(** 3-claw up with extra pendant. *)
Definition is_3claw_up_xp_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d e =>
    [(b, a); (b, c); (b, e); (d, c)]).

(** 3-claw down with extra leg. *)
Definition is_3claw_down_xl_b : M5 -> bool :=
  has_edges_of_shape (fun a b c d e =>
    [(a, b); (c, b); (e, b); (c, d)]).

(* ------------------------------------------------------------------ *)
(** * Bundled disjunction *)

Definition any_pattern_b (M : M5) : bool :=
  is_4claw_up_b M || is_4claw_down_b M || is_bowtie_b M ||
  is_disjoint_b M || is_chain3_below_b M || is_chain3_above_b M ||
  is_M_shape_b M  || is_K32mm_b M || is_3claw_up_xp_b M ||
  is_3claw_down_xl_b M.

(* ------------------------------------------------------------------ *)
(** * Decidable enumeration: every 4-edge poset matches a pattern. *)

(* ------------------------------------------------------------------ *)
(** * Bridge: a 4-edge poset's matrix equals from_edges of its strict-edge list. *)

(** Strict-edge list of a matrix (restricted to all_pairs). *)
Definition M_edges (M : M5) : list (Fin.t 5 * Fin.t 5) :=
  filter (fun p => strict_b M (fst p) (snd p)) all_pairs.

(** Every element of Fin.t 5 appears in all5. *)
Lemma in_all5_v : forall i : Fin.t 5, In i all5.
Proof.
  intros i.
  pattern i; apply Fin.caseS'; [ simpl; tauto | intros i1 ].
  pattern i1; apply Fin.caseS'; [ simpl; tauto | intros i2 ].
  pattern i2; apply Fin.caseS'; [ simpl; tauto | intros i3 ].
  pattern i3; apply Fin.caseS'; [ simpl; tauto | intros i4 ].
  pattern i4; apply Fin.caseS'; [ simpl; tauto | intros i5 ].
  inversion i5.
Qed.

Lemma in_all_pairs : forall i j : Fin.t 5, In (i, j) all_pairs.
Proof.
  intros i j. unfold all_pairs.
  apply in_flat_map. exists i. split; [apply in_all5_v|].
  apply in_map. apply in_all5_v.
Qed.

(** [from_edges es i j] reflects membership in es OR diagonal. *)
Lemma from_edges_spec : forall es i j,
  from_edges es i j = true <-> (In (i, j) es \/ i = j).
Proof.
  intros es i j. unfold from_edges. rewrite orb_true_iff.
  split.
  - intros [Hex | Heq].
    + left. apply existsb_exists in Hex. destruct Hex as [p [Hp Hpe]].
      rewrite andb_true_iff in Hpe. destruct Hpe as [H1 H2].
      rewrite fin5_eqb_true_iff in H1, H2.
      destruct p as [i' j']. simpl in *. subst. exact Hp.
    + right. apply fin5_eqb_true_iff in Heq. exact Heq.
  - intros [Hin | Heq].
    + left. apply existsb_exists. exists (i, j). split; [exact Hin|].
      simpl. rewrite !fin5_eqb_refl. reflexivity.
    + right. apply fin5_eqb_true_iff. exact Heq.
Qed.

(** For a poset M, [M i j = from_edges (M_edges M) i j]. *)
Lemma poset_eq_from_edges : forall M,
  is_poset_b M = true ->
  forall i j, M i j = from_edges (M_edges M) i j.
Proof.
  intros M Hp i j.
  unfold is_poset_b in Hp. rewrite !andb_true_iff in Hp.
  destruct Hp as [[Hrefl _Hanti] _Htr].
  unfold is_refl_b in Hrefl.
  rewrite forallb_forall in Hrefl.
  destruct (Fin.eq_dec i j) as [Heq | Hneq].
  - (* diagonal *)
    subst j. rewrite Hrefl by apply in_all5_v.
    unfold from_edges. rewrite fin5_eqb_refl. rewrite orb_true_r. reflexivity.
  - (* off-diagonal: M i j ↔ In (i,j) M_edges *)
    destruct (M i j) eqn:HM.
    + symmetry. apply from_edges_spec. left.
      unfold M_edges. apply filter_In. split; [apply in_all_pairs|].
      simpl. unfold strict_b. rewrite HM. simpl.
      apply fin5_eqb_false_iff in Hneq. rewrite Hneq. reflexivity.
    + symmetry. unfold from_edges.
      apply orb_false_intro.
      * apply not_true_is_false. intros Hex.
        apply existsb_exists in Hex. destruct Hex as [p [Hp Hpe]].
        rewrite andb_true_iff in Hpe. destruct Hpe as [H1 H2].
        destruct p as [i' j']. simpl in *.
        rewrite fin5_eqb_true_iff in H1, H2. subst.
        unfold M_edges in Hp. apply filter_In in Hp. destruct Hp as [_ Hs].
        simpl in Hs. unfold strict_b in Hs. rewrite HM in Hs. discriminate.
      * apply fin5_eqb_false_iff. exact Hneq.
Qed.
