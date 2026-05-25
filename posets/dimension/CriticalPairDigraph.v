(** * Critical-Pair Digraph Infrastructure

    The critical-pair digraph of a poset [R] has the elements of the
    underlying type as vertices, and a directed edge [x -> y] iff
    [(x, y)] is a critical pair of [R].

    This file provides the basic infrastructure (finiteness of the edge
    set, non-emptiness criterion, classical decidability) needed by
    Trotter's Theorem 6.1 in the n = 5 dispatcher.  See
    [docs/superpowers/plans/2026-05-22-close-remaining-admits.md],
    Track B Phase B1. *)

From Stdlib Require Import List Classical ClassicalEpsilon.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs LinearSum.
(* Re-export the explicit-U Ensemble interface AFTER [CriticalPairs]
   (which itself imports Szpilrajn → implicit U).  Matches the pattern
   used elsewhere in [posets/dimension/]. *)
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section CriticalPairDigraph.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** The critical-pair digraph of [R]: directed edge [x -> y] iff
      [(x, y)] is a critical pair. *)
  Definition CP_digraph : A -> A -> Prop :=
    fun x y => IsCriticalPair R x y.

End CriticalPairDigraph.

(** ** Decidability of critical-pair membership.

    Critical pairs are defined by a [forall a, ...]/[forall b, ...]
    universally quantified body, so decidability is non-constructive.
    We use classical logic to obtain it. *)

Lemma cp_digraph_decidable :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  forall x y : A, IsCriticalPair R x y \/ ~ IsCriticalPair R x y.
Proof.
  intros A R Hpos _ x y.
  apply classic.
Qed.

(** ** Non-emptiness of the CP digraph for a non-chain poset.

    A finite poset has at least one critical pair iff it has at least
    one incomparable pair.  Forward direction: every CP is incomparable
    by definition.  Backward direction: the lifting lemma
    [incomparable_lifting_to_critical_pair]. *)

Lemma cp_digraph_nonempty_iff_incomparable :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  (exists a b : A, Incomparable R a b) <-> (exists x y : A, IsCriticalPair R x y).
Proof.
  intros A R Hpos HfinA. split.
  - (* incomparable pair -> critical pair (lifting). *)
    intros [a [b Hinc]].
    destruct (incomparable_lifting_to_critical_pair R HfinA a b Hinc)
      as [x' [y' [_ [_ Hcp]]]].
    exists x', y'. exact Hcp.
  - (* critical pair -> incomparable (immediate from the class). *)
    intros [x [y Hcp]].
    exists x, y. exact Hcp.(critical_incomparable).
Qed.

(** ** Finiteness of the CP digraph.

    For a finite poset, only finitely many pairs (x, y) exist, so the
    set of critical pairs is a finite list.  We enumerate the Cartesian
    product of the carrier with itself and use classical decidability
    to filter. *)

Section CP_digraph_finite_section.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** Cartesian product of two lists, as a single list of pairs. *)
  Fixpoint list_prod (xs : list A) (ys : list A) : list (A * A) :=
    match xs with
    | nil => nil
    | x :: xs' =>
        List.map (fun y => (x, y)) ys ++ list_prod xs' ys
    end.

  Lemma list_prod_in_iff :
    forall xs ys x y,
      List.In (x, y) (list_prod xs ys) <-> List.In x xs /\ List.In y ys.
  Proof.
    induction xs as [| x0 xs IH].
    - intros ys x y. simpl. split.
      + intro Hf. destruct Hf.
      + intros [Hf _]. destruct Hf.
    - intros ys x y. simpl. split.
      + intro Hin.
        apply in_app_or in Hin. destruct Hin as [Hmap | Hrest].
        * apply in_map_iff in Hmap.
          destruct Hmap as [y0 [Heq Hy0]]. inversion Heq. subst x y0.
          split; [left; reflexivity | exact Hy0].
        * apply IH in Hrest. destruct Hrest as [Hx_in Hy_in].
          split; [right; exact Hx_in | exact Hy_in].
      + intros [Hx_in Hy_in].
        destruct Hx_in as [Heq | Hx_in].
        * subst x0. apply in_or_app. left.
          apply in_map_iff. exists y. split; [reflexivity | exact Hy_in].
        * apply in_or_app. right. apply IH. split; assumption.
  Qed.

  (** Filter a list of pairs to keep only the critical pairs.  Uses
      classical [excluded_middle_informative] to make the boolean
      decision. *)
  Fixpoint filter_cp (l : list (A * A)) : list (A * A) :=
    match l with
    | nil => nil
    | p :: rest =>
        if excluded_middle_informative (IsCriticalPair R (fst p) (snd p))
        then p :: filter_cp rest
        else filter_cp rest
    end.

  Lemma filter_cp_in_iff :
    forall l p, List.In p (filter_cp l) <->
                (List.In p l /\ IsCriticalPair R (fst p) (snd p)).
  Proof.
    induction l as [| q rest IH].
    - intro p. simpl. split.
      + intro Hf. destruct Hf.
      + intros [Hf _]. destruct Hf.
    - intro p. simpl.
      destruct (excluded_middle_informative
                  (IsCriticalPair R (fst q) (snd q))) as [Hq_cp | Hq_ncp].
      + split.
        * intro Hin. destruct Hin as [Heq | Hrest].
          { subst q. split; [left; reflexivity | exact Hq_cp]. }
          { apply IH in Hrest. destruct Hrest as [Hpl Hpcp].
            split; [right; exact Hpl | exact Hpcp]. }
        * intros [Hpl Hpcp]. destruct Hpl as [Heq | Hpl].
          { subst p. left. reflexivity. }
          { right. apply IH. split; assumption. }
      + split.
        * intro Hin. apply IH in Hin. destruct Hin as [Hpl Hpcp].
          split; [right; exact Hpl | exact Hpcp].
        * intros [Hpl Hpcp]. destruct Hpl as [Heq | Hpl].
          { subst p. exfalso. apply Hq_ncp. exact Hpcp. }
          { apply IH. split; assumption. }
  Qed.

End CP_digraph_finite_section.

Lemma cp_digraph_finite :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  exists L : list (A * A),
    forall x y, IsCriticalPair R x y <-> List.In (x, y) L.
Proof.
  intros A R Hpos HfinA.
  (* Step 1: enumerate the carrier as a list. *)
  destruct (finite_cardinal _ _ HfinA) as [n Hcard].
  destruct (cardinal_to_list A (Full_set A) n Hcard)
    as [carrier [_ [Hcarrier_iff _]]].
  (* Step 2: build the Cartesian product as a list of pairs. *)
  set (all_pairs := list_prod carrier carrier).
  (* Step 3: filter to keep only critical pairs. *)
  exists (filter_cp R all_pairs).
  intros x y. split.
  - intro Hcp.
    apply filter_cp_in_iff. split; [| simpl; exact Hcp].
    unfold all_pairs. apply list_prod_in_iff. split.
    + apply Hcarrier_iff. apply Full_intro.
    + apply Hcarrier_iff. apply Full_intro.
  - intro Hin.
    apply filter_cp_in_iff in Hin. destruct Hin as [_ Hcp].
    simpl in Hcp. exact Hcp.
Qed.

(** ** Extremality predicate.

    A critical pair [(x', y')] of [R] is *extremal* if it is maximal
    under the natural CP-refinement preorder
      [(p, q) <= (x', y')  iff  R p x' /\ R y' q]
    restricted to the set of critical pairs.

    Geometric intuition: [(x', y')] is at the "top" of the CP digraph
    in the sense that no other CP [(p, q)] sits "above" it (with [x']
    further from the bottom and [y'] further from the top).  Because
    the carrier is finite, such a maximal element always exists once
    at least one CP exists.

    Why this is the right notion for Trotter's boundary argument.
    Trotter's per-L' boundary set construction processes a *single*
    "designated" critical pair [(x', y')] and shows that all other
    critical pairs whose endpoints intersect [{x', y'}] can be either
    reversed by [L_extra] or covered by a per-L' boundary set.  The
    extremality condition makes the inductive case go through: any
    boundary CP [(p, q)] sharing an endpoint with [(x', y')] and
    pointing "upward" (i.e. with [R x' p] or [R q y']) must collapse
    to [(x', y')] itself, eliminating the awkward case where the
    boundary set would need to chase an infinite tower of CPs.

    Concretely the predicate has two clauses:
      - [(x', y')] is itself a critical pair of [R];
      - any critical pair [(p, q)] with [R p x' /\ R y' q] is exactly
        [(x', y')].
    The second clause is the *maximality-under-refinement* clause:
    we cannot push the first coordinate further down ([R p x']) and
    simultaneously the second coordinate further up ([R y' q]) while
    remaining a critical pair, except trivially at [(x', y')] itself.

    Note: this is exactly the fixed-point property of the lifting in
    [incomparable_lifting_to_critical_pair] applied with [(x', y')]
    in place of [(x, y)]; iterating the lift terminates at extremal
    pairs by finiteness. *)

Definition IsExtremalCP {A : Type} (R : A -> A -> Prop)
                        `{IsPoset A R} (x' y' : A) : Prop :=
  IsCriticalPair R x' y' /\
  forall p q : A,
    IsCriticalPair R p q ->
    R p x' ->
    R y' q ->
    p = x' /\ q = y'.

(** ** Existence of an extremal critical pair.

    Strategy: enumerate the (finite) CP digraph as a list [L] via
    [cp_digraph_finite], then walk [L] picking a CP that is
    maximal under the refinement preorder
      [(p, q) <= (x, y)  iff  R p x /\ R y q]
    among the CPs in [L].  Because the underlying [R] is antisymmetric,
    the preorder restricted to the finite set of pairs in [L] is a
    partial order, so a maximal element exists.

    The proof is by induction on the *length* of [L] using a
    well-founded order on naturals.  At each step we either find that
    the head of the list is maximal among all elements of the list, or
    we remove it and recurse on the (shorter) sublist of elements
    above it under the preorder. *)

Section ExtremalCPExistence.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** The CP-refinement preorder, as a relation on pairs.
      [cp_le pq rs] means [rs] is "more extremal" than [pq]: the first
      coordinate is pushed down ([R fst(rs) fst(pq)]) and the second
      coordinate is pushed up ([R snd(pq) snd(rs)]). *)
  Definition cp_le (pq rs : A * A) : Prop :=
    R (fst rs) (fst pq) /\ R (snd pq) (snd rs).

  Lemma cp_le_refl : forall pq, cp_le pq pq.
  Proof. intro pq. split; apply poset_refl. Qed.

  Lemma cp_le_trans : forall pq rs uv,
    cp_le pq rs -> cp_le rs uv -> cp_le pq uv.
  Proof.
    intros pq rs uv [H1 H2] [H3 H4].
    split.
    - eapply poset_trans; eauto.
    - eapply poset_trans; eauto.
  Qed.

  Lemma cp_le_antisym : forall pq rs,
    cp_le pq rs -> cp_le rs pq -> pq = rs.
  Proof.
    intros [p q] [r s] [H1 H2] [H3 H4]. simpl in *.
    f_equal.
    - apply poset_antisym; assumption.
    - apply poset_antisym; assumption.
  Qed.

  (** Standard finite-list max-element lemma for the [cp_le] preorder.
      Stated abstractly so the induction is on plain list length. *)
  Lemma list_has_cp_max :
    forall (L : list (A * A)),
    L <> nil ->
    exists m : A * A,
      List.In m L /\
      forall p : A * A, List.In p L -> cp_le m p -> p = m.
  Proof.
    induction L as [| h L' IH].
    - intro Hne. exfalso. apply Hne. reflexivity.
    - intros _.
      destruct L' as [| h' L''] eqn:HL'eq.
      + (* Singleton list. *)
        exists h. split; [left; reflexivity |].
        intros p Hin Hle. destruct Hin as [Heq | Hf]; [| destruct Hf].
        symmetry. exact Heq.
      + (* Cons case. *)
        assert (Htail_ne : (h' :: L'') <> nil) by discriminate.
        specialize (IH Htail_ne).
        destruct IH as [m_tail [Hin_tail Hmax_tail]].
        (* Two cases: cp_le m_tail h, or not. *)
        destruct (classic (cp_le m_tail h)) as [Hle | Hnle].
        * (* h is at least as big as m_tail: use h. *)
          exists h. split; [left; reflexivity |].
          intros p Hin Hh_le_p.
          destruct Hin as [Hheq | Htin].
          { symmetry. exact Hheq. }
          { (* p ∈ tail.  cp_le h p and cp_le m_tail h give cp_le m_tail p
               (by transitivity), so Hmax_tail forces p = m_tail.
               Then cp_le m_tail h ∧ cp_le h m_tail by antisym gives h
               = m_tail.  So p = m_tail = h. *)
            assert (Hmt_le_p : cp_le m_tail p)
              by (eapply cp_le_trans; eauto).
            specialize (Hmax_tail p Htin Hmt_le_p). subst p.
            apply cp_le_antisym; assumption. }
        * (* h is not above m_tail: use m_tail. *)
          exists m_tail. split; [right; exact Hin_tail |].
          intros p Hin Hmt_le_p.
          destruct Hin as [Hheq | Htin].
          { subst p. exfalso. apply Hnle. exact Hmt_le_p. }
          { apply Hmax_tail; assumption. }
  Qed.

End ExtremalCPExistence.

(** ** Main lemma: every non-antichain non-chain finite poset has an
    extremal critical pair.

    The argument:
      - Use [cp_digraph_finite] to enumerate all CPs as a list [L].
      - [L] is non-empty by [cp_digraph_nonempty_iff_incomparable].
      - Apply [list_has_cp_max] to find a maximal element of [L] under
        [cp_le].
      - That element is the desired extremal CP. *)

Lemma extremal_cp_exists :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  (exists a b : A, Incomparable R a b) ->
  exists x' y' : A, IsExtremalCP R x' y'.
Proof.
  intros A R Hpos HfinA Hinc.
  destruct (cp_digraph_finite R HfinA) as [L HL_iff].
  destruct (proj1 (cp_digraph_nonempty_iff_incomparable R HfinA) Hinc)
    as [x0 [y0 Hcp0]].
  assert (HL_ne : L <> nil).
  { intro Heq. subst L.
    apply (proj1 (HL_iff x0 y0) Hcp0). }
  destruct (list_has_cp_max R L HL_ne) as [[xm ym] [Hin_m Hmax_m]].
  exists xm, ym.
  split.
  - apply HL_iff. exact Hin_m.
  - intros p q Hcp_pq Hxmp Hyqm.
    assert (HinL_pq : List.In (p, q) L) by (apply HL_iff; exact Hcp_pq).
    assert (Hcp_le : cp_le R (xm, ym) (p, q)).
    { split; simpl; assumption. }
    specialize (Hmax_m (p, q) HinL_pq Hcp_le).
    inversion Hmax_m. subst. split; reflexivity.
Qed.

(** ** Convenience: extremal CP existence from a non-antichain, non-chain
    finite poset.

    Trotter's Theorem 6.1 starts from a poset that is neither an
    antichain nor a chain — equivalently, it has at least one
    incomparable pair AND at least two related elements.  The
    non-antichain side is irrelevant for extremal CP existence (one
    needs only an incomparable pair, since the CP digraph is
    non-empty), so the slightly stronger statement below is what
    downstream consumers will actually need.

    We state it as a corollary so that the link to Trotter's setup is
    explicit, even though it is equivalent to [extremal_cp_exists]. *)

Corollary extremal_cp_exists_non_chain :
  forall {A : Type} (R : A -> A -> Prop) `{IsPoset A R},
  Finite A (Full_set A) ->
  ~ (forall a b : A, R a b \/ R b a) ->
  exists x' y' : A, IsExtremalCP R x' y'.
Proof.
  intros A R Hpos HfinA Hnchain.
  (* Extract an incomparable pair from the non-chain hypothesis. *)
  assert (Hinc : exists a b : A, Incomparable R a b).
  { destruct (not_all_ex_not _ _ Hnchain) as [a Ha].
    destruct (not_all_ex_not _ _ Ha) as [b Hab].
    exists a, b. unfold Incomparable. intro Hcmp.
    apply Hab. destruct Hcmp as [Hab' | Hba]; [left | right]; assumption. }
  apply extremal_cp_exists; assumption.
Qed.

(** ** Discharge sketch for [trotter_boundary_existence].

    With [extremal_cp_exists] in hand, the still-Admitted Sub-claim 4
    in [posets/dimension/RemovablePairs.v] becomes:

    1. Apply [extremal_cp_exists] to obtain an extremal CP
       [(x_e, y_e)].
    2. If [(x_e, y_e) = (x', y')] (the "designated" CP in the
       lemma's hypothesis), then the second clause of [IsExtremalCP]
       collapses every interior boundary CP into [(x', y')] — making
       the [B_of L' := nil] witness valid for clauses (a) and (b),
       and L_extra alone covers clause (c).
    3. Otherwise [(x_e, y_e) ≠ (x', y')] but is still a CP and is
       maximal under [cp_le].  Either reduce to case 2 by switching
       the designated CP, or feed the extremal CP through Trotter's
       L_extra and boundary set construction to discharge clause (c)
       for every CP whose endpoints intersect [{x', y'}] — by
       extremality, no such CP can refine [(x', y')] further.

    Step 3 is the residual combinatorial work; it requires a careful
    case analysis on which endpoint of the boundary CP lies in
    [{x', y'}], plus reuse of [trotter_L_extra_exists] (already Qed)
    for the boundary CPs reversed via [L_extra].  The Coq side of
    that work belongs in [RemovablePairs.v], not here. *)
