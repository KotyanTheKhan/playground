# Dilworth Theorem — Hall's Marriage Theorem Proof Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the two `Admitted` lemmas in `posets/dilworth/WidthUpperBound.v` with complete Coq proofs by proving Hall's marriage theorem in a new `Hall.v` file and applying it via an augmented bipartite graph.

**Architecture:** (1) `Hall.v` — a self-contained, type-polymorphic Hall's marriage theorem proved by strong induction on `|X|` with a classical tight/non-tight case split. (2) `WidthUpperBound.v` — three new helper lemmas connecting the Dilworth poset structure to Hall's hypothesis, then the two admits filled using `Hall.hall_marriage_theorem`. No dune changes needed (`coq.theory` auto-discovers `Hall.v`).

**Tech Stack:** Coq + Stdlib (Ensembles, Finite_sets, Classical, ClassicalEpsilon, ClassicalChoice, Finite_sets_facts, Wf_nat). Build: `dune build posets/dilworth/Hall.vo` and `dune build posets/`. No unit tests — compilation IS the test.

---

## File Map

| File | Status | Responsibility |
|------|--------|----------------|
| `posets/dilworth/Hall.v` | **Create** | Abstract Hall's marriage theorem (no poset imports) |
| `posets/dilworth/WidthUpperBound.v` | **Modify** | Add `From Dilworth Require Import Hall`; add 3 helpers; fill 2 admits |

---

### Task 1: Create `Hall.v` — definitions and stub

**Files:**
- Create: `posets/dilworth/Hall.v`

Hall's theorem is stated for arbitrary left type `L` and right type `R`. This heterogeneous form is needed because the Dilworth application uses `A` on the left and `sum A A` on the right.

- [ ] **Step 1: Write `Hall.v`**

```coq
From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith Wf_nat.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Dilworth Require Import CardinalArithmetic CardinalLemmas.

Section Hall.
  Variables L R : Type.

  (** N(S) = the union of nbrs(x) for x ∈ S *)
  Definition set_neighbors (nbrs : L -> Ensemble R) (S : Ensemble L) : Ensemble R :=
    fun y => exists x, In L S x /\ In R (nbrs x) y.

  (** Hall's condition: every S ⊆ X satisfies |S| ≤ |N(S)| *)
  Definition HallCondition (X : Ensemble L) (nbrs : L -> Ensemble R) : Prop :=
    forall S ns nn,
      Included L S X ->
      cardinal L S ns ->
      cardinal R (set_neighbors nbrs S) nn ->
      ns <= nn.

  (** Perfect matching: injective f : X → Y with f(x) ∈ nbrs(x) *)
  Definition IsPerfectMatching
      (X : Ensemble L) (Y : Ensemble R)
      (nbrs : L -> Ensemble R) (m : L -> R) : Prop :=
    (forall x, In L X x -> In R Y (m x)) /\
    (forall x, In L X x -> In R (nbrs x) (m x)) /\
    (forall x1 x2, In L X x1 -> In L X x2 -> m x1 = m x2 -> x1 = x2).

  (** Main theorem — proved in later tasks *)
  Theorem hall_marriage_theorem :
      forall (X : Ensemble L) (Y : Ensemble R) nx (nbrs : L -> Ensemble R),
    cardinal L X nx ->
    Finite R Y ->
    (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
    HallCondition X nbrs ->
    exists m : L -> R, IsPerfectMatching X Y nbrs m.
  Proof.
  Admitted.

End Hall.
```

- [ ] **Step 2: Build**

Run: `dune build posets/dilworth/Hall.vo`
Expected: success (Admitted is fine for now)

- [ ] **Step 3: Commit**

```bash
git add posets/dilworth/Hall.v
git commit -m "feat: add Hall.v scaffold with definitions and admitted theorem"
```

---

### Task 2: Hall helper lemmas — set_neighbors and cardinality

**Files:**
- Modify: `posets/dilworth/Hall.v` — add before `hall_marriage_theorem`

These helpers are called inside the Hall proof. Add them all inside the `Section Hall`.

- [ ] **Step 1: Add set_neighbors properties**

```coq
  Lemma set_neighbors_empty : forall nbrs,
    set_neighbors nbrs (Empty_set L) = Empty_set R.
  Proof.
    intros nbrs. apply Extensionality_Ensembles. intros y. split.
    - intros [x [Hx _]]. inversion Hx.
    - intro Hy. inversion Hy.
  Qed.

  Lemma set_neighbors_mono : forall nbrs S T,
    Included L S T ->
    Included R (set_neighbors nbrs S) (set_neighbors nbrs T).
  Proof.
    intros nbrs S T Hincl y [x [Hx Hy]].
    exists x. split; [exact (Hincl x Hx) | exact Hy].
  Qed.

  Lemma set_neighbors_union : forall nbrs S T,
    set_neighbors nbrs (Union L S T) =
    Union R (set_neighbors nbrs S) (set_neighbors nbrs T).
  Proof.
    intros nbrs S T. apply Extensionality_Ensembles. intros y. split.
    - intros [x [Hx Hy]]. inversion Hx as [z Hz | z Hz]; subst.
      + apply Union_introl. exists z. split; assumption.
      + apply Union_intror. exists z. split; assumption.
    - intros Hy. inversion Hy as [z Hz | z Hz]; subst.
      + destruct Hz as [x [Hx Hyx]].
        exists x. split; [apply Union_introl; exact Hx | exact Hyx].
      + destruct Hz as [x [Hx Hyx]].
        exists x. split; [apply Union_intror; exact Hx | exact Hyx].
  Qed.

  (* N(nbrs \ {y₀})(S) = N(nbrs)(S) \ {y₀} *)
  Lemma set_neighbors_remove_point :
      forall (nbrs : L -> Ensemble R) (S : Ensemble L) (y0 : R),
    set_neighbors (fun x z => In R (nbrs x) z /\ z <> y0) S =
    fun z => In R (set_neighbors nbrs S) z /\ z <> y0.
  Proof.
    intros nbrs S y0. apply Extensionality_Ensembles. intros z. split.
    - intros [x [Hx [Hzx Hneq]]].
      split; [exists x; split; assumption | exact Hneq].
    - intros [[x [Hx Hzx]] Hneq].
      exists x. split; [exact Hx | split; assumption].
  Qed.

  (* N(nbrs ∩ complement T)(S) = N(nbrs)(S) ∩ complement T *)
  Lemma set_neighbors_remove_set :
      forall (nbrs : L -> Ensemble R) (S : Ensemble L) (T : Ensemble R),
    set_neighbors (fun x z => In R (nbrs x) z /\ ~ In R T z) S =
    fun z => In R (set_neighbors nbrs S) z /\ ~ In R T z.
  Proof.
    intros nbrs S T. apply Extensionality_Ensembles. intros z. split.
    - intros [x [Hx [Hzx Hnot]]].
      split; [exists x; split; assumption | exact Hnot].
    - intros [[x [Hx Hzx]] Hnot].
      exists x. split; [exact Hx | split; assumption].
  Qed.
```

- [ ] **Step 2: Add cardinal helper lemmas**

These lemmas handle cardinality arithmetic used in the Hall proof's case analysis.

```coq
  Lemma Finite_diff_set : forall (S T : Ensemble R),
    Finite R S ->
    Finite R (fun y => In R S y /\ ~ In R T y).
  Proof.
    intros S T HS.
    apply (Finite_downward_closed R S HS).
    intros x [Hx _]. exact Hx.
  Qed.

  (* If x ∈ S and |S| = S n, then |S \ {x}| = n *)
  Lemma card_remove_point_R : forall (S : Ensemble R) (x : R) n,
    In R S x ->
    cardinal R S (S n) ->
    cardinal R (fun y => In R S y /\ y <> x) n.
  Proof.
    intros. exact (cardinal_remove R S x n H H0).
  Qed.

  (* |S| ≥ 1 when x ∈ S *)
  Lemma card_inhabited_pos : forall (S : Ensemble L) x n,
    In L S x -> cardinal L S n -> n >= 1.
  Proof.
    intros S x n Hx Hcard.
    destruct n; [inversion Hcard; subst; inversion Hx | lia].
  Qed.

  (* If T ⊊ X (proper subset, same cardinality finite type) then |T| < |X| *)
  (* Proved by: X has some x ∉ T, so |T| ≤ |X \ {x}| = |X| - 1 < |X| *)
  Lemma proper_subset_card_lt : forall (X T : Ensemble L) n m,
    cardinal L X n ->
    cardinal L T m ->
    Included L T X ->
    Inhabited L T ->
    T <> X ->
    m < n.
  Proof.
    intros X T n m HcardX HcardT Hincl HinhT Hneq.
    apply Nat.lt_of_le_pred.
    - destruct n as [| n']. {
        (* n = 0: X = ∅, but T ⊆ X = ∅, contradicts Inhabited T *)
        inversion HcardX. subst.
        destruct HinhT as [a Ha]. apply Hincl in Ha. inversion Ha. }
      simpl. exact (le_n_Sn n').
    - (* m ≤ n - 1 = n' *)
      destruct n as [| n']. {
        inversion HcardX. subst.
        destruct HinhT as [a Ha]. apply Hincl in Ha. inversion Ha. }
      simpl.
      (* T ≠ X, so some x ∈ X is not in T *)
      assert (Hx_exists : exists x, In L X x /\ ~ In L T x).
      { apply NNPP. intro Hnot.
        apply Hneq. apply Extensionality_Ensembles. intros x. split.
        - intro Hx. apply Hincl in Hx. exact Hx.
        - intro Hx.
          apply NNPP. intro Hnot'.
          apply Hnot. exists x. split; [exact Hx | exact Hnot']. }
      destruct Hx_exists as [x [Hx_X Hx_notT]].
      assert (Hcard_X' : cardinal L (fun y => In L X y /\ y <> x) n').
      { exact (cardinal_remove L X x n' Hx_X HcardX). }
      apply (incl_card_le L T (fun y => In L X y /\ y <> x) m n');
        [exact HcardT | exact Hcard_X' |].
      intros y Hy. split; [exact (Hincl y Hy) |].
      intro Heq. subst y. exact (Hx_notT Hy).
  Qed.

  (* |X \ T| < |X| when T is inhabited and T ⊆ X *)
  Lemma diff_card_lt : forall (X T : Ensemble L) n m,
    cardinal L X n ->
    cardinal L T m ->
    m >= 1 ->
    Included L T X ->
    cardinal L (fun y => In L X y /\ ~ In L T y) (n - m) ->
    n - m < n.
  Proof.
    intros X T n m HcardX HcardT Hm Hincl Hdiff.
    lia.
  Qed.
```

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/Hall.vo`
Expected: success

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/Hall.v
git commit -m "feat: add Hall helper lemmas for set_neighbors and cardinality"
```

---

### Task 3: Hall theorem — base case and proof skeleton

**Files:**
- Modify: `posets/dilworth/Hall.v` — replace `Admitted` with a `Fix`-based skeleton

- [ ] **Step 1: Replace the Admitted proof body with a Fix skeleton**

Replace the body of `hall_marriage_theorem` (`Proof. Admitted.`) with:

```coq
  Proof.
    intros X Y nx. revert X Y.
    refine (Fix lt_wf
      (fun nx => forall (X : Ensemble L) (Y : Ensemble R) (nbrs : L -> Ensemble R),
        cardinal L X nx ->
        Finite R Y ->
        (forall x y, In L X x -> In R (nbrs x) y -> In R Y y) ->
        HallCondition X nbrs ->
        exists m : L -> R, IsPerfectMatching X Y nbrs m)
      (fun nx IH => _)).
    intros X Y nbrs Hcard_X HfinY Hnbrs_Y Hhall.
    destruct nx as [| nx'].
    - (* ===== Base case: X = ∅ ===== *)
      (* Hall condition on ∅ is vacuously satisfied. Any function works. *)
      inversion Hcard_X. subst.
      (* We need some default value in R for the function range.
         Use choice: for each l : L, exists r : R satisfying True. *)
      (* Since X = Empty_set L, we just need any m : L -> R. *)
      (* If R is empty the proof is still valid (no x ∈ X to check). *)
      (* Use classical choice with a trivial relation. *)
      assert (Hchoice : exists m : L -> R,
        forall x : L, (In L (Empty_set L) x -> False)).
      { exists (fun _ => epsilon (inhabits (epsilon (inhabits todo) (fun _ => True))) (fun _ => True)).
        intros x Hx. inversion Hx. }
      (* Simpler: just produce any witness using classical epsilon on R → L → R *)
      (* We need inhabited R to call epsilon. If R is uninhabited and X=∅, all
         conditions hold vacuously. Handle by classical case split. *)
      destruct (classic (inhabited R)) as [[r0] | Huninh].
      + exists (fun _ => r0).
        repeat split; intros x Hx; inversion Hx.
      + (* R is uninhabited — conditions vacuously hold *)
        exfalso.
        (* Actually if R is uninhabited, nbrs x = ∅ for all x.
           Hall condition on ∅ gives 0 ≤ 0. Fine. But we still need m : L -> R.
           If R is uninhabited, there's no m : L -> R (without ⊥).
           This case can't arise if HallCondition is satisfiable and X is non-empty...
           but X = ∅ here, so no issue — we just need to produce SOME function.
           If R is uninhabited, use exfalso from Finite R Y:
           Finite R Y implies... Y could still be ∅ even if R uninhabited.
           Actually if R is uninhabited there is no function L -> R unless L is also
           uninhabited. We need L uninhabited in this branch. *)
        (* Actually for nx = 0, X = ∅, so all conditions on m are vacuous.
           We only need m : L -> R to exist. Since R might be uninhabited,
           we handle this by noting that if R is uninhabited, we can still produce
           m using ex_falso in the body — but Coq needs a concrete term.
           
           Practical fix: change the exists to provide epsilon with a default derived
           from Finite R Y. Or simply: if R uninhabited and X = ∅, use any proof of
           False — but we don't have one. 
           
           Better: add `inhabited R` as a hypothesis OR use the epsilon trick below. *)
        (* Leave this as Admitted for now — see note in Task 3 *)
        admit.
    - (* ===== Inductive case: |X| = S nx' ===== *)
      (* X is inhabited *)
      assert (Hinhab_X : Inhabited L X).
      { inversion Hcard_X as [| X' n Hcard' x Hnotin]. subst.
        apply Inhabited_intro with x. apply Union_intror. apply In_singleton. }
      (* Case split: tight or non-tight *)
      destruct (classic (exists (T : Ensemble L),
          Inhabited L T /\ T <> X /\ Included L T X /\
          exists nt nn : nat,
            cardinal L T nt /\
            cardinal R (set_neighbors nbrs T) nn /\
            nt = nn))
        as [Htight | Hntight].
      + (* --- Tight case --- *)
        destruct Htight as [T [HinhT [HneqT [HinclT [nt [nn [HcardT [HcardNT Heq]]]]]]]].
        subst nn.
        (* Apply IH to T (with same nbrs and Y) *)
        assert (HcardT_lt : nt < S nx').
        { destruct (finite_cardinal L T (cardinal_finite L T nt HcardT)) as [nt' Hnt'].
          (* nt = nt' since cardinal is deterministic *)
          assert (Hnt_eq : nt' = nt). {
            apply Nat.le_antisymm;
            [exact (incl_card_le L T T nt' nt Hnt' HcardT (fun x Hx => Hx)) |
             exact (incl_card_le L T T nt nt' HcardT Hnt' (fun x Hx => Hx))]. }
          subst nt'.
          apply (proper_subset_card_lt X T (S nx') nt HcardX HcardT HinclT HinhT HneqT). }
        assert (HhallT : HallCondition T nbrs).
        { intros S ns nn HinclS HcardS HcardNS.
          apply (Hhall S ns nn).
          - intros x Hx. exact (HinclT x (HinclS x Hx)).
          - exact HcardS.
          - exact HcardNS. }
        destruct (IH nt HcardT_lt T Y nbrs HcardT HfinY Hnbrs_Y HhallT)
          as [mT [HmT_Y [HmT_nbrs HmT_inj]]].
        (* N(T) = image of T under mT *)
        pose (NT := fun y => In R (set_neighbors nbrs T) y).
        (* Define X'' = X \ T *)
        pose (X'' := fun x => In L X x /\ ~ In L T x).
        (* |X''| < S nx' since T is inhabited (|T| ≥ 1) *)
        (* First get |X''| *)
        assert (HfinX : Finite L X) by exact (cardinal_finite L X (S nx') Hcard_X).
        assert (HfinX'' : Finite L X'') by exact (Finite_downward_closed L X HfinX X'' (fun x [Hx _] => Hx)).
        destruct (finite_cardinal L X'' HfinX'') as [nX'' HcardX''].
        assert (HX''_lt : nX'' < S nx').
        { destruct nt as [| nt'].
          - (* T is inhabited but |T| = 0: contradiction *)
            destruct HinhT as [a Ha]. inversion HcardT. subst. inversion Ha.
          - (* |T| ≥ 1 *)
            (* |X''| + |T| ≤ |X| = S nx' and |T| ≥ 1, so |X''| ≤ nx' < S nx' *)
            assert (Hle : nX'' + S nt' <= S nx').
            { apply (incl_card_le L (fun x => In L X'' x \/ In L T x) X).
              - (* |X'' ∪ T| ≥ nX'' + S nt' *)
                (* This needs a disjoint union lemma. Admit for now. *)
                admit.
              - exact Hcard_X.
              - intros x [Hx | Hx].
                + exact (proj1 Hx).
                + exact (HinclT x Hx). }
            lia. }
        (* Define nbrs'' : L -> Ensemble R — restricted neighbors avoiding N(T) *)
        pose (nbrs'' := fun x z => In R (nbrs x) z /\ ~ In R NT z).
        (* HallCondition for X'' with nbrs'' *)
        assert (Hhall'' : HallCondition X'' nbrs'').
        { intros S ns nn HinclS HcardS HcardNS.
          (* N''(S) = N(S) \ N(T) *)
          (* Hall on S ∪ T ⊆ X: |N(S ∪ T)| ≥ |S ∪ T| = |S| + |T| *)
          (* |N''(S)| = |N(S ∪ T)| - |N(T)| ≥ |S| + |T| - |T| = |S| *)
          admit. }
        (* nbrs''(x) ⊆ Y \ N(T) *)
        assert (Hnbrs'' : forall x y, In L X'' x -> In R (nbrs'' x) y -> In R (fun z => In R Y z /\ ~ In R NT z) y).
        { intros x y [Hx _] [Hy Hnot]. split; [exact (Hnbrs_Y x y Hx Hy) | exact Hnot]. }
        (* Y \ N(T) is finite *)
        assert (HfinY'' : Finite R (fun z => In R Y z /\ ~ In R NT z)).
        { exact (Finite_downward_closed R Y HfinY _ (fun z [Hz _] => Hz)). }
        destruct (IH nX'' HX''_lt X'' (fun z => In R Y z /\ ~ In R NT z) nbrs''
                     HcardX'' HfinY''
                     (fun x y Hx Hy => Hnbrs'' x y Hx Hy)
                     Hhall'')
          as [m'' [Hm''_Y [Hm''_nbrs Hm''_inj]]].
        (* Combine mT and m'' into m *)
        pose (m := fun x =>
          if (classic_dec (In L T x)) then mT x else m'' x).
        exists m.
        (* Verify m is a perfect matching — admit for task 4 details *)
        admit.
      + (* --- Non-tight case --- *)
        (* Every proper non-empty S ⊊ X has |N(S)| > |S| *)
        assert (Hstrict : forall S ns nn,
          Inhabited L S -> S <> X -> Included L S X ->
          cardinal L S ns -> cardinal R (set_neighbors nbrs S) nn ->
          nn > ns).
        { intros S ns nn HinhS HneqS HinclS HcardS HcardNS.
          destruct (Nat.lt_or_ge ns nn) as [Hlt | Hge]; [exact Hlt |].
          exfalso. apply Hntight.
          assert (Hnn_le : nn <= ns) by exact Hge.
          assert (Hns_le : ns <= nn) by exact (Hhall S ns nn HinclS HcardS HcardNS).
          assert (Heq : nn = ns) by lia.
          exists S. exact (conj HinhS (conj HneqS (conj HinclS (ex_intro _ ns (ex_intro _ nn (conj HcardS (conj HcardNS (eq_sym Heq)))))))).  }
        (* Pick x0 ∈ X *)
        destruct Hinhab_X as [x0 Hx0].
        (* nbrs(x0) is non-empty since |N({x0})| ≥ 1 *)
        assert (Hnbrs_ne : Inhabited R (nbrs x0)).
        { destruct (classic (Inhabited R (nbrs x0))) as [H | H]; [exact H |].
          exfalso.
          assert (Hcard_nbrs_x0 : cardinal R (set_neighbors nbrs (Singleton L x0)) 0).
          { apply (cardinal_extensional_poly R (Empty_set R)); [| apply card_empty].
            intros y. split; [intro Hy; inversion Hy | intros [z [Hz _]]; inversion Hz; subst z].
            apply H. apply Inhabited_intro with y. inversion Hz. subst. admit. }
          assert (Hcard_x0 : cardinal L (Singleton L x0) 1).
          { replace 1 with (S 0) by reflexivity.
            apply card_add; [apply card_empty | intro Hc; inversion Hc]. }
          assert (H1le0 : 1 <= 0).
          { apply (Hhall (Singleton L x0) 1 0).
            - intros z Hz. inversion Hz. subst. exact Hx0.
            - exact Hcard_x0.
            - exact Hcard_nbrs_x0. }
          lia. }
        destruct Hinhab_R as [y0 Hy0_nbrs].
        (* Define X' = X \ {x0}, nbrs' = nbrs with y0 removed *)
        pose (X' := fun x => In L X x /\ x <> x0).
        pose (nbrs' := fun x z => In R (nbrs x) z /\ z <> y0).
        (* |X'| = nx' *)
        assert (HcardX' : cardinal L X' nx').
        { exact (cardinal_remove L X x0 nx' Hx0 Hcard_X). }
        (* Finite Y \ {y0} *)
        assert (HfinY' : Finite R (fun z => In R Y z /\ z <> y0)).
        { exact (Finite_downward_closed R Y HfinY _ (fun z [Hz _] => Hz)). }
        (* nbrs'(x) ⊆ Y \ {y0} *)
        assert (Hnbrs' : forall x y, In L X' x -> In R (nbrs' x) y ->
            In R (fun z => In R Y z /\ z <> y0) y).
        { intros x y [Hx _] [Hy Hneq].
          split; [exact (Hnbrs_Y x y Hx Hy) | exact Hneq]. }
        (* HallCondition X' nbrs' *)
        assert (Hhall' : HallCondition X' nbrs').
        { intros S ns nn HinclS HcardS HcardNS.
          destruct ns as [| ns'].
          - lia.
          - (* S non-empty, S ⊆ X' ⊊ X, so |N(S)| > |S| *)
            assert (HinhS : Inhabited L S).
            { inversion HcardS as [| S' n' Hcard' s Hs_notin]. subst.
              apply Inhabited_intro with s. apply Union_intror. apply In_singleton. }
            assert (HneqS : S <> X).
            { intro Heq. subst S.
              (* S = X but S ⊆ X' = X \ {x0} → x0 ∉ S → x0 ∉ X, contradiction *)
              assert (Hx0_not : ~ In L X x0).
              { intro Hx0'. apply (HinclS x0 Hx0'). exact (conj Hx0' (fun h => h)). }
              (* Hmm: HinclS : Included L X X', so x0 ∈ X and HinclS x0 Hx0 : In L X' x0 *)
              (* X' = X \ {x0}, so In L X' x0 gives x0 ≠ x0 — contradiction *)
              pose proof (HinclS x0 Hx0) as [_ Hneq].
              exact (Hneq eq_refl). }
            assert (HinclSX : Included L S X).
            { intros x Hx. exact (proj1 (HinclS x Hx)). }
            (* Compute |N(S)| *)
            assert (HfinS : Finite R (set_neighbors nbrs S)).
            { apply (Finite_downward_closed R Y HfinY).
              intros y [x [Hx Hy]]. exact (Hnbrs_Y x y (HinclSX x Hx) Hy). }
            destruct (finite_cardinal R (set_neighbors nbrs S) HfinS) as [nsN HcardNS_orig].
            (* By Hstrict: nsN > S ns' *)
            assert (HnsN_gt : nsN > S ns').
            { exact (Hstrict S (S ns') nsN HinhS HneqS HinclSX HcardS HcardNS_orig). }
            (* N'(S) = N(S) \ {y0}, |N'(S)| ≥ |N(S)| - 1 ≥ S ns' *)
            rewrite set_neighbors_remove_point in HcardNS.
            (* |{z | z ∈ N(S) ∧ z ≠ y0}| = nn *)
            (* |N(S)| - 1 ≤ nn ≤ |N(S)| *)
            assert (Hnn_le : nn <= nsN).
            { apply (incl_card_le R _ (set_neighbors nbrs S) nn nsN HcardNS HcardNS_orig).
              intros z [Hz _]. exact Hz. }
            (* Also nn ≥ nsN - 1 ≥ S ns' *)
            lia. } (* nn ≥ nsN - 1 ≥ (S ns' + 1) - 1 = S ns' — need: nn ≥ nsN - 1 *)
            (* Actually we need: nn = nsN or nn = nsN - 1 depending on whether y0 ∈ N(S) *)
            (* In either case nn ≥ nsN - 1 ≥ S ns' *)
            (* The lia above doesn't close it without nn ≥ nsN - 1. Need extra step. *)
        (* Apply IH to X' *)
        destruct (IH nx' (Nat.lt_succ_diag_r nx') X'
                     (fun z => In R Y z /\ z <> y0) nbrs'
                     HcardX' HfinY' Hnbrs' Hhall')
          as [m' [Hm'_Y [Hm'_nbrs Hm'_inj]]].
        (* Define m : X → Y by m(x0) = y0, m(x) = m'(x) for x ∈ X' *)
        pose (m := fun x =>
          if (classic_dec (x = x0)) then y0 else m' x).
        exists m.
        (* Verify perfect matching — details admitted for Task 5 *)
        admit.
  Qed.
```

**Note:** This skeleton has several `admit`s marking sub-goals to fill in Tasks 4 and 5. The structure and branching logic are complete.

- [ ] **Step 2: Build**

Run: `dune build posets/dilworth/Hall.vo`
Expected: success (admits are fine)

- [ ] **Step 3: Commit**

```bash
git add posets/dilworth/Hall.v
git commit -m "feat: add Hall theorem proof skeleton with tight/non-tight split"
```

---

### Task 4: Hall theorem — fill non-tight case admits

**Files:**
- Modify: `posets/dilworth/Hall.v`

Fill the admits in the non-tight branch. The non-tight IH call is already set up; what remains:
1. `HallCondition X' nbrs'` verification (the `lia` gap)
2. The combined matching `m` being a perfect matching

- [ ] **Step 1: Fix the HallCondition X' nbrs' proof**

Replace the `lia` tactic (and surrounding `Hhall'` proof) with:

```coq
        assert (Hhall' : HallCondition X' nbrs').
        { intros S ns nn HinclS HcardS HcardNS.
          (* N'(S) = N(nbrs)(S) \ {y₀} *)
          rewrite set_neighbors_remove_point in HcardNS.
          destruct ns as [| ns'].
          - (* S = ∅: 0 ≤ nn trivially *) lia.
          - (* S non-empty *)
            assert (HinhS : Inhabited L S).
            { inversion HcardS as [| S' n' _ s _]. subst.
              apply Inhabited_intro with s. apply Union_intror. apply In_singleton. }
            assert (HneqS : S <> X).
            { intro Heq. subst S. destruct (HinclS x0 Hx0) as [_ Habs]. exact (Habs eq_refl). }
            assert (HinclSX : Included L S X) by (intros x Hx; exact (proj1 (HinclS x Hx))).
            (* Get cardinal of N_orig(S) *)
            assert (HfinNS : Finite R (set_neighbors nbrs S)).
            { apply (Finite_downward_closed R Y HfinY).
              intros y [x [Hx Hy]]. exact (Hnbrs_Y x y (HinclSX x Hx) Hy). }
            destruct (finite_cardinal R (set_neighbors nbrs S) HfinNS) as [nsN HcardNS_orig].
            (* By non-tight: nsN > S ns' *)
            assert (HnsN_gt : nsN > S ns').
            { exact (Hstrict S (S ns') nsN HinhS HneqS HinclSX HcardS HcardNS_orig). }
            (* {z ∈ N(S) | z ≠ y₀} has cardinality either nsN or nsN - 1 *)
            assert (Hnn_bounds : nn = nsN \/ nn = nsN - 1).
            { destruct (classic (In R (set_neighbors nbrs S) y0)) as [Hy0_in | Hy0_out].
              - (* y₀ ∈ N(S): removing it decreases cardinality by 1 *)
                right.
                assert (HcardNS' : cardinal R (fun z => In R (set_neighbors nbrs S) z /\ z <> y0) (nsN - 1)).
                { destruct nsN as [| nsN']. { inversion HcardNS_orig. subst. inversion Hy0_in. }
                  simpl. exact (cardinal_remove R (set_neighbors nbrs S) y0 nsN' Hy0_in HcardNS_orig). }
                apply Nat.le_antisymm;
                [exact (incl_card_le R _ _ nn (nsN-1) HcardNS HcardNS' (fun z Hz => Hz)) |
                 exact (incl_card_le R _ _ (nsN-1) nn HcardNS' HcardNS (fun z Hz => Hz))].
              - (* y₀ ∉ N(S): removing it doesn't change cardinality *)
                left.
                apply Nat.le_antisymm;
                [exact (incl_card_le R _ (set_neighbors nbrs S) nn nsN HcardNS HcardNS_orig (fun z [Hz _] => Hz)) |].
                apply (incl_card_le R (set_neighbors nbrs S) _ nsN nn HcardNS_orig HcardNS).
                intros z Hz. split; [exact Hz | intro Heq; subst z; exact (Hy0_out Hz)]. }
            lia. }
```

- [ ] **Step 2: Fill the combined matching m verification**

Replace the final `admit` in the non-tight branch with:

```coq
        (* m(x0) = y0, m(x) = m'(x) for x ≠ x0 *)
        exists m.
        split; [| split].
        - (* m(x) ∈ Y *)
          intros x Hx.
          unfold m. destruct (classic_dec (x = x0)) as [Heq | Hneq].
          + (* x = x0: m(x0) = y0 ∈ Y *)
            exact (Hnbrs_Y x0 y0 Hx0 Hy0_nbrs).
          + (* x ≠ x0: m(x) = m'(x) ∈ Y \ {y0} ⊆ Y *)
            destruct (Hm'_Y x (conj Hx Hneq)) as [Hy _]. exact Hy.
        - (* m(x) ∈ nbrs(x) *)
          intros x Hx.
          unfold m. destruct (classic_dec (x = x0)) as [Heq | Hneq].
          + subst x. exact Hy0_nbrs.
          + destruct (Hm'_nbrs x (conj Hx Hneq)) as [Hnbr _]. exact Hnbr.
        - (* m injective *)
          intros x1 x2 Hx1 Hx2 Heq_m.
          unfold m in Heq_m.
          destruct (classic_dec (x1 = x0)) as [Heq1 | Hneq1];
          destruct (classic_dec (x2 = x0)) as [Heq2 | Hneq2].
          + subst x1. subst x2. reflexivity.
          + (* m(x0) = y0 = m'(x2), but m'(x2) ∈ Y \ {y0}: contradiction *)
            subst x1.
            destruct (Hm'_Y x2 (conj Hx2 Hneq2)) as [_ Hy0_neq].
            exact (False_ind _ (Hy0_neq Heq_m)).
          + subst x2.
            destruct (Hm'_Y x1 (conj Hx1 Hneq1)) as [_ Hy0_neq].
            exact (False_ind _ (Hy0_neq (eq_sym Heq_m))).
          + (* Both in X': use m' injectivity *)
            exact (Hm'_inj x1 x2 (conj Hx1 Hneq1) (conj Hx2 Hneq2) Heq_m).
```

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/Hall.vo`
Expected: success (tight case still admitted)

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/Hall.v
git commit -m "feat: fill non-tight case of Hall's theorem proof"
```

---

### Task 5: Hall theorem — fill tight case admits

**Files:**
- Modify: `posets/dilworth/Hall.v`

Fill the admits in the tight branch. The key goals:
1. `|X''| < S nx'` (using `nX'' + nt ≤ S nx'` and `nt ≥ 1`)
2. `HallCondition X'' nbrs''` (using Hall on `S ∪ T`)
3. Combined matching `m` is a perfect matching

- [ ] **Step 1: Fill `|X''| < S nx'`**

Replace the disjoint union `admit` with:

```coq
        (* To show nX'' + S nt' ≤ S nx', use: X'' ∪ T ⊆ X and |X''| + |T| ≤ |X| *)
        (* X'' and T are disjoint, so |X'' ∪ T| = |X''| + |T| *)
        assert (Hcard_union : cardinal L (fun x => In L X'' x \/ In L T x) (nX'' + S nt')).
        { (* X'' ∩ T = ∅ by definition of X'' = X \ T *)
          (* Prove by induction on HcardX'' then apply card_add repeatedly *)
          (* Alternative: use cardinal_disjoint_union *)
          (* Build up: X'' ∪ T has card nX'' + nt *)
          admit. (* see Note below *) }
        exact (incl_card_le L _ X _ _ Hcard_union Hcard_X
          (fun x [Hx | Hx] => [exact (proj1 Hx) | exact (HinclT x Hx)])). }
```

**Note:** The disjoint cardinal union lemma (`|A ∪ B| = |A| + |B|` when `A ∩ B = ∅`) is not in the existing codebase. Add it as a helper lemma earlier in `Hall.v`:

```coq
  (* If A and B are disjoint (A ∩ B = ∅) and |A|=n, |B|=m, then |A ∪ B| = n+m *)
  Lemma cardinal_disjoint_union : forall (S T : Ensemble L) n m,
    (forall x, In L S x -> ~ In L T x) ->
    cardinal L S n ->
    cardinal L T m ->
    cardinal L (Union L S T) (n + m).
  Proof.
    intros S T n m Hdisj HcardS HcardT.
    revert T m Hdisj HcardT.
    induction HcardS as [| S' n' HcardS' IH a Ha_notin]; intros T m Hdisj HcardT.
    - (* |S| = 0: Union ∅ T = T *)
      simpl.
      apply (cardinal_extensional_poly L T); [| exact HcardT].
      intros x. split.
      + intro Hx. apply Union_intror. exact Hx.
      + intro Hx. inversion Hx as [z Hz | z Hz]; subst.
        * inversion Hz.
        * exact Hz.
    - (* |S| = S n' *)
      simpl.
      (* Union (Add S' a) T = Add (Union S' T) a *)
      apply (cardinal_extensional_poly L (Add L (Union L S' T) a)).
      + intros x. split.
        * intro Hx. unfold Add in Hx.
          inversion Hx as [z Hz | z Hz]; subst.
          -- inversion Hz as [w Hw | w Hw]; subst.
             ++ unfold Add. apply Union_introl. apply Union_introl. exact Hw.
             ++ unfold Add. apply Union_introl. apply Union_intror. exact Hw.
          -- inversion Hz. subst. unfold Add. apply Union_intror. apply In_singleton.
        * intro Hx. unfold Add in Hx.
          inversion Hx as [z Hz | z Hz]; subst.
          -- inversion Hz as [w Hw | w Hw]; subst.
             ++ unfold Add. apply Union_introl. unfold Add. apply Union_introl. exact Hw.
             ++ apply Union_intror. exact Hw.
          -- inversion Hz. subst. unfold Add. apply Union_introl. unfold Add. apply Union_intror. apply In_singleton.
      + apply card_add.
        * apply IH.
          -- intros x Hx. exact (Hdisj x (Union_introl _ _ _ _ Hx)).
          -- exact HcardT.
        * intro Hcontra.
          inversion Hcontra as [z Hz | z Hz]; subst.
          -- exact (Ha_notin Hz).
          -- exact (Hdisj a (Union_intror _ _ _ _ (In_singleton _ _ _)) Hz).
  Qed.
```

- [ ] **Step 2: Fill `HallCondition X'' nbrs''`**

Replace the `Hhall''` admit:

```coq
        assert (Hhall'' : HallCondition X'' nbrs'').
        { intros S ns nn HinclS HcardS HcardNS.
          (* nbrs'' = nbrs ∩ complement N(T), so N''(S) = N(S) \ N(T) *)
          rewrite set_neighbors_remove_set in HcardNS.
          (* N(S ∪ T) = N(S) ∪ N(T) *)
          (* |N(S ∪ T)| ≥ |S ∪ T| = |S| + |T| by Hall on S ∪ T ⊆ X *)
          (* |N''(S)| = |N(S) \ N(T)| = |N(S ∪ T)| - |N(T)| ≥ |S| + |T| - |T| = |S| *)
          (* Step 1: S ∩ T = ∅ (since S ⊆ X'' = X \ T) *)
          assert (Hdisj : forall x, In L S x -> ~ In L T x).
          { intros x Hx. destruct (HinclS x Hx) as [_ Hnot]. exact Hnot. }
          (* Step 2: S ∪ T ⊆ X *)
          assert (HinclST_X : Included L (Union L S T) X).
          { intros x Hx. inversion Hx as [z Hz | z Hz]; subst.
            - exact (proj1 (HinclS z Hz)).
            - exact (HinclT z Hz). }
          (* Step 3: |S ∪ T| = ns + nt *)
          assert (HcardST : cardinal L (Union L S T) (ns + nt)).
          { exact (cardinal_disjoint_union S T ns nt Hdisj HcardS HcardT). }
          (* Step 4: N(S ∪ T) has some cardinal nST ≥ ns + nt *)
          assert (HfinST_N : Finite R (set_neighbors nbrs (Union L S T))).
          { apply (Finite_downward_closed R Y HfinY).
            intros y [x [Hx Hy]]. exact (Hnbrs_Y x y (HinclST_X x Hx) Hy). }
          destruct (finite_cardinal R (set_neighbors nbrs (Union L S T)) HfinST_N) as [nST HcardST_N].
          assert (HnST_ge : nST >= ns + nt).
          { exact (Hhall (Union L S T) (ns + nt) nST HinclST_X HcardST HcardST_N). }
          (* Step 5: N(S ∪ T) = N(S) ∪ N(T) *)
          assert (HeqST : set_neighbors nbrs (Union L S T) =
                          Union R (set_neighbors nbrs S) (set_neighbors nbrs T)).
          { exact (set_neighbors_union nbrs S T). }
          (* Step 6: N(T) ⊆ N(S ∪ T), so |N(S ∪ T)| - |N(T)| = |N(S ∪ T) \ N(T)| *)
          (* And N(S ∪ T) \ N(T) = N(S) \ N(T) = N''(S) *)
          (* Step 7: |N(T)| = nt (from HcardNT) *)
          (* Step 8: nn = |N''(S)| ≥ nST - nt ≥ (ns + nt) - nt = ns *)
          assert (Hnn_bounds : nn <= nST - nt).
          { (* N''(S) ⊆ N(S ∪ T) \ N(T) *)
            admit. (* Cardinality of set difference argument *) }
          lia. }
```

- [ ] **Step 3: Fill the combined matching verification for tight case**

Replace the final tight-branch admit with:

```coq
        (* m = mT on T, m = m'' on X'' *)
        exists m.
        split; [| split].
        - (* m(x) ∈ Y *)
          intros x Hx.
          unfold m. destruct (classic_dec (In L T x)) as [HxT | HxnT].
          + (* x ∈ T: m(x) = mT(x) ∈ N(T) ⊆ Y *)
            exact (Hnbrs_Y x (mT x) Hx (HmT_nbrs x HxT)).
          + (* x ∈ X'': m(x) = m''(x) ∈ Y \ N(T) ⊆ Y *)
            assert (HxX'' : In L X'' x) by exact (conj Hx HxnT).
            destruct (Hm''_Y x HxX'') as [Hy _]. exact Hy.
        - (* m(x) ∈ nbrs(x) *)
          intros x Hx.
          unfold m. destruct (classic_dec (In L T x)) as [HxT | HxnT].
          + exact (HmT_nbrs x HxT).
          + assert (HxX'' : In L X'' x) by exact (conj Hx HxnT).
            destruct (Hm''_nbrs x HxX'') as [Hnbr _]. exact Hnbr.
        - (* m injective *)
          intros x1 x2 Hx1 Hx2 Heq.
          unfold m in Heq.
          destruct (classic_dec (In L T x1)) as [Hx1T | Hx1nT];
          destruct (classic_dec (In L T x2)) as [Hx2T | Hx2nT].
          + (* Both in T: use mT injectivity *)
            exact (HmT_inj x1 x2 Hx1T Hx2T Heq).
          + (* x1 ∈ T, x2 ∈ X'': mT(x1) ∈ N(T), m''(x2) ∈ Y \ N(T): contradiction *)
            exfalso.
            assert (HmT_NT : In R NT (mT x1)).
            { exists x1. split; [exact Hx1T | exact (HmT_nbrs x1 Hx1T)]. }
            assert (Hm''_notNT : ~ In R NT (m'' x2)).
            { destruct (Hm''_Y x2 (conj Hx2 Hx2nT)) as [_ Hnot]. exact Hnot. }
            rewrite <- Heq in Hm''_notNT. exact (Hm''_notNT HmT_NT).
          + exfalso.
            assert (HmT_NT : In R NT (mT x2)).
            { exists x2. split; [exact Hx2T | exact (HmT_nbrs x2 Hx2T)]. }
            assert (Hm''_notNT : ~ In R NT (m'' x1)).
            { destruct (Hm''_Y x1 (conj Hx1 Hx1nT)) as [_ Hnot]. exact Hnot. }
            rewrite Heq in Hm''_notNT. exact (Hm''_notNT HmT_NT).
          + (* Both in X'': use m'' injectivity *)
            exact (Hm''_inj x1 x2 (conj Hx1 Hx1nT) (conj Hx2 Hx2nT) Heq).
```

- [ ] **Step 4: Build with no remaining admits in Hall.v**

Run: `dune build posets/dilworth/Hall.vo`
Expected: success

If any goals remain, fix them inline. The common remaining issues are:
- `N(T) ⊆ N(S ∪ T) \ N(T)` cardinality: use `incl_card_le` after establishing the set inclusion
- Cardinal of `X'' ∪ T`: use `cardinal_disjoint_union`

- [ ] **Step 5: Commit**

```bash
git add posets/dilworth/Hall.v
git commit -m "feat: complete Hall's marriage theorem proof"
```

---

### Task 6: Add `min_elements_eq_la` to `WidthUpperBound.v`

**Files:**
- Modify: `posets/dilworth/WidthUpperBound.v`

Add `From Dilworth Require Import Hall` to imports. Then add helper lemma.

- [ ] **Step 1: Add Hall import**

Change line 4 of `WidthUpperBound.v` from:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers.
```
to:
```coq
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas WidthLowerBound Helpers Hall.
```

- [ ] **Step 2: Add `min_elements_eq_la`**

Add this lemma in the `DilworthBackward` section, after the existing helpers (around line 78, before the "Special Cases" block):

```coq
  (* Minimal elements of sub (when sub ⊆ Above(la)) are exactly la *)
  Lemma min_elements_eq_la : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    forall x, In A sub x ->
      ((forall y, In A sub y -> R y x -> y = x) <-> In A la x).
  Proof.
    intros sub la w Hla Habove x Hx.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    split.
    - (* x minimal in sub → x ∈ la *)
      intro Hmin.
      (* x ∈ Above(la): ∃ a ∈ la with R a x *)
      destruct (Habove x Hx) as [a [Ha_la Hax]].
      (* a ∈ la ⊆ sub, R a x, and x minimal → a = x *)
      assert (Ha_sub : In A sub a) by exact (Hincl_la a Ha_la).
      assert (Haeqx : a = x) by exact (Hmin a Ha_sub Hax).
      subst a. exact Ha_la.
    - (* x ∈ la → x minimal in sub *)
      intro Hx_la.
      intros y Hy_sub Hyx.
      (* R y x and x ∈ la ⊆ sub, y ∈ sub ⊆ Above(la) *)
      destruct (Habove y Hy_sub) as [b [Hb_la Hby]].
      (* R b y and R y x → R b x; since b ∈ la and x ∈ la and la antichain → b = x *)
      assert (Hbx : R b x) by exact (poset_trans b y x Hby Hyx).
      assert (Hbeqx : b = x) by exact (Hincompat b x Hb_la Hx_la (or_introl Hbx)).
      subst b.
      (* R x y and R y x → x = y by antisymmetry *)
      exact (poset_antisym y x Hyx Hby).
  Qed.
```

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/WidthUpperBound.vo`
Expected: success

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/WidthUpperBound.v
git commit -m "feat: add min_elements_eq_la helper to WidthUpperBound"
```

---

### Task 7: Add `dilworth_hall_defect` to `WidthUpperBound.v`

**Files:**
- Modify: `posets/dilworth/WidthUpperBound.v`

This lemma establishes Hall's defect condition for the Dilworth strict-order bipartite graph: `|S| ≤ |N_strict(S)| + w` for all `S ⊆ sub`.

- [ ] **Step 1: Add `dilworth_hall_defect`**

Add after `min_elements_eq_la`:

```coq
  (* N_strict(S) = strict successors of S within sub *)
  Definition StrictSucc (sub S : Ensemble A) : Ensemble A :=
    fun y => In A sub y /\ exists x, In A S x /\ R x y /\ x <> y.

  (* Hall defect: |S| ≤ |N_strict(S)| + w for all S ⊆ sub *)
  (* Equivalently: the antichain of elements of S with no strict successor has size ≤ w *)
  Lemma dilworth_hall_defect : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    forall S ns nn,
      Included A S sub ->
      cardinal A S ns ->
      cardinal A (StrictSucc sub S) nn ->
      ns <= nn + w.
  Proof.
    intros sub la w Hla Habove S ns nn HinclS HcardS HcardNS.
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [_ Hincompat].
    (* Let M = {x ∈ S | x has no strict successor in S} = S ∩ (S \ N_strict(S)) *)
    (* M is an antichain: if x, y ∈ M and R x y, then y is a strict successor of x, 
       contradicting x ∈ M *)
    pose (M := fun x => In A S x /\ ~ In A (StrictSucc sub S) x).
    assert (HM_anti : IsAntichain R M).
    { split.
      - (* M is inhabited if S is, but M might be empty. Use a singleton if S non-empty? *)
        (* Actually M might be empty. IsAntichain requires Inhabited. *)
        (* We need a different approach: show |M| ≤ w without M being an antichain *)
        admit. (* See alternative below *)
      - intros x y [HxS HxnM] [HyS HynM] Hcomp.
        (* If R x y and x ≠ y: y is a strict successor of x, so x ∈ N_strict(S): contradiction *)
        (* If R y x and y ≠ x: x is a strict successor of y, so y ∈ N_strict(S): contradiction *)
        (* If x = y: done *)
        destruct Hcomp as [Hxy | Hyx].
        + destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
          exfalso. apply HxnM. unfold StrictSucc.
          exact (conj (HinclS x HxS)
                      (ex_intro _ x (conj HxS (conj Hxy Hneq)))).
        + destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
          exfalso. apply HynM. unfold StrictSucc.
          exact (conj (HinclS y HyS)
                      (ex_intro _ y (conj HyS (conj Hyx (fun h => Hneq (eq_sym h)))))).  }
    (* |M| ≤ w since M is an antichain in sub *)
    ...
    (* |S| = |M| + |N_strict(S)| ... actually not quite *)
    (* Better: injection from S into M ∪ N_strict(S) *)
    (* Each x ∈ S either has a strict successor (injection into N_strict(S)) or is in M *)
    (* So |S| ≤ |M| + |N_strict(S)| ≤ w + nn *)
    admit.
  Qed.
```

**Note:** The proof strategy is:
1. Define `M = {x ∈ S | x has no strict successor in S ∩ sub}`  
2. Show `M` is an antichain in `sub` (elements of `M` are pairwise incomparable, since if `R x y` with `x,y ∈ M`, `x ≠ y`, then `y` is a strict successor of `x`, contradicting `x ∈ M`)
3. Since `M ⊆ S ⊆ sub`, `|M| ≤ w`
4. Injection `S → M ∪ N_strict(S)`: for `x ∈ S`, if no strict successor → `x ∈ M`; else pick a strict successor `f(x) ∈ N_strict(S)`; this gives `|S| ≤ |M| + |N_strict(S)| ≤ w + nn`

The `IsAntichain` class requires `Inhabited`, so handle the empty case separately or use `InjectionPrinciple.cardinal_injection_principle_poly` directly without antichain packaging.

- [ ] **Step 2: Complete the proof**

Replace the admits using the strategy above:

```coq
    (* Simpler approach: injection from (S \ N_strict(S)) into la *)
    (* If x ∈ S and x ∉ N_strict(S), then x has no strict successor in S.
       We'll show x must be minimal in sub, hence x ∈ la. *)
    (* But this isn't quite right either: x might have strict successors in sub but not in S *)
    
    (* Correct approach: show S \ N_strict(S) has cardinality ≤ w *)
    (* S \ N_strict(S) = elements of S with no strict predecessor in S *)
    (* Wait, N_strict(S) = successors OF S, not predecessors. Let me re-check. *)
    
    (* N_strict(S) = {y ∈ sub | ∃ x ∈ S, R x y ∧ x ≠ y} = strict successors of S *)
    (* M = S \ N_strict(S) = {x ∈ S | x is not a strict successor of any element of S} *)
    
    (* Key: M is an antichain. Proof: if x, y ∈ M with R x y and x ≠ y, *)
    (* then y is a strict successor of x ∈ S, so y ∈ N_strict(S), *)
    (* contradicting y ∈ M = S \ N_strict(S). *)
    
    (* So |M| ≤ w. *)
    (* And |S| ≤ |M| + |N_strict(S)| = |M| + nn ≤ w + nn. *)
    
    (* This needs: |S| ≤ |M| + |N_strict(S)| *)
    (* Injection S → M ∪ N_strict(S): each x ∈ S maps to itself (in M or N_strict(S)) *)
    (* Wait, S ⊆ M ∪ N_strict(S)? Not necessarily. *)
    
    (* Actually: for each x ∈ S:
       Case 1: x ∉ N_strict(S) → x ∈ M
       Case 2: x ∈ N_strict(S) → x ∈ N_strict(S)
       So S ⊆ M ∪ N_strict(S). ✓ *)
    (* But M and N_strict(S) may overlap (x ∈ S ∩ N_strict(S) but no successor in S). *)
    (* |M ∪ N_strict(S)| ≤ |M| + |N_strict(S)|. And |S| ≤ |M ∪ N_strict(S)|. *)
    (* So |S| ≤ |M| + nn ≤ w + nn. ✓ *)
```

The full proof uses `incl_card_le` and the injection principle. Fill in the details.

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/WidthUpperBound.vo`
Expected: success

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/WidthUpperBound.v
git commit -m "feat: add dilworth_hall_defect helper"
```

---

### Task 8: Prove `above_chain_assignment_exists`

**Files:**
- Modify: `posets/dilworth/WidthUpperBound.v`

Replace the `Admitted` in `above_chain_assignment_exists` (line ~499) with a complete proof using Hall's theorem.

**Strategy:**
1. Build augmented bipartite graph: left = `sub`, right = `sum A A`
   - `inl y` for `y ∈ sub` (strict successors)
   - `inr a` for `a ∈ la` (chain label dummies)
2. Verify Hall's condition using `dilworth_hall_defect`
3. Apply `Hall.hall_marriage_theorem` to get `m_aug : A → sum A A`
4. Define `f : A → A` by following `m_aug` backwards to la-elements
5. Show fibers are chains

- [ ] **Step 1: Define the augmented graph types and neighbors**

In the proof of `above_chain_assignment_exists`, after the `intros`:

```coq
  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    exists f : A -> A,
      (forall x, In A sub x -> In A la (f x) /\ R (f x) x) /\
      (forall a, In A la a -> IsChain R (fun x => In A sub x /\ f x = a)).
  Proof.
    intros sub la w Hla Habove.
    assert (Hla' := Hla).
    destruct Hla as [Hanti Hincl_la Hcard_la Hmax].
    destruct Hanti as [Hinhab_la Hincompat].
    (* Augmented right type: sum A A *)
    (* Left: sub (type A). Right: sum A A. *)
    (* Right set Y_aug: {inl y | y ∈ sub} ∪ {inr a | a ∈ la} *)
    pose (Y_aug : Ensemble (sum A A) :=
      fun z => match z with
        | inl y => In A sub y
        | inr a => In A la a
      end).
    (* Augmented neighbors: nbrs_aug(x) = {inl y | y ∈ sub, R x y, x ≠ y} ∪ {inr a | a ∈ la} *)
    pose (nbrs_aug : A -> Ensemble (sum A A) := fun x z =>
      match z with
        | inl y => In A sub y /\ R x y /\ x <> y
        | inr a => In A la a
      end).
    (* Y_aug is finite *)
    assert (HfinY : Finite (sum A A) Y_aug).
    { (* Y_aug = image_inl(sub) ∪ image_inr(la), both finite *)
      admit. }
    (* nbrs_aug(x) ⊆ Y_aug *)
    assert (Hnbrs_Y : forall x z, In A sub x -> In (sum A A) (nbrs_aug x) z -> In (sum A A) Y_aug z).
    { intros x z Hx Hz. destruct z as [y | a]; simpl in *.
      - exact (proj1 Hz).
      - exact Hz. }
    (* Hall's condition for the augmented graph *)
    assert (HcardX : exists nx, cardinal A sub nx).
    { destruct (classic (Finite A sub)) as [Hfin | Hnfin].
      - destruct (finite_cardinal A sub Hfin) as [n Hn]. exact (ex_intro _ n Hn).
      - (* sub is infinite? No: la ⊆ sub ⊆ Above(la), and we have a finite la cardinal *)
        admit. }
    destruct HcardX as [nx HcardX].
    assert (Hhall : @Hall.HallCondition A (sum A A) sub nbrs_aug).
    { intros S ns nn HinclS HcardS HcardNS.
      (* N_aug(S) = N_strict(S) ∪ {inr a | a ∈ la} *)
      (* |N_aug(S)| = |N_strict(S)| + w *)
      (* By dilworth_hall_defect: ns ≤ |N_strict(S)| + w = nn *)
      admit. }
    (* Apply Hall's theorem *)
    destruct (@Hall.hall_marriage_theorem A (sum A A) sub Y_aug nx nbrs_aug
                HcardX HfinY Hnbrs_Y Hhall)
      as [m_aug [Hmaug_Y [Hmaug_nbrs Hmaug_inj]]].
    (* From m_aug, define f *)
    (* Key observation: la-elements map to inr (their label) *)
    (* For a ∈ la: m_aug(a) ∈ nbrs_aug(a) = {inl y | R a y, a ≠ y} ∪ {inr b | b ∈ la} *)
    (* la-elements are minimal in sub, so they have no strict successors... wait, *)
    (* Actually la-elements DO have strict successors (elements above them in sub). *)
    (* The matching might send a ∈ la to either inl(successor) or inr(label). *)
    (* We can't guarantee a maps to inr(a) without more argument. *)
    
    (* Alternative: define f(x) = the la-element of x's chain differently. *)
    (* From the matching m_aug, we define a successor function on sub. *)
    (* Then f(x) = the la-element reachable by following successors backwards. *)
    
    (* For the plan: use the following approach:
       - m_aug maps sub injectively into sub ∪ la (using sum A A)
       - Right-unmatched in sub (elements y ∈ sub not in image of m_aug via inl) = la
       - Each chain is: a ∈ la, then x1 with m_aug(x1) = inl(a)... wait, m_aug goes
         FROM sub TO (sub ∪ la). So m_aug(x) = inl(y) means x's "successor" is y. *)
    
    (* Actually we need to re-examine the direction. *)
    (* m_aug : sub → sum A A *)
    (* m_aug(x) = inl(y): x's match is y (successor) *)
    (* m_aug(x) = inr(a): x's match is dummy a (x is a chain starter) *)
    
    (* Chain starters are elements x with m_aug(x) = inr(_) *)
    (* There are exactly w chain starters (since there are w dummies and matching is injective) *)
    
    (* f(x) = the unique a ∈ la such that x is in the chain of a *)
    (* For chain starters (m_aug(x) = inr a): f(x) = a *)
    (* For others: f(x) = f(m_aug_inl(x)) where m_aug(x) = inl(m_aug_inl(x)) *)
    
    (* Define f by: f(x) = epsilon y (y ∈ la ∧ ... x in chain of y ...) *)
    (* This requires the chain-following recursion which needs a termination argument *)
    
    (* Practical approach for the plan:
       Use strong induction on the rank of x in the chain (length of chain from x to root). *)
    admit.
  Qed.
```

**Note:** The `f` definition requires following the chain backwards. The cleanest Coq approach:

Define the chain function recursively with a fuel parameter bounded by `|sub|`:

```coq
    Fixpoint chain_root_aux (m : A -> sum A A) (x : A) (fuel : nat) : A :=
      match fuel, m x with
      | _, inr a => a
      | 0, inl _ => x  (* shouldn't happen with enough fuel *)
      | S fuel', inl y => chain_root_aux m y fuel'
      end.
    
    pose (f := fun x => chain_root_aux m_aug x nx).
```

Then prove:
- `f(x) ∈ la`: when the chain terminates (fuel ≥ chain length), `m_aug(terminus) = inr a` with `a ∈ la`
- `R(f(x), x)`: by transitivity along the chain (each edge has `R`)
- Fiber is a chain: elements in the same fiber form an order-chain (comparable by transitivity)

The termination argument: since edges are strict order and the poset is finite, chain length ≤ `|sub|`.

- [ ] **Step 2: Fill the admitted subgoals one by one**

Proceed in this order:
1. `HfinY`: `Finite (sum A A) Y_aug` — by `Finite_downward_closed` on `sub ∪ la`
2. `nx` existence and finiteness of sub: `sub` is finite because `la ⊆ sub ⊆ Above(la)` and... actually finiteness of `sub` is NOT given! The theorem requires a cardinality hypothesis. Check `DilworthB` in the file — it passes `Hcard_n : cardinal A sub n`. So `above_chain_assignment_exists` should also receive this. Either add a `cardinal A sub nx` hypothesis, or derive it from the context in `DilworthB`.

**Recommended fix:** Add `cardinal A sub nx` as a hypothesis to `above_chain_assignment_exists`:

```coq
  Lemma above_chain_assignment_exists : forall (sub la : Ensemble A) w nx,
    cardinal A sub nx ->
    IsLargestAntichain R sub la w ->
    Included A sub (Above R la) ->
    exists f : A -> A, ...
```

And update the caller `chain_cover_of_above` to pass the cardinality.

3. `Hhall`: Hall's condition — use `dilworth_hall_defect` after relating `HallCondition.set_neighbors nbrs_aug S` to `StrictSucc sub S ∪ image_inr(la)`.

4. Chain function and its properties — use `chain_root_aux` with fuel = `nx`.

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/WidthUpperBound.vo`
Expected: success

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/WidthUpperBound.v
git commit -m "feat: prove above_chain_assignment_exists using Hall's theorem"
```

---

### Task 9: Prove `below_chain_assignment_exists`

**Files:**
- Modify: `posets/dilworth/WidthUpperBound.v`

Symmetric to Task 8. Replace the `Admitted` in `below_chain_assignment_exists` (line ~556).

- [ ] **Step 1: Mirror the above_chain proof with Below/R-reversed**

The proof is structurally identical with these substitutions:
- `Above R la` → `Below R la`  
- `R x y` (in neighbor edges) → `R y x` (in neighbor edges)
- `R a x` (in `f` requirement) → `R x a` (in `f` requirement)
- `la` = minimal elements → `la` = MAXIMAL elements of `sub`
- Chain order: descending instead of ascending

Key change in augmented neighbors:
```coq
    (* nbrs_aug for Below: edges go from x to strict predecessors of x in sub *)
    pose (nbrs_aug : A -> Ensemble (sum A A) := fun x z =>
      match z with
        | inl y => In A sub y /\ R y x /\ x <> y   (* y is strict predecessor of x *)
        | inr a => In A la a                         (* la-element dummy *)
      end).
```

The `dilworth_hall_defect` lemma needs a symmetric version for `Below`:

```coq
  Definition StrictPred (sub S : Ensemble A) : Ensemble A :=
    fun y => In A sub y /\ exists x, In A S x /\ R y x /\ x <> y.

  Lemma dilworth_hall_defect_below : forall (sub la : Ensemble A) w,
    IsLargestAntichain R sub la w ->
    Included A sub (Below R la) ->
    forall S ns nn,
      Included A S sub ->
      cardinal A S ns ->
      cardinal A (StrictPred sub S) nn ->
      ns <= nn + w.
```

Add this lemma to WidthUpperBound.v and prove it symmetrically to `dilworth_hall_defect`.

- [ ] **Step 2: Complete the proof**

The chain_root_aux for Below follows predecessors (via `inl y` where `R y x`).

- [ ] **Step 3: Build**

Run: `dune build posets/dilworth/WidthUpperBound.vo`
Expected: success

- [ ] **Step 4: Commit**

```bash
git add posets/dilworth/WidthUpperBound.v
git commit -m "feat: prove below_chain_assignment_exists using Hall's theorem"
```

---

### Task 10: Final build verification and cleanup

**Files:**
- No new changes; verify everything compiles

- [ ] **Step 1: Full project build**

Run: `dune build posets/`
Expected: success with zero errors

- [ ] **Step 2: Verify no Admitted remain**

Run: `grep -r "Admitted" posets/dilworth/*.v`
Expected: no output (zero Admitteds)

- [ ] **Step 3: Verify no new Axiom declarations**

Run: `grep -r "^Axiom" posets/dilworth/*.v`
Expected: no output

- [ ] **Step 4: Final commit**

```bash
git add posets/dilworth/
git commit -m "feat: complete Dilworth theorem proof — all Admitteds replaced"
```

---

## Self-Review

**Spec coverage check:**
- `Hall.v` with `hall_marriage_theorem`: Tasks 1–5 ✓
- `dune` change: not needed (`coq.theory` auto-discovers) ✓
- `min_elements_eq_la`: Task 6 ✓
- `dilworth_hall_defect`: Task 7 ✓
- `matching_to_assignment`: folded into Tasks 8 and 9 (inline, not a separate lemma) ✓
- `above_chain_assignment_exists`: Task 8 ✓
- `below_chain_assignment_exists`: Task 9 ✓
- Acceptance criteria (no Admitted, `dune build @all` passes): Task 10 ✓

**Known challenges requiring careful Coq work:**
1. **Finiteness of `sub`**: `above_chain_assignment_exists` needs `cardinal A sub nx` — add as hypothesis
2. **`Finite (sum A A) Y_aug`**: Use `Finite_downward_closed` on a manually constructed finite superset
3. **Hall condition for augmented graph**: Requires relating `Hall.set_neighbors nbrs_aug S` to `StrictSucc sub S` (the StrictSucc part) plus `la` (the dummy part); use cardinality addition
4. **Chain function termination**: Use the fuel-based `chain_root_aux` with `fuel = nx`; prove correctness by showing chain depth ≤ `nx` (finite poset, strict edges)
5. **Non-tight case `lia` gap in Hall**: The `nn ≥ nsN - 1` bound requires case analysis on whether `y₀ ∈ N(S)` (see Task 4)
6. **Tight case cardinality `|X''| + |T| ≤ |X|`**: Use `cardinal_disjoint_union` (proved in Task 5)
