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
