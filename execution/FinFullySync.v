(* generic n-way ordinal-partition dim<=2 theorem

   Part 1: the generic ordinal-partition predicate, subtype-finiteness, and
   the full-block order-isomorphism lever.  Later tasks append to this file. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim.
Import ListNotations.

Section FinFullySync.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* A finite ordinal partition of (A,R): a list of nonempty blocks that
     covers A, is pairwise disjoint, and is ordinally stacked (everything in
     an earlier block is below everything in a later block under R). *)
  Definition fin_ordinal_partition (blocks : list (Ensemble A)) : Prop :=
    (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\
    (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\
    (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
       Ensembles.In _ (nth i blocks (Empty_set _)) x ->
       ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\
    (forall i j, i < j -> j < length blocks ->
       forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                   Ensembles.In _ (nth j blocks (Empty_set _)) y -> R x y).

  (* Restrict a block [B] to the subtype carried by [L]. *)
  Definition restrict_block (L B : Ensemble A) : Ensemble {z | Ensembles.In _ L z} :=
    fun z => Ensembles.In _ B (proj1_sig z).
End FinFullySync.

(* The subtype carrier of any subset of a finite carrier is itself finite. *)
Lemma fin_sub_order_finite :
  forall {A : Type} (R : A -> A -> Prop) (Hfin : Finite A (Full_set A)) (L : Ensemble A),
    Finite {z : A | Ensembles.In _ L z} (Full_set {z | Ensembles.In _ L z}).
Proof.
  intros A R Hfin L.
  (* L is finite, being a subset of the finite Full_set A. *)
  assert (HLfin : Finite A L).
  { apply Finite_downward_closed with (Full_set A).
    - exact Hfin.
    - intros x _. apply Full_intro. }
  destruct (finite_cardinal _ _ HLfin) as [m Hm].
  apply (cardinal_finite _ _ m).
  exact (cardinal_subtype_full A L m Hm).
Qed.

(* If a block [B] is all of [A], then the subtype order on [B] is order-iso to
   [R], so any dimension witness for the block lifts to one for (A,R). *)
Lemma fin_block_iso_full :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (B : Ensemble A),
    (forall x, Ensembles.In _ B x) ->
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
              inhabited (PosetDimension R d).
Proof.
  intros A R HR B HBfull d [Hd].
  (* maps between A and {z | In B z} *)
  pose (f := fun x : A => exist (fun z => Ensembles.In _ B z) x (HBfull x)).
  pose (g := @proj1_sig A (fun z => Ensembles.In _ B z)).
  apply inhabits.
  (* The block-subtype carries [fin_sub_order_poset R B]. *)
  pose proof (fin_sub_order_poset R B) as Hsubpos.
  (* Transport the dimension witness from the block order to R using the
     inverse iso (f' := g, g' := f). *)
  apply (dimension_iso {z | Ensembles.In _ B z} A
           (fin_sub_order R B) R g f).
  - (* f' (g' z) = z, i.e. f (g z) = z *)
    intro z. destruct z as [x Hx]. unfold f, g. simpl.
    f_equal. apply proof_irrelevance.
  - (* g' (f' x) = x, i.e. g (f x) = x *)
    intro x. unfold f, g. reflexivity.
  - (* order iso: fin_sub_order R B z z' <-> R (g z) (g z') *)
    intros z z'. unfold fin_sub_order, g. reflexivity.
  - exact Hd.
Qed.
