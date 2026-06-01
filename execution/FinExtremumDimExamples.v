(* exact barrier dimension examples (test-only)

   A concrete example exercising the exact extremum lemma [fin_add_min_dim]
   on a 2-element chain (false < true on bool).  The "rest" (everything
   distinct from the global minimum [false]) is the singleton {true}, so the
   block dimension is 0 and the whole-poset dimension is exactly max 0 1 = 1.
   ZERO Admitted. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import FinPosetDimSurgery FinPosetDim FinExtremumDim.

(* A 2-element chain: false < true on bool. *)
Definition chain2_R (a b : bool) : Prop := a = b \/ (a = false /\ b = true).

#[export] Instance chain2_poset : IsPoset bool chain2_R.
Proof.
  constructor.
  - (* refl *)
    intro a. left. reflexivity.
  - (* antisym *)
    intros a b Hab Hba.
    destruct Hab as [Hab | [Ha Hb]].
    + exact Hab.
    + destruct Hba as [Hba | [Hb' Ha']].
      * symmetry. exact Hba.
      * (* a = false and a = true: contradiction *)
        subst. discriminate.
  - (* trans *)
    intros a b c Hab Hbc.
    destruct Hab as [Hab | [Ha Hb]].
    + subst b. exact Hbc.
    + destruct Hbc as [Hbc | [Hb' Hc]].
      * subst c. right. split; assumption.
      * (* b = true and b = false: contradiction *)
        subst. discriminate.
Qed.

Lemma true_neq_false : true <> false.
Proof. discriminate. Qed.

(* bool is finite: Full_set bool = Add (Add Empty false) true. *)
Lemma chain2_Hfin : Finite bool (Full_set bool).
Proof.
  apply (cardinal_finite bool (Full_set bool) 2).
  replace (Full_set bool)
    with (Add bool (Add bool (Empty_set bool) false) true).
  - apply card_add.
    + apply card_add.
      * apply card_empty.
      * intro Hbad. destruct Hbad.
    + (* true not in Add Empty false *)
      intro Hbad. apply Add_inv in Hbad. destruct Hbad as [Hbad | Hbad].
      * destruct Hbad.
      * exact (true_neq_false (eq_sym Hbad)).
  - apply Extensionality_Ensembles. split.
    + intros x _. constructor.
    + intros x _. destruct x.
      * right. constructor.
      * left. right. constructor.
Qed.

(* false is a global minimum of chain2_R. *)
Lemma chain2_min : fin_global_min chain2_R false.
Proof.
  intro x. destruct x.
  - right. split; reflexivity.
  - left. reflexivity.
Qed.

(* The rest { x : bool | x <> false } is the singleton {true}, hence
   any two of its elements are equal. *)
Lemma chain2_rest_all_eq :
  forall x y : {z : bool | z <> false}, x = y.
Proof.
  intros [x Hx] [y Hy].
  assert (Hxt : x = true) by (destruct x; [reflexivity | contradiction Hx; reflexivity]).
  assert (Hyt : y = true) by (destruct y; [reflexivity | contradiction Hy; reflexivity]).
  subst x. subst y.
  f_equal. apply proof_irrelevance.
Qed.

(* chain2_R is a total (linear) order. *)
Lemma chain2_total : forall a b : bool, chain2_R a b \/ chain2_R b a.
Proof.
  intros a b. destruct a, b.
  - left. left. reflexivity.
  - right. right. split; reflexivity.
  - left. right. split; reflexivity.
  - left. left. reflexivity.
Qed.

(* The singleton realizer { chain2_R } realizes chain2_R. *)
Lemma chain2_singleton_realizer :
  IsRealizer chain2_R (Singleton (bool -> bool -> Prop) chain2_R).
Proof.
  constructor.
  - intros L HL. apply Singleton_inv in HL. subst L.
    constructor.
    + constructor.
      * exact chain2_poset.
      * exact chain2_total.
    + intros x y Hxy. exact Hxy.
  - intros x y. split.
    + intros Hxy L HL. apply Singleton_inv in HL. subst L. exact Hxy.
    + intros Hall. apply (Hall chain2_R). constructor.
Qed.

Lemma chain2_singleton_card1 :
  cardinal (bool -> bool -> Prop) (Singleton (bool -> bool -> Prop) chain2_R) 1.
Proof.
  replace (Singleton (bool -> bool -> Prop) chain2_R)
    with (Add (bool -> bool -> Prop) (Empty_set _) chain2_R).
  - apply card_add.
    + apply card_empty.
    + intro Hbad. destruct Hbad.
  - apply Extensionality_Ensembles. split.
    + intros L HL. destruct HL as [L HL | L HL].
      * destruct HL.
      * exact HL.
    + intros L HL. right. exact HL.
Qed.

(* Build PosetDimension chain2_R 1 directly (Type-sorted record), avoiding
   eliminating an [inhabited (...)] from fin_dim_exists. *)
Lemma chain2_dim1 : PosetDimension chain2_R 1.
Proof.
  refine {| dimension_realizer := Singleton (bool -> bool -> Prop) chain2_R;
            dimension_is_realizer := chain2_singleton_realizer;
            dimension_cardinality := chain2_singleton_card1;
            dimension_is_minimum := _ |}.
  intros r n Hr Hcard.
  (* 1 <= n: an empty realizer would force chain2_R total in both directions,
     contradicting that true and false are incomparable upward. *)
  destruct n as [| n'].
  - exfalso.
    assert (Hempty : r = Empty_set _) by (apply cardinalO_empty; exact Hcard).
    (* realizer_intersection true false : chain2_R true false <-> vacuous true *)
    assert (Hbad : chain2_R true false).
    { apply (proj2 (realizer_intersection Hr true false)).
      intros L HL. rewrite Hempty in HL. destruct HL. }
    destruct Hbad as [Hbad | [_ Hbad]].
    + discriminate Hbad.
    + discriminate Hbad.
  - lia.
Qed.

(* PosetDimension is Type-sorted, so the existential body is wrapped in
   [inhabited (...)] (the standard idiom used throughout execution/*Examples*.v)
   to land in Prop.  This is the strongest well-typed rendering of
   "exists dW, PosetDimension chain2_R dW /\ dW = 1". *)
Example chain2_exact_dim :
  exists dW, inhabited (PosetDimension chain2_R dW) /\ dW = 1.
Proof.
  pose proof chain2_Hfin as Hfin.
  (* block dimension 0 (singleton rest): fin_singleton_dim0 does not depend on
     the finiteness hypothesis, so its only explicit argument after the poset
     instance is the "all elements equal" proof. *)
  pose proof (@fin_singleton_dim0
                {z : bool | z <> false}
                (fin_sub_order chain2_R (fun x => x <> false))
                (fin_sub_order_poset chain2_R (fun x => x <> false))
                (fun x y => chain2_rest_all_eq x y)) as HdRest.
  (* whole-poset dimension: built directly as a Type-sorted record *)
  pose proof chain2_dim1 as HdW.
  (* exact extremum lemma: dW = max 0 1 = 1 *)
  pose proof (@fin_add_min_dim bool chain2_R chain2_poset Hfin false
                chain2_min
                (ex_intro (fun x => x <> false) true true_neq_false)
                0 HdRest 1 HdW) as Heq.
  exists 1. split.
  - exact (inhabits HdW).
  - reflexivity.
Qed.
