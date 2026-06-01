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

(* A prefix block (B ⊆ L), restricted to the L-subtype, has the same dimension. *)
Lemma restricted_block_dim2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (L B : Ensemble A),
    (forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
      inhabited (PosetDimension
                  (fin_sub_order (fin_sub_order R L) (restrict_block L B)) d).
Proof.
  intros A R HR L B Hsub d [Hd].
  apply inhabits.
  (* Make the two subtype-poset instances available to resolution. *)
  pose proof (fin_sub_order_poset R B) as HposB.
  pose proof (fin_sub_order_poset R L) as HposL.
  pose proof (fin_sub_order_poset (fin_sub_order R L) (restrict_block L B)) as HposTgt.
  (* source carrier: {z | In B z}; target carrier:
     {w : {z | In L z} | In (restrict_block L B) w}. *)
  pose (f := fun s : {z | Ensembles.In _ B z} =>
               let (x, HxB) := s in
               exist (fun w : {z | Ensembles.In _ L z} =>
                        Ensembles.In _ (restrict_block L B) w)
                     (exist (fun z => Ensembles.In _ L z) x (Hsub x HxB))
                     HxB).
  pose (g := fun w : {w : {z | Ensembles.In _ L z}
                      | Ensembles.In _ (restrict_block L B) w} =>
               exist (fun z => Ensembles.In _ B z)
                     (proj1_sig (proj1_sig w)) (proj2_sig w)).
  apply (dimension_iso
           {z | Ensembles.In _ B z}
           {w : {z | Ensembles.In _ L z}
            | Ensembles.In _ (restrict_block L B) w}
           (fin_sub_order R B)
           (fin_sub_order (fin_sub_order R L) (restrict_block L B))
           f g).
  - (* g (f s) = s *)
    intro s. destruct s as [x HxB]. unfold f, g. cbn.
    reflexivity.
  - (* f (g w) = w *)
    intro w. destruct w as [[x HxL] Hw]. unfold f, g. cbn.
    (* goal: exist _ (exist _ x (Hsub x Hw)) Hw = exist _ (exist _ x HxL) Hw *)
    (* The inner [In L x] proofs differ; replace [Hsub x Hw] by [HxL]. *)
    generalize (Hsub x Hw); intro HxL'.
    replace HxL' with HxL by apply proof_irrelevance.
    reflexivity.
  - (* order iso *)
    intros s s'. destruct s as [x HxB]. destruct s' as [x' Hx'B].
    unfold f, fin_sub_order. simpl. reflexivity.
  - exact Hd.
Qed.

(* The prefix of an ordinal partition, restricted to its union L, is an ordinal
   partition of the L-subtype. *)
Lemma nth_map_restrict :
  forall {A : Type} (R : A -> A -> Prop) (L : Ensemble A)
         (pre : list (Ensemble A)) (i : nat),
    i < length pre ->
    nth i (map (restrict_block L) pre) (Empty_set _)
    = restrict_block L (nth i pre (Empty_set _)).
Proof.
  intros A R L pre i Hi.
  rewrite (nth_indep (map (restrict_block L) pre) (Empty_set _)
             (restrict_block L (Empty_set _))).
  - rewrite map_nth. reflexivity.
  - rewrite length_map. exact Hi.
Qed.

Lemma restrict_partition :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (L : Ensemble A) (pre : list (Ensemble A)),
    (forall B, List.In B pre -> forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    fin_ordinal_partition R pre ->
    (forall x, Ensembles.In _ L x <->
       exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    fin_ordinal_partition (fin_sub_order R L) (map (restrict_block L) pre).
Proof.
  intros A R HR L pre Hsub Hpart HLeq.
  destruct Hpart as [Hne [Hcov [Hdis Hbel]]].
  unfold fin_ordinal_partition.
  repeat split.
  - (* nonempty *)
    intros blk Hblk.
    apply in_map_iff in Hblk. destruct Hblk as [B [HBeq HBin]]. subst blk.
    destruct (Hne B HBin) as [x HxB].
    pose (HxL := Hsub B HBin x HxB).
    exists (exist (fun z => Ensembles.In _ L z) x HxL).
    unfold restrict_block. simpl. exact HxB.
  - (* cover *)
    intro z. destruct z as [x HxL].
    destruct (proj1 (HLeq x) HxL) as [i [Hi Hxi]].
    exists i. split.
    + rewrite length_map. exact Hi.
    + rewrite (nth_map_restrict R L pre i Hi).
      unfold restrict_block. simpl. exact Hxi.
  - (* disjoint *)
    intros i j z Hi Hj Hij Hzi Hzj.
    rewrite length_map in Hi, Hj.
    rewrite (nth_map_restrict R L pre i Hi) in Hzi.
    rewrite (nth_map_restrict R L pre j Hj) in Hzj.
    unfold restrict_block in Hzi, Hzj. simpl in Hzi, Hzj.
    apply (Hdis i j (proj1_sig z) Hi Hj Hij Hzi Hzj).
  - (* below *)
    intros i j Hij Hj x y Hxi Hyj.
    rewrite length_map in Hj.
    assert (Hi : i < length pre) by lia.
    rewrite (nth_map_restrict R L pre i Hi) in Hxi.
    rewrite (nth_map_restrict R L pre j Hj) in Hyj.
    unfold restrict_block in Hxi, Hyj. simpl in Hxi, Hyj.
    unfold fin_sub_order.
    apply (Hbel i j Hij Hj (proj1_sig x) (proj1_sig y) Hxi Hyj).
Qed.
