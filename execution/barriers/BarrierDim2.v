(* BarrierDim2.v
   All-cases binary barrier dim<=2 lever.

   Given a barrier (L, U) of an execution E, if both blocks have dimension
   <= 2, then E has dimension <= 2. The proof splits on whether either block
   has dimension 0 (forcing that block to be a singleton, hence a global
   extremum, reducible via ExtremumReduction) and otherwise applies the
   barrier_dimension max-formula. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Frontier Ordinal ExtremumReduction.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* A dimension-0 lower block forces it to be a singleton {m}, which is then a
   global minimum of E, and the upper block is its complement. *)
Lemma block_dim0_global_min :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E L) 0 ->
    exists m, IsGlobalMin E m /\ (forall x, Ensembles.In _ U x <-> x <> m).
Proof.
  intros E L U HB Hdim0.
  destruct HB as [Hcov [Hdisj [HinhL [HinhU Hbelow]]]].
  destruct HinhL as [m Hm].
  exists m.
  pose proof (dimension_cardinality Hdim0) as Hcard.
  pose proof (cardinalO_empty _ _ Hcard) as Hemp.
  pose proof (dimension_is_realizer Hdim0) as Hreal.
  (* Every pair in the L-sub-poset is related (vacuous realizer). *)
  assert (Huniv : forall a b : {z | Ensembles.In _ L z}, sub_order E L a b).
  { intros a b.
    apply (realizer_intersection Hreal a b).
    intros L' HL'.
    rewrite Hemp in HL'.
    destruct HL'. }
  (* Hence every element of L equals m. *)
  assert (HallL : forall x (Hx : Ensembles.In _ L x), x = m).
  { intros x Hx.
    pose (a := exist (fun z => Ensembles.In _ L z) x Hx).
    pose (b := exist (fun z => Ensembles.In _ L z) m Hm).
    assert (Hab : a = b).
    { apply (poset_antisym a b).
      - exact (Huniv a b).
      - exact (Huniv b a). }
    change x with (proj1_sig a).
    rewrite Hab. reflexivity. }
  split.
  - intro x.
    destruct (Hcov x) as [HxL | HxU].
    + rewrite (HallL x HxL). apply poset_refl.
    + exact (Hbelow m x Hm HxU).
  - intro x; split.
    + intro HxU. intro Heq. subst x.
      exact (Hdisj m (conj Hm HxU)).
    + intro Hne.
      destruct (Hcov x) as [HxL | HxU].
      * exfalso. apply Hne. exact (HallL x HxL).
      * exact HxU.
Qed.

(* Dual: a dimension-0 upper block is a singleton {m}, a global maximum, and
   the lower block is its complement. *)
Lemma block_dim0_global_max :
  forall E L U, IsBarrier E L U ->
    PosetDimension (sub_order E U) 0 ->
    exists m, IsGlobalMax E m /\ (forall x, Ensembles.In _ L x <-> x <> m).
Proof.
  intros E L U HB Hdim0.
  destruct HB as [Hcov [Hdisj [HinhL [HinhU Hbelow]]]].
  destruct HinhU as [m Hm].
  exists m.
  pose proof (dimension_cardinality Hdim0) as Hcard.
  pose proof (cardinalO_empty _ _ Hcard) as Hemp.
  pose proof (dimension_is_realizer Hdim0) as Hreal.
  assert (Huniv : forall a b : {z | Ensembles.In _ U z}, sub_order E U a b).
  { intros a b.
    apply (realizer_intersection Hreal a b).
    intros L' HL'.
    rewrite Hemp in HL'.
    destruct HL'. }
  assert (HallU : forall x (Hx : Ensembles.In _ U x), x = m).
  { intros x Hx.
    pose (a := exist (fun z => Ensembles.In _ U z) x Hx).
    pose (b := exist (fun z => Ensembles.In _ U z) m Hm).
    assert (Hab : a = b).
    { apply (poset_antisym a b).
      - exact (Huniv a b).
      - exact (Huniv b a). }
    change x with (proj1_sig a).
    rewrite Hab. reflexivity. }
  split.
  - intro x.
    destruct (Hcov x) as [HxL | HxU].
    + exact (Hbelow x m HxL Hm).
    + rewrite (HallU x HxU). apply poset_refl.
  - intro x; split.
    + intro HxL. intro Heq. subst x.
      exact (Hdisj m (conj HxL Hm)).
    + intro Hne.
      destruct (Hcov x) as [HxL | HxU].
      * exact HxL.
      * exfalso. apply Hne. exact (HallU x HxU).
Qed.

(* The lever: if both blocks of a barrier have dimension <= 2, so does E. *)
Lemma barrier_dim_le2 :
  forall E L U, IsBarrier E L U ->
    (exists d, inhabited (PosetDimension (sub_order E L) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension (sub_order E U) d) /\ d <= 2) ->
    (exists d, exec_has_dimension E d /\ d <= 2).
Proof.
  intros E L U HB [dL [ [HdL] HleL ]] [dU [ [HdU] HleU ]].
  destruct dL as [|dL'].
  - (* dL = 0: lower block is a singleton -> global min; U is its complement. *)
    destruct (block_dim0_global_min E L U HB HdL) as [m [Hmin HUeq]].
    assert (HUfun : U = (fun x => x <> m)).
    { apply functional_extensionality. intro x.
      apply propositional_extensionality. exact (HUeq x). }
    rewrite HUfun in HdU.
    apply (proj1 (remove_min_preserves_dim2 E m Hmin)).
    exists dU. split.
    + exact (inhabits HdU).
    + exact HleU.
  - destruct dU as [|dU'].
    + (* dU = 0: upper block singleton -> global max; L is its complement. *)
      destruct (block_dim0_global_max E L U HB HdU) as [m [Hmax HLeq]].
      assert (HLfun : L = (fun x => x <> m)).
      { apply functional_extensionality. intro x.
        apply propositional_extensionality. exact (HLeq x). }
      rewrite HLfun in HdL.
      apply (proj1 (remove_max_preserves_dim2 E m Hmax)).
      exists (S dL'). split.
      * exact (inhabits HdL).
      * exact HleL.
    + (* both > 0: apply the max-formula. *)
      destruct (exec_dimension_exists E) as [d [Hd]].
      pose proof (barrier_dimension E L U HB (S dL') (S dU') d HdL HdU Hd
                    (Nat.lt_0_succ dL') (Nat.lt_0_succ dU')) as Hmax.
      exists d. split.
      * exact (inhabits Hd).
      * rewrite Hmax. lia.
Qed.
