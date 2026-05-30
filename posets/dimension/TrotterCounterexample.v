(** A CONCRETE COUNTEREXAMPLE justifying the removal of the former Trotter
    coverage core [trotter_path_family_impossible] (RemovablePairs.v): that
    boundary-CP coverage claim was FALSE AS STATED, and this file proves the
    self-contained model fact that defeats it.

    Model (5 elements): x' < d1, x' < d2; q, y' isolated.
      - (x',y') is an extremal critical pair.
      - S' = {d1,d2,q} is a 3-antichain; r' = {La, Lb}, La: d1<q<d2, Lb: d2<q<d1
        realizes it.  In BOTH extensions q is above one of d1,d2 — neither puts
        q below both.
      - For the boundary CP (x',q): under EVERY L' in r' there is an augmenting
        path x' -> q in the B=nil augmented step relation (x' ->R-> d_i ->L'-> q).

    The deleted coverage core claimed that for an arbitrary residual realizer
    r', every boundary CP is *covered* (rejected from the augmented closure for
    some L' in r').  Here all of its premises hold (extremal CP + realizer +
    per-L' augmenting path), so the pair (x',q) is uncoverable by ANY L' in r' —
    the forced cycle x' -> S' -> q is unavoidable in every extension.  Hence
    coverage holds only for a coordinated (removable-pair, realizer) choice, not
    for an arbitrary extremal CP + arbitrary realizer.  See the soundness note
    on [non_antichain_removable_pair_exists] in RemovablePairs.v.

    Uses [proof_irrelevance] (for subtype equalities), consistent with the
    development's existing classical axioms. *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Relations.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs CriticalPairDigraph.
Import ListNotations.

Inductive Elt := eX | eY | eD1 | eD2 | eQ.

Definition Rel (a b : Elt) : Prop :=
  a = b \/ (a = eX /\ (b = eD1 \/ b = eD2)).

#[local] Instance Rel_poset : IsPoset Elt Rel.
Proof.
  constructor.
  - intro x. left. reflexivity.
  - intros x y Hxy Hyx.
    destruct Hxy as [E | [Hx Hb]]; [exact E |].
    destruct Hyx as [E2 | [Hy Hb2]]; [symmetry; exact E2 |].
    subst x. subst y. destruct Hb2 as [E|E]; discriminate.
  - intros x y z Hxy Hyz.
    destruct Hxy as [E | [Hx Hb]]; [subst x; exact Hyz |].
    destruct Hyz as [E2 | [Hy Hb2]].
    + subst z. right. split; assumption.
    + subst y. destruct Hb as [E|E]; discriminate.
Qed.

(* ---- finiteness of the carrier ---- *)
Lemma Elt_full_finite : Finite Elt (Full_set Elt).
Proof.
  apply Finite_downward_closed with
    (A := Add Elt (Add Elt (Add Elt (Add Elt (Singleton Elt eX) eY) eD1) eD2) eQ).
  - repeat apply Add_preserves_Finite. apply Singleton_is_finite.
  - intros x _. destruct x.
    + apply Union_introl; apply Union_introl; apply Union_introl;
        apply Union_introl; apply In_singleton.
    + apply Union_introl; apply Union_introl; apply Union_introl;
        apply Union_intror; apply In_singleton.
    + apply Union_introl; apply Union_introl;
        apply Union_intror; apply In_singleton.
    + apply Union_introl; apply Union_intror; apply In_singleton.
    + apply Union_intror; apply In_singleton.
Qed.

(* ---- residual S' = carrier \ {eX, eY} ---- *)
Definition Sset : Ensemble Elt :=
  Setminus Elt (Setminus Elt (Full_set Elt) (Singleton Elt eX)) (Singleton Elt eY).

Lemma in_Sset : forall a, In Elt Sset a <-> (a <> eX /\ a <> eY).
Proof.
  intro a. unfold Sset, Setminus, In. split.
  - intros [[_ HnX] HnY]. split.
    + intro E. apply HnX. rewrite E. apply In_singleton.
    + intro E. apply HnY. rewrite E. apply In_singleton.
  - intros [HX HY]. split; [split |].
    + apply Full_intro.
    + intro Hc. inversion Hc. congruence.
    + intro Hc. inversion Hc. congruence.
Qed.

Definition Tsub := {a : Elt | In Elt Sset a}.
Definition Rsub (a b : Tsub) : Prop := Rel (proj1_sig a) (proj1_sig b).

(* ---- two rank functions, giving the two linear extensions of S' ---- *)
Definition ranka (a : Elt) : nat :=
  match a with eD1 => 0 | eQ => 1 | eD2 => 2 | _ => 5 end.
Definition rankb (a : Elt) : nat :=
  match a with eD2 => 0 | eQ => 1 | eD1 => 2 | _ => 5 end.

Definition La (x y : Tsub) : Prop := ranka (proj1_sig x) <= ranka (proj1_sig y).
Definition Lb (x y : Tsub) : Prop := rankb (proj1_sig x) <= rankb (proj1_sig y).

(* generic: a rank injective on S' yields a linear extension of Rsub *)
Lemma rankrel_linext :
  forall (rk : Elt -> nat),
    (forall a b, In Elt Sset a -> In Elt Sset b -> rk a = rk b -> a = b) ->
    IsLinearExtension Rsub (fun x y : Tsub => rk (proj1_sig x) <= rk (proj1_sig y)).
Proof.
  intros rk Hinj. constructor.
  - constructor.
    + constructor.
      * intro x. apply Nat.le_refl.
      * intros x y Hxy Hyx.
        assert (Heq : rk (proj1_sig x) = rk (proj1_sig y)) by lia.
        assert (Hpe : proj1_sig x = proj1_sig y)
          by (apply Hinj; [ apply proj2_sig | apply proj2_sig | exact Heq ]).
        destruct x as [px hpx]; destruct y as [py hpy]; simpl in Hpe.
        subst py. f_equal. apply proof_irrelevance.
      * intros x y z. apply Nat.le_trans.
    + intros x y. lia.
  - intros x y HR. unfold Rsub in HR.
    destruct x as [px hpx]; destruct y as [py hpy]; simpl in *.
    assert (Hpe : px = py).
    { destruct HR as [E | [HxX _]]; [ exact E |].
      exfalso. exact (proj1 (proj1 (in_Sset px) hpx) HxX). }
    subst py. apply Nat.le_refl.
Qed.

Lemma ranka_inj : forall a b, In Elt Sset a -> In Elt Sset b -> ranka a = ranka b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (proj1 (in_Sset a)) in Ha. apply (proj1 (in_Sset b)) in Hb.
  destruct Ha as [HaX HaY]; destruct Hb as [HbX HbY].
  destruct a, b; try reflexivity; try (exfalso; (apply HaX + apply HaY + apply HbX + apply HbY); reflexivity);
    simpl in Heq; discriminate.
Qed.

Lemma rankb_inj : forall a b, In Elt Sset a -> In Elt Sset b -> rankb a = rankb b -> a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (proj1 (in_Sset a)) in Ha. apply (proj1 (in_Sset b)) in Hb.
  destruct Ha as [HaX HaY]; destruct Hb as [HbX HbY].
  destruct a, b; try reflexivity; try (exfalso; (apply HaX + apply HaY + apply HbX + apply HbY); reflexivity);
    simpl in Heq; discriminate.
Qed.

Lemma La_linext : IsLinearExtension Rsub La.
Proof. apply (rankrel_linext ranka ranka_inj). Qed.
Lemma Lb_linext : IsLinearExtension Rsub Lb.
Proof. apply (rankrel_linext rankb rankb_inj). Qed.

(* ---- the realizer r' = {La, Lb} ---- *)
Definition rprime : Ensemble (Tsub -> Tsub -> Prop) := fun L => L = La \/ L = Lb.

Lemma in_Sset_cases : forall a, In Elt Sset a -> a = eD1 \/ a = eD2 \/ a = eQ.
Proof.
  intros a Ha. apply (proj1 (in_Sset a)) in Ha. destruct Ha as [HX HY].
  destruct a; [ exfalso; apply HX; reflexivity | exfalso; apply HY; reflexivity
              | left; reflexivity | right; left; reflexivity | right; right; reflexivity ].
Qed.

#[local] Instance rprime_realizer : IsRealizer Rsub rprime.
Proof.
  constructor.
  - intros L HL. destruct HL as [-> | ->]; [ apply La_linext | apply Lb_linext ].
  - intros x y. split.
    + intros HR L HL. unfold Rsub in HR.
      destruct x as [px hpx]; destruct y as [py hpy]; simpl in HR.
      assert (Hpe : px = py).
      { destruct HR as [E | [HxX _]]; [ exact E |].
        exfalso. exact (proj1 (proj1 (in_Sset px) hpx) HxX). }
      subst py. destruct HL as [-> | ->]; unfold La, Lb; simpl; apply Nat.le_refl.
    + intros Hall. unfold Rsub.
      destruct x as [px hpx]; destruct y as [py hpy]; simpl.
      pose proof (Hall La (or_introl eq_refl)) as HLa.
      pose proof (Hall Lb (or_intror eq_refl)) as HLb.
      unfold La, Lb in HLa, HLb; simpl in HLa, HLb.
      left.
      pose proof (in_Sset_cases px hpx) as Hpx.
      pose proof (in_Sset_cases py hpy) as Hpy.
      destruct Hpx as [ -> | [ -> | -> ] ]; destruct Hpy as [ -> | [ -> | -> ] ];
        simpl in HLa, HLb; try reflexivity; exfalso; lia.
Qed.

(* ---- (eX, eY) is an extremal critical pair ---- *)
Lemma cp_XY : IsCriticalPair Rel eX eY.
Proof.
  constructor.
  - intros [H|H]; destruct H as [H|[H H']]; try discriminate H;
      destruct H' as [H'|H']; discriminate H'.
  - intros a [HR Hne]. destruct HR as [E | [HX _]]; [ congruence | subst a; contradiction ].
  - intros b [HR Hne]. destruct HR as [E | [HX _]]; [ congruence | discriminate HX ].
Qed.

Lemma extremal_XY : IsExtremalCP Rel eX eY.
Proof.
  split; [ exact cp_XY |].
  intros p q Hcp HpX HyQ.
  (* R p eX -> p = eX *)
  assert (Hp : p = eX).
  { destruct HpX as [E | [HX _]]; [ exact E | exact HX ]. }
  (* R eY q -> q = eY *)
  assert (Hq : q = eY).
  { destruct HyQ as [E | [HY _]]; [ symmetry; exact E | discriminate HY ]. }
  split; assumption.
Qed.

(* ---- (eX, eQ) is a critical pair ---- *)
Lemma cp_XQ : IsCriticalPair Rel eX eQ.
Proof.
  constructor.
  - intros [H|H]; destruct H as [H|[H H']]; try discriminate H;
      destruct H' as [H'|H']; discriminate H'.
  - intros a [HR Hne]. destruct HR as [E | [HX _]]; [ congruence | subst a; contradiction ].
  - intros b [HR Hne]. destruct HR as [E | [HX _]]; [ congruence | discriminate HX ].
Qed.

(* ---- membership facts ---- *)
Lemma inS_D1 : In Elt Sset eD1. Proof. apply in_Sset. split; discriminate. Qed.
Lemma inS_D2 : In Elt Sset eD2. Proof. apply in_Sset. split; discriminate. Qed.
Lemma inS_Q  : In Elt Sset eQ.  Proof. apply in_Sset. split; discriminate. Qed.

(* ---- the B = nil augmented step relation for this model ----
   (a local copy of [aug_step Sset eX eY L' nil] from RemovablePairs.v,
   inlined so this disproof stands alone). *)
Definition augN (L' : Tsub -> Tsub -> Prop) (a b : Elt) : Prop :=
  Rel a b
  \/ (exists (ha : In Elt Sset a) (hb : In Elt Sset b),
        L' (exist _ a ha) (exist _ b hb))
  \/ (a = eX /\ b = eY).

(* ---- THE COUNTEREXAMPLE: all premises of the deleted coverage core
   [trotter_path_family_impossible] hold on this model, yet the boundary CP
   (eX,eQ) admits an augmenting path under EVERY L' in r' — so it is covered
   by no L', contradicting the core's conclusion.  The core was therefore
   false; this is why it was removed from RemovablePairs.v. ---- *)
Theorem coverage_core_premises_hold_yet_pair_uncovered :
  (* (eX,eY) is an extremal critical pair *)
  IsExtremalCP Rel eX eY
  (* rprime = {La, Lb} realizes the residual S' = {eD1,eD2,eQ} *)
  /\ IsRealizer Rsub rprime
  (* yet for EVERY extension L' in rprime, the boundary CP (eX,eQ) has an
     augmenting path eX -> eQ — hence it can be rejected (covered) by NO L' *)
  /\ (forall L', In _ rprime L' -> clos_refl_trans Elt (augN L') eX eQ).
Proof.
  split; [ exact extremal_XY |].
  split; [ exact rprime_realizer |].
  intros L' HL'. destruct HL' as [-> | ->].
  - (* La : eX -> eD1 -> eQ *)
    eapply rt_trans.
    + apply rt_step. left. right. split; [ reflexivity | left; reflexivity ].
    + apply rt_step. right. left.
      exists inS_D1, inS_Q. unfold La; simpl. lia.
  - (* Lb : eX -> eD2 -> eQ *)
    eapply rt_trans.
    + apply rt_step. left. right. split; [ reflexivity | right; reflexivity ].
    + apply rt_step. right. left.
      exists inS_D2, inS_Q. unfold Lb; simpl. lia.
Qed.
