From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple.


Section DilworthForward.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (* WidthLowerBound.v now uses the classes defined in Definitions.v *)


  (* ========================================================================= *)
  (* Basic Interaction Between Chains and Antichains                          *)
  (* ========================================================================= *)

  Lemma chain_antichain_intersect_once : forall (chain anti : Ensemble A),
    IsChain R chain ->
    IsAntichain R anti ->
    forall x y, In A chain x -> In A chain y ->
                In A anti x -> In A anti y ->
                x = y.
  Proof.
    intros chain anti Hc Ha x y Hcx Hcy Hax Hay.
    destruct Hc as [Hinhab_c Hchain].
    destruct Ha as [Hinhab_a Hanti].
    assert (Hcomp := Hchain x y Hcx Hcy).
    apply (Hanti x y Hax Hay Hcomp).
  Qed.

  (* ========================================================================= *)
  (* Pigeonhole Principle for Chains and Antichains                           *)
  (* ========================================================================= *)
  Lemma pigeonhole_chains_antichains : forall (cover : Ensemble (Ensemble A)) (anti : Ensemble A) n m,
    IsChainCover R cover ->
    IsAntichain R anti ->
    cardinal (Ensemble A) cover n ->
    cardinal A anti m ->
    m > n ->
    exists x y c, In A anti x /\ In A anti y /\ In (Ensemble A) cover c /\
                  In A c x /\ In A c y /\ x <> y.
  Proof.
    intros cover anti n m Hcover Ha Hcard_cover Hcard_anti Hgt.
    destruct Ha as [Hinhab_a Hanti].
    
    (* Every antichain element must be in some chain *)
    assert (Helem_in_chain : forall x, In A anti x -> exists c, In (Ensemble A) cover c /\ In A c x).
    {
      intros x Hx.
      destruct Hcover as [_ _ Hallcover].
      apply Hallcover. apply Full_intro.
    }
    
    (* Define relation RR: anti element x is in chain c *)
    pose (RR := fun (x : A) (c : Ensemble A) => In A c x).
    
    (* Proof by contradiction *)
    apply NNPP. intro Hnot_exists.
    
    (* This means each chain contains at most one antichain element *)
    assert (Hat_most_one : forall c x y,
              In (Ensemble A) cover c ->
              In A anti x -> In A anti y ->
              In A c x -> In A c y -> x = y).
    {
      intros c x y Hc Hx Hy Hcx Hcy.
      apply NNPP. intro Hneq.
      apply Hnot_exists.
      exists x, y, c. repeat split; auto.
    }
    
    (* Derive m <= n from the above, contradicting m > n *)
    assert (Hcontra : m <= n).
    {
      (* Apply the polymorphic cardinality injection principle with relation RR *)
      apply (cardinal_injection_principle_poly A (Ensemble A) anti cover RR m n).
      - (* Every antichain element maps to some chain *)
        exact Helem_in_chain.
      - (* No two distinct antichain elements map to the same chain *)
        intros x y c Hx Hy Hc Hxc Hyc.
        unfold RR in Hxc, Hyc.
        apply (Hat_most_one c x y Hc Hx Hy Hxc Hyc).
      - exact Hcard_anti.
      - exact Hcard_cover.
    }
    lia.
  Qed.

  (* ========================================================================= *)
  (* Forward Direction: DilworthA                                              *)
  (* ========================================================================= *)

  Theorem DilworthA : forall (cover : Ensemble (Ensemble A)) (anti : Ensemble A) n m,
    IsChainCover R cover ->
    IsAntichain R anti ->
    cardinal (Ensemble A) cover n ->
    cardinal A anti m ->
    m <= n.
  Proof.
    intros cover anti n m Hcover Hanti Hcard_cover Hcard_anti.
    
    (* Proof by contradiction: assume m > n *)
    destruct (le_gt_dec m n) as [Hle | Hgt]; [exact Hle |].
    
    (* By pigeonhole principle, some chain must contain two antichain elements *)
    destruct (pigeonhole_chains_antichains cover anti n m Hcover Hanti Hcard_cover Hcard_anti Hgt)
      as [x [y [c [Hax [Hay [Hc [Hcx [Hcy Hneq]]]]]]]].
    
    (* But this contradicts the fact that antichain elements are incomparable *)
    destruct Hcover as [Hchains _ _].
    destruct (Hchains c Hc) as [_ Hchain_c].
    destruct (Hchain_c x y Hcx Hcy) as [Hxy | Hyx].
    - (* Case: R x y *)
      destruct Hanti as [_ Hanti_prop].
      assert (Heq : x = y) by (apply Hanti_prop; auto; left; auto).
      contradiction.
    - (* Case: R y x *)
      destruct Hanti as [_ Hanti_prop].
      assert (Heq : x = y) by (apply Hanti_prop; auto; right; auto).
      contradiction.
  Qed.

End DilworthForward.
