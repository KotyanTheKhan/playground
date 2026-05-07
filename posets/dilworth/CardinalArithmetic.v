From Stdlib Require Import Ensembles Finite_sets Classical Arith Lia.
From Stdlib Require Import FunctionalExtensionality PropExtensionality.
From Dilworth Require Import CardinalLemmas.


(** Cardinal removal: removing an element decreases cardinality by 1 *)
Lemma cardinal_remove : forall (U : Type) (A : Ensemble U) (x : U) (n : nat),
  In U A x ->
  cardinal U A (S n) ->
  cardinal U (fun y => In U A y /\ y <> x) n.
Proof.
  intros U A x n Hx Hcard.
  (* Induction on the cardinal witness *)
  remember (S n) as Sn eqn:HSn.
  generalize dependent n.
  induction Hcard as [| A' m Hcard' IH z Hz_notin]; intros n' HSn.
  - (* Base case: cardinality 0 *)
    discriminate HSn.
  - (* Step case: A = Add A' z with cardinal A' m *)
    injection HSn as Heq. subst m.
    unfold Add in Hx.
    inversion Hx as [y Hy | y Hy]; subst.
    + (* x is in A' *)
      assert (Hx_in_A' : In U A' x) by exact Hy.
      assert (Hxz_neq : x <> z).
      {
        intro Heq. subst z. contradiction.
      }
      destruct n' as [| n''].
      * (* n' = 0, so |A'| = 0, but x ∈ A' is a contradiction *)
        inversion Hcard'. subst. inversion Hx_in_A'.
      * (* n' = S n'', so |A'| = S n'' *)
        assert (Hremove_A' : cardinal U (fun y => In U A' y /\ y <> x) n'').
        {
          apply (IH Hx_in_A' n'' eq_refl).
        }
        (* Now show that (Add A' z) \ {x} = Add (A' \ {x}) z *)
        (* First prove the set equality *)
        assert (Hset_eq : forall y, 
          (In U (Add U A' z) y /\ y <> x) <-> 
          In U (Add U (fun y => In U A' y /\ y <> x) z) y).
        {
          intro y. split; intro Hy_in.
          - (* → *)
            destruct Hy_in as [Hy_A Hy_neq].
            unfold Add in Hy_A.
            inversion Hy_A as [w Hw | w Hw]; subst.
            + unfold Add. left. split; assumption.
            + unfold Add. right. inversion Hw. reflexivity.
          - (* ← *)
            unfold Add in Hy_in.
            inversion Hy_in as [y' Hy' | y' Hy']; subst.
            + destruct Hy' as [Hy'_A' Hy'_neq].
              split.
              * unfold Add. left. exact Hy'_A'.
              * exact Hy'_neq.
            + inversion Hy'. subst y. split.
              * unfold Add. right. apply In_singleton.
              * intro Heq_contr. symmetry in Heq_contr. contradiction.
        }
        (* Apply card_add to (A' \ {x}) and z *)
        assert (Hz_notin' : ~ In U (fun y => In U A' y /\ y <> x) z).
        {
          intro Hcontra. destruct Hcontra as [Hz_in Hz_neq]. contradiction.
        }
        pose proof (card_add U (fun y => In U A' y /\ y <> x) n'' Hremove_A' z Hz_notin') as Hcard_add.
        (* Now use Extensionality_Ensembles *)
        eapply Extensionality_Ensembles in Hset_eq.
        rewrite <- Hset_eq in Hcard_add.
        exact Hcard_add.
    + (* x = z, the added element *)
      inversion Hy. subst x.
      (* Then (Add A' z) \ {z} = A' *)
      assert (Hset_eq : forall y,
        (In U (Add U A' z) y /\ y <> z) <-> In U A' y).
      {
        intro y. split; intro Hy_in.
        - destruct Hy_in as [Hy_A Hy_neq].
          unfold Add in Hy_A.
          inversion Hy_A as [w Hw | w Hw]; subst.
          + exact Hw.
          + inversion Hw. subst. contradiction.
        - split.
          + unfold Add. left. exact Hy_in.
          + intro Heq. subst y. contradiction.
      }
      eapply Extensionality_Ensembles in Hset_eq.
      rewrite Hset_eq.
      exact Hcard'.
Qed.

Lemma cardinal_injection_principle_poly :
  forall (U V : Type) (A : Ensemble U) (B : Ensemble V) (n : nat),
    cardinal U A (S n) ->
    cardinal V B n ->
    forall f : U -> V,
      (forall x, In U A x -> In V B (f x)) ->
      (forall x y, In U A x -> In U A y -> f x = f y -> x = y) ->
      False.
Proof.
  intros U V.
  (* Strong induction on n, generalizing over A, B, f *)
  assert (Hind : forall n : nat,
    (forall m : nat, m < n ->
      forall A : Ensemble U, forall B : Ensemble V,
        cardinal U A (S m) ->
        cardinal V B m ->
        forall f : U -> V,
          (forall x, In U A x -> In V B (f x)) ->
          (forall x y, In U A x -> In U A y -> f x = f y -> x = y) ->
          False) ->
    forall A : Ensemble U, forall B : Ensemble V,
      cardinal U A (S n) ->
      cardinal V B n ->
      forall f : U -> V,
        (forall x, In U A x -> In V B (f x)) ->
        (forall x y, In U A x -> In U A y -> f x = f y -> x = y) ->
        False).
  {
    intros n IHn A B HcardA HcardB f Hf_range Hf_inj.
  
  (* Case analysis on n *)
  destruct n as [| n'].
  - (* Base case: n = 0 *)
    (* |A| = 1 but |B| = 0 *)
    inversion HcardA as [| A0 m Hcard_A0 a Ha_notin]; subst.
    inversion Hcard_A0; subst.
    (* A0 = ∅, so A = {a}, but B = ∅ *)
    inversion HcardB; subst.
    (* f(a) ∈ B but B = ∅ *)
    assert (Ha_in : In U (Add U (Empty_set U) a) a).
    {
      unfold Add. right. apply In_singleton.
    }
    pose proof (Hf_range a Ha_in) as Hfa_in.
    inversion Hfa_in.
      
  - (* Inductive case: n = S n' *)
    (* |A| = S (S n') and |B| = S n' *)
    (* Pick an element a ∈ A *)
    inversion HcardA as [| A' m Hcard_A' a Ha_notin]; subst.
    assert (Ha_in_A : In U (Add U A' a) a).
    {
      unfold Add. right. apply In_singleton.
    }
    
    (* Let b = f(a) ∈ B *)
    pose proof (Hf_range a Ha_in_A) as Hb_in_B.
    remember (f a) as b.
    
    (* Define A \ {a} and B \ {b} *)
    set (A_minus_a := fun x => In U (Add U A' a) x /\ x <> a).
    set (B_minus_b := fun y => In V B y /\ y <> b).
    
    (* |A \ {a}| = S n' *)
    assert (Hcard_A_minus_a : cardinal U A_minus_a (S n')).
    {
      apply (cardinal_remove U (Add U A' a) a (S n') Ha_in_A HcardA).
    }
    
    (* |B \ {b}| = n' *)
    assert (Hcard_B_minus_b : cardinal V B_minus_b n').
    {
      apply (cardinal_remove V B b n' Hb_in_B HcardB).
    }
    
    (* f restricts to f : A \ {a} → B \ {b} *)
    assert (Hf_range' : forall x, In U A_minus_a x -> In V B_minus_b (f x)).
    {
      intros x [Hx_in_A Hx_neq_a].
      split.
      - apply Hf_range. exact Hx_in_A.
      - intro Heq. subst b.
        (* If f(x) = f(a), then by injectivity x = a *)
        assert (Hx_eq_a : x = a).
        {
          apply Hf_inj; auto.
        }
        contradiction.
    }
    
    (* f is still injective on A \ {a} *)
    assert (Hf_inj' : forall x y, 
      In U A_minus_a x -> In U A_minus_a y -> f x = f y -> x = y).
    {
      intros x y [Hx_in _] [Hy_in _] Hfxy.
      apply Hf_inj; auto.
    }
    
    (* Apply IH to get contradiction *)
    refine (IHn n' (Nat.lt_succ_diag_r n') A_minus_a B_minus_b 
            Hcard_A_minus_a Hcard_B_minus_b f Hf_range' Hf_inj').
  }
  (* Now apply the inductive principle *)
  intros A B n HcardA HcardB f Hf_range Hf_inj.
  revert A B HcardA HcardB f Hf_range Hf_inj.
  induction n as [n IHn] using lt_wf_ind.
  intros A B HcardA HcardB f Hf_range Hf_inj.
  apply (Hind n IHn A B HcardA HcardB f Hf_range Hf_inj).
Qed.