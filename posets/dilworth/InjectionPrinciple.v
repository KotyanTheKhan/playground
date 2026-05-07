From Stdlib Require Import Ensembles Finite_sets Classical Arith Lia.
From Stdlib Require Import ClassicalChoice ClassicalDescription.
From Dilworth Require Import CardinalArithmetic.

Section DilworthAxioms.

  (* ========================================================================= *)
  (* LEVEL 1: Cardinal Arithmetic                                              *)
  (* ========================================================================= *)

  (** Helper lemma: extract a subset of a given cardinality *)
  Lemma cardinal_subset_exists : forall (U : Type) (A : Ensemble U) (n m : nat),
    cardinal U A n ->
    m <= n ->
    exists A' : Ensemble U, (forall x, In U A' x -> In U A x) /\ cardinal U A' m.
  Proof.
    intros U A n m HcardA Hle.
    revert A HcardA.
    induction Hle as [| n Hle IH].
    - (* m = n: take A' = A *)
      intros A HcardA.
      exists A. split.
      + intros x Hx. exact Hx.
      + exact HcardA.
    - (* m <= n, want m <= S n *)
      intros A HcardA.
      (* A has cardinality S n, so A = Add A0 a for some a and |A0| = n *)
      inversion HcardA as [| A0 n' Hcard_A0 a Ha_notin]; subst.
      (* Apply IH to A0 *)
      destruct (IH A0 Hcard_A0) as [A' [Hsub HcardA']].
      exists A'. split.
      + intros x Hx. unfold Add. left. apply Hsub. exact Hx.
      + exact HcardA'.
  Qed.

  Lemma cardinal_injection_principle_poly : 
    forall (B_type C_type : Type) (B : Ensemble B_type) (C : Ensemble C_type) 
           (Rel : B_type -> C_type -> Prop) n m,
    (forall x, In B_type B x -> exists y, In C_type C y /\ Rel x y) ->
    (forall x y z, In B_type B x -> In B_type B y -> In C_type C z -> Rel x z -> Rel y z -> x = y) ->
    cardinal B_type B n ->
    cardinal C_type C m ->
    n <= m.
  Proof.
    intros B_type C_type B C Rel n m Hrel_total Hrel_inj HcardB HcardC.
    
    (* Use excluded middle to decide n ≤ m *)
    destruct (le_gt_dec n m) as [Hle | Hgt].
    - (* n ≤ m: done *)
      exact Hle.
    - (* n > m: derive contradiction *)
      exfalso.
      
      (* We'll prove by strong induction on m that if n > m, we get a contradiction *)
      (* The key idea: if |B| > |C| with an injective relation, impossible *)
      
      (* Use Axiom of Choice to extract a function from Rel *)
      (* First, check if C_type is inhabited *)
      assert (HC_type_inhabited : exists y0 : C_type, True).
      {
        (* We need to show C_type is inhabited *)
        (* If m = 0, then C is empty, but B is non-empty (since n > m ≥ 1) *)
        (* This leads to immediate contradiction *)
        destruct m as [| m'].
        - (* m = 0: C is empty but B is non-empty *)
          assert (n > 0) by lia.
          (* B has cardinality n > 0, so B is non-empty *)
          destruct n as [| n'].
          + lia.
          + inversion HcardB as [| B' k Hcard' b Hb_notin]; subst.
            assert (Hb_in : In B_type (Add B_type B' b) b).
            {
              unfold Add. right. apply In_singleton.
            }
            destruct (Hrel_total b Hb_in) as [y [Hy_in _]].
            (* But C has cardinality 0, so y ∉ C *)
            inversion HcardC. subst. inversion Hy_in.
        - (* m = S m', so C is non-empty *)
          inversion HcardC as [| C' k Hcard' c Hc_notin]; subst.
          exists c. exact I.
      }
      
      (* Now apply choice *)
      destruct HC_type_inhabited as [y0 _].
      pose (Rel' := fun (x : B_type) (y : C_type) => 
        (In B_type B x -> In C_type C y /\ Rel x y) /\
        (~ In B_type B x -> y = y0)).
      
      assert (Hchoice : exists f : B_type -> C_type, forall x : B_type, Rel' x (f x)).
      {
        apply choice.
        intro x.
        destruct (classic (In B_type B x)) as [Hx_in | Hx_notin].
        - destruct (Hrel_total x Hx_in) as [y [Hy_in Hrel_xy]].
          exists y.
          unfold Rel'. split.
          + intro. split; assumption.
          + intro. contradiction.
        - exists y0.
          unfold Rel'. split.
          + intro. contradiction.
          + intro. reflexivity.
      }
      
      destruct Hchoice as [f Hf].
      
      (* Show f satisfies conditions for pigeonhole principle *)
      assert (Hf_range : forall x, In B_type B x -> In C_type C (f x)).
      {
        intros x Hx_in.
        specialize (Hf x).
        unfold Rel' in Hf.
        destruct Hf as [Hf_in _].
        destruct (Hf_in Hx_in) as [Hfx_in _].
        exact Hfx_in.
      }
      
      assert (Hf_inj : forall x y, In B_type B x -> In B_type B y -> f x = f y -> x = y).
      {
        intros x y Hx_in Hy_in Hfxy.
        assert (Hfx := Hf x). assert (Hfy := Hf y).
        unfold Rel' in Hfx, Hfy.
        destruct Hfx as [Hfx_in _].
        destruct Hfy as [Hfy_in _].
        destruct (Hfx_in Hx_in) as [Hfx_C Hrel_x].
        destruct (Hfy_in Hy_in) as [Hfy_C Hrel_y].
        rewrite Hfxy in Hrel_x.
        apply (Hrel_inj x y (f y) Hx_in Hy_in Hfy_C Hrel_x Hrel_y).
      }
      
      (* Now we have n > m *)
      (* Case analysis: either n = S m or n > S m *)
      assert (Hn_cases : n = S m \/ n > S m) by lia.
      destruct Hn_cases as [Hn_eq | Hn_gt].
      + (* n = S m: direct application of pigeonhole *)
        rewrite Hn_eq in HcardB.
        eapply (CardinalArithmetic.cardinal_injection_principle_poly 
                B_type C_type B C m HcardB HcardC f Hf_range Hf_inj).
      + (* n > S m: extract a subset of size S m *)
        (* We have n > S m, so S m < n, thus S m <= n *)
        assert (HSm_le_n : S m <= n) by lia.
        
        (* Extract a subset B' ⊆ B with |B'| = S m *)
        destruct (cardinal_subset_exists B_type B n (S m) HcardB HSm_le_n) 
          as [B' [Hsub HcardB']].
        
        (* Show that f restricted to B' satisfies the pigeonhole conditions *)
        assert (Hf_range' : forall x, In B_type B' x -> In C_type C (f x)).
        {
          intros x Hx_in.
          apply Hf_range. apply Hsub. exact Hx_in.
        }
        
        assert (Hf_inj' : forall x y, In B_type B' x -> In B_type B' y -> f x = f y -> x = y).
        {
          intros x y Hx_in Hy_in Hfxy.
          apply Hf_inj.
          - apply Hsub. exact Hx_in.
          - apply Hsub. exact Hy_in.
          - exact Hfxy.
        }
        
        (* Apply the pigeonhole principle to B' and C *)
        eapply (CardinalArithmetic.cardinal_injection_principle_poly 
                B_type C_type B' C m HcardB' HcardC f Hf_range' Hf_inj').
  Qed.

End DilworthAxioms.
