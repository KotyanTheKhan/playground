From Stdlib Require Import Ensembles Finite_sets Classical Lia Arith.
From Stdlib Require Import Finite_sets_facts ClassicalEpsilon ClassicalChoice.
From Posets Require Import PosetClasses.
From Dilworth Require Import CardinalArithmetic Definitions InjectionPrinciple CardinalLemmas.

Section Helpers.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** In a chain C ⊆ Above(la), the la-element a is the minimum:
      every other element x satisfies R a x. *)
  Lemma chain_la_is_min : forall (la C : Ensemble A) a x,
    IsAntichain R la ->
    IsChain R C ->
    Included A C (Above R la) ->
    In A C a ->
    In A la a ->
    In A C x ->
    R a x.
  Proof.
    intros la C a x Hanti Hchain Hincl Ha_C Ha_la Hx_C.
    destruct Hanti as [_ Hincompat].
    destruct Hchain as [_ Hcomp].
    assert (Hx_above : In A (Above R la) x) by exact (Hincl x Hx_C).
    destruct Hx_above as [b [Hb_la Hbx]].
    destruct (Hcomp a x Ha_C Hx_C) as [Rax | Rxa].
    - exact Rax.
    - assert (Hba : R b a).
      { exact (poset_trans b x a Hbx Rxa). }
      assert (Hab : a = b).
      { apply Hincompat; [exact Ha_la | exact Hb_la | right; exact Hba]. }
      subst b. exact Hbx.
  Qed.

  (** In a chain C ⊆ Below(la), the la-element a is the maximum:
      every other element y satisfies R y a. *)
  Lemma chain_la_is_max : forall (la C : Ensemble A) a y,
    IsAntichain R la ->
    IsChain R C ->
    Included A C (Below R la) ->
    In A C a ->
    In A la a ->
    In A C y ->
    R y a.
  Proof.
    intros la C a y Hanti Hchain Hincl Ha_C Ha_la Hy_C.
    destruct Hanti as [_ Hincompat].
    destruct Hchain as [_ Hcomp].
    assert (Hy_below : In A (Below R la) y) by exact (Hincl y Hy_C).
    destruct Hy_below as [b [Hb_la Hyb]].
    destruct (Hcomp a y Ha_C Hy_C) as [Ray | Rya].
    - assert (Hab : R a b).
      { exact (poset_trans a y b Ray Hyb). }
      assert (Heq : a = b).
      { apply Hincompat; [exact Ha_la | exact Hb_la | left; exact Hab]. }
      subst b. exact Hyb.
    - exact Rya.
  Qed.

  (** Each chain in a w-chain-cover of a set with largest antichain la of size w
      contains at least one la-element. *)
  Lemma each_chain_has_la_element :
    forall (sub la : Ensemble A) w (cover : Ensemble (Ensemble A)),
    IsAntichain R la ->
    Included A la sub ->
    cardinal A la w ->
    IsChainCover R sub cover ->
    cardinal (Ensemble A) cover w ->
    forall C, In (Ensemble A) cover C ->
    exists a, In A la a /\ In A C a.
  Proof.
    intros sub la w cover Hanti Hincl_la Hcard_la Hcov Hcard_cov C HC.
    destruct Hanti as [Hinhab Hincompat].
    (* By contradiction: if no la-element is in C, then la can be injected into
       cover \ {C}, giving w ≤ w-1, contradiction. *)
    destruct (classic (exists a, In A la a /\ In A C a)) as [Hex | Hnex].
    - exact Hex.
    - exfalso.
      (* No la-element is in C *)
      assert (Hno_la : forall a, In A la a -> ~ In A C a).
      { intros a Ha Habs. apply Hnex. exact (ex_intro _ a (conj Ha Habs)). }
      (* The injection la → cover sends each a to the chain containing a.
         Since a ∉ C, it maps into cover \ {C}. *)
      destruct w as [| w'].
      { (* w = 0: la empty, but la is inhabited *)
        inversion Hcard_la. subst. destruct Hinhab as [a Ha]. inversion Ha. }
      (* |cover| = S w', remove C to get |cover\{C}| = w' *)
      assert (Hcard_minus : cardinal (Ensemble A) (fun D => In (Ensemble A) cover D /\ D <> C) w').
      { apply cardinal_remove; assumption. }
      (* Injection la → cover\{C} *)
      assert (Htot : forall a, In A la a ->
                exists D, In (Ensemble A) (fun D => In (Ensemble A) cover D /\ D <> C) D /\
                          In A D a).
      { intros a Ha.
        pose proof (Hincl_la a Ha) as Ha_sub.
        destruct (@chain_cover_covers A R sub cover Hcov a Ha_sub) as [D [HD Ha_D]].
        exists D. split.
        - split; [exact HD |].
          intro Heq. subst D. exact (Hno_la a Ha Ha_D).
        - exact Ha_D. }
      assert (Hinj : forall a b D, In A la a -> In A la b ->
                In (Ensemble A) (fun D => In (Ensemble A) cover D /\ D <> C) D ->
                In A D a -> In A D b -> a = b).
      { intros a b D Ha Hb [HD _] HaD HbD.
        destruct (@chain_cover_chains A R sub cover Hcov D HD) as [_ Hcomp].
        exact (Hincompat a b Ha Hb (Hcomp a b HaD HbD)). }
      assert (Hle : S w' <= w').
      { exact (InjectionPrinciple.cardinal_injection_principle_poly
                 A (Ensemble A) la
                 (fun D => In (Ensemble A) cover D /\ D <> C)
                 (fun a D => In A D a) (S w') w'
                 Htot Hinj Hcard_la Hcard_minus). }
      lia.
  Qed.

  (** Image of a finite set under a function has cardinality ≤ the source. *)
  Lemma image_cardinal_le : forall {B : Type} (S : Ensemble A) (f : A -> B) n,
    cardinal A S n ->
    exists m, cardinal B (fun y => exists x, In A S x /\ y = f x) m /\ m <= n.
  Proof.
    intros B S f n Hcard.
    induction Hcard as [| S' k Hcard' [m [Hm Hmk]] a Ha_notin].
    - exists 0. split.
      + assert (Heq : (fun y : B => exists x : A, In A (Empty_set A) x /\ y = f x) = Empty_set B).
        { apply Extensionality_Ensembles. intro y. split.
          - intros [x [Hx _]]. inversion Hx.
          - intro Hy. inversion Hy. }
        rewrite Heq. apply card_empty.
      + lia.
    - (* S = Add S' a *)
      destruct (classic (In B (fun y => exists x, In A S' x /\ y = f x) (f a))) as [Hin | Hnin].
      + (* f a already in image of S' *)
        exists m. split.
        * apply (cardinal_extensional_poly B
            (fun y => exists x, In A S' x /\ y = f x)
            (fun y => exists x, In A (Add A S' a) x /\ y = f x) m).
          { intro y. split; intro Hy.
            - destruct Hy as [x0 [Hx0 Heq_y]].
              exists x0. split; [apply Union_introl; exact Hx0 | exact Heq_y].
            - destruct Hy as [x0 [Hx0 Heq_y]].
              assert (Hcase : In A S' x0 \/ x0 = a).
              { unfold Add in Hx0.
                inversion Hx0 as [z Hz | z Hz].
                - left. exact Hz.
                - right. inversion Hz. reflexivity. }
              destruct Hcase as [Hx0_S' | Hx0_a].
              + exists x0. split; [exact Hx0_S' | exact Heq_y].
              + subst x0.
                destruct Hin as [x1 [Hx1 Heq1]].
                exists x1. split; [exact Hx1 | congruence]. }
          exact Hm.
        * lia.
      + (* f a not in image of S' *)
        exists (S m). split.
        * apply (cardinal_extensional_poly B
            (Add B (fun y => exists x, In A S' x /\ y = f x) (f a))
            (fun y => exists x, In A (Add A S' a) x /\ y = f x) (S m)).
          { intro y. split; intro Hy.
            - inversion Hy as [y0 Hy0 | y0 Hy0].
              + destruct Hy0 as [x0 [Hx0 Heq_y]].
                exists x0. split; [apply Union_introl; exact Hx0 | exact Heq_y].
              + inversion Hy0. subst y.
                exists a. split; [apply Union_intror; apply In_singleton | reflexivity].
            - destruct Hy as [x0 [Hx0 Heq_y]].
              assert (Hcase : In A S' x0 \/ x0 = a).
              { unfold Add in Hx0.
                inversion Hx0 as [z Hz | z Hz].
                - left. exact Hz.
                - right. inversion Hz. reflexivity. }
              destruct Hcase as [Hx0_S' | Hx0_a].
              + apply Union_introl. exists x0. split; [exact Hx0_S' | exact Heq_y].
              + subst x0. apply Union_intror. rewrite Heq_y. apply In_singleton. }
          apply card_add; assumption.
        * lia.
  Qed.

End Helpers.
