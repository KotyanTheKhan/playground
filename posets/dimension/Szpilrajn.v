From Stdlib Require Import Ensembles Finite_sets Arith Classical.
From Coq Require Import FunctionalExtensionality PropExtensionality.
From Coq Require Import Relations.Relation_Operators.
From ZornsLemma Require Import ZornsLemma EnsemblesImplicit.
From Posets Require Import PosetClasses.

(** Generalized: TC(M ∪ {(q,p)}) is a poset when p and q are incomparable in M. *)
Lemma add_incomparable_general :
  forall (A : Type) (M : A -> A -> Prop) `{HM : IsPoset A M} (p q : A),
  ~ (M p q \/ M q p) ->
  IsPoset A (@clos_trans A (fun a b => M a b \/ (a = q /\ b = p))).
Proof.
  intros A M HM p q Hinc.
  set (ext := fun a b => M a b \/ (a = q /\ b = p)).
  (* Path invariant: every path in TC(ext) from a to b satisfies
     M a b  \/  (M a q /\ M p b). *)
  assert (Hinv : forall a b,
    @clos_trans A ext a b -> M a b \/ (M a q /\ M p b)).
  { intros a b Htc.
    induction Htc as [a b Hstep | a m b _ IH1 _ IH2].
    - destruct Hstep as [HMab | [-> ->]].
      + left; exact HMab.
      + right; split; apply poset_refl.
    - destruct IH1 as [Ham | [Haq Hpm]],
               IH2 as [Hmb | [Hmq Hpb]].
      + left; eapply poset_trans; eauto.
      + right; split; [eapply poset_trans; eauto | auto].
      + right; split; [auto | eapply poset_trans; eauto].
      + exfalso; apply Hinc; left; eapply poset_trans; eauto. }
  constructor.
  - intro a; apply t_step; left; apply poset_refl.
  - intros a b Hab Hba.
    destruct (Hinv a b Hab) as [HMab | [Haq Hpb]],
             (Hinv b a Hba) as [HMba | [Hbq Hpa]].
    + eapply poset_antisym; eauto.
    + exfalso; apply Hinc; left;
        eapply poset_trans; [eapply poset_trans; [exact Hpa | exact HMab] | exact Hbq].
    + exfalso; apply Hinc; left;
        eapply poset_trans; [eapply poset_trans; [exact Hpb | exact HMba] | exact Haq].
    + exfalso; apply Hinc; left; eapply poset_trans; [exact Hpb | exact Hbq].
  - intros a b c Hab Hbc; eapply t_trans; eauto.
Qed.
