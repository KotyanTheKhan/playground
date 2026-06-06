(** * Kleene fixed-point theorem.

    On a complete lattice (a pointed dcpo), an ω-continuous monotone map f has
    least fixed point [sup_n f^n(bot)] — the supremum of the ascending Kleene
    chain bot <= f bot <= f^2 bot <= ...

    The complete lattice is presented as a poset [(A,R)] with [inf]/[sup]
    operators (as in KnasterTarski); [bot := inf (Full_set)] is the least
    element, and ω-continuity of f is hypothesized on ascending sequences.

    Index entry: [kleene-fixpoint] in docs/references/poset-facts-index.md. *)
From Stdlib Require Import Ensembles Arith Lia.
From Posets Require Import PosetClasses.

Section Kleene.
  Context {A : Type} (R : A -> A -> Prop) `{IsPoset A R}.

  Definition IsLowerBound (S : Ensemble A) (m : A) : Prop :=
    forall x, In A S x -> R m x.
  Definition IsGLB (S : Ensemble A) (m : A) : Prop :=
    IsLowerBound S m /\ forall l, IsLowerBound S l -> R l m.
  Definition IsUpperBound (S : Ensemble A) (m : A) : Prop :=
    forall x, In A S x -> R x m.
  Definition IsLUB (S : Ensemble A) (m : A) : Prop :=
    IsUpperBound S m /\ forall u, IsUpperBound S u -> R m u.

  Context (sup : Ensemble A -> A) (Hsup : forall S, IsLUB S (sup S)).
  Context (inf : Ensemble A -> A) (Hinf : forall S, IsGLB S (inf S)).

  (** Convenience: membership <= sup, and sup is below any upper bound. *)
  Lemma le_sup : forall S x, In A S x -> R x (sup S).
  Proof. intros S x Hx. destruct (Hsup S) as [Hub _]. apply Hub; exact Hx. Qed.

  Lemma sup_le : forall S u, IsUpperBound S u -> R (sup S) u.
  Proof. intros S u Hu. destruct (Hsup S) as [_ Hleast]. apply Hleast; exact Hu. Qed.

  (** Least element. *)
  Definition bot : A := inf (Full_set A).
  Lemma bot_least : forall x, R bot x.
  Proof.
    intro x. destruct (Hinf (Full_set A)) as [Hlb _].
    apply Hlb. constructor.
  Qed.

  Context (f : A -> A) (Hmono : forall x y, R x y -> R (f x) (f y)).

  (** The Kleene chain f^n(bot). *)
  Fixpoint iter (n : nat) : A :=
    match n with
    | 0 => bot
    | S k => f (iter k)
    end.

  Lemma iter_step : forall n, R (iter n) (iter (S n)).
  Proof.
    induction n.
    - apply bot_least.
    - simpl. apply Hmono. exact IHn.
  Qed.

  Definition chainSet : Ensemble A := fun a => exists n, a = iter n.
  Definition image_f_chain : Ensemble A := fun a => exists n, a = f (iter n).

  Definition kleene_lfp : A := sup chainSet.

  Lemma in_chainSet : forall n, In A chainSet (iter n).
  Proof. intro n. exists n. reflexivity. Qed.

  Lemma in_image_f_chain : forall n, In A image_f_chain (f (iter n)).
  Proof. intro n. exists n. reflexivity. Qed.

  (** ω-continuity of f on ascending sequences. *)
  Hypothesis Hcont :
    forall g : nat -> A,
      (forall n, R (g n) (g (S n))) ->
      f (sup (fun a => exists n, a = g n)) = sup (fun a => exists n, a = f (g n)).

  (** sup of the iterates is a fixed point. *)
  Theorem kleene_lfp_fixed : f kleene_lfp = kleene_lfp.
  Proof.
    unfold kleene_lfp, chainSet.
    rewrite (Hcont iter iter_step).
    (* goal: sup image_f_chain = sup chainSet (image_f_chain = {f (iter n)}) *)
    apply (poset_antisym (R := R)).
    - (* sup {f(iter n)} <= sup {iter n} *)
      apply sup_le. intros x [n Hx]. subst x.
      change (f (iter n)) with (iter (S n)).
      apply le_sup. exists (S n). reflexivity.
    - (* sup {iter n} <= sup {f(iter n)} *)
      apply sup_le. intros x [n Hx]. subst x.
      apply (poset_trans (R := R) (iter n) (f (iter n)) (sup (fun a => exists m, a = f (iter m)))).
      + change (f (iter n)) with (iter (S n)). apply iter_step.
      + apply le_sup. exists n. reflexivity.
  Qed.

  (** It is the least (pre-)fixed point. *)
  Theorem kleene_lfp_least : forall y, f y = y -> R kleene_lfp y.
  Proof.
    intros y Hy.
    assert (Hall : forall n, R (iter n) y).
    { induction n.
      - apply bot_least.
      - simpl. rewrite <- Hy. apply Hmono. exact IHn. }
    apply sup_le. intros x [n Hx]. subst x. apply Hall.
  Qed.

End Kleene.
