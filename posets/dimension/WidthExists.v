(** * Width existence: every finite nonempty poset has a maximum antichain.

    Needed to rewire [hiraguchi_bound] through [dimension_le_width] +
    [antichain_complement_dim_bound]. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Arith Lia Classical.
From Posets Require Import PosetClasses.
From Dilworth Require Import Definitions.
From Dimension Require Import DimDefs Theorems.

(** A bounded nat-predicate that holds somewhere has a maximum witness. *)
Lemma bounded_max_exists :
  forall (P : nat -> Prop) (n : nat),
    (exists k, k <= n /\ P k) ->
    exists m, m <= n /\ P m /\ (forall j, j <= n -> P j -> j <= m).
Proof.
  intros P n. induction n as [| n' IH]; intros [k [Hk Hpk]].
  - assert (k = 0) by lia. subst k.
    exists 0. split; [ lia | split; [ exact Hpk | intros j Hj _; lia ] ].
  - destruct (classic (P (S n'))) as [Hpsn | Hnpsn].
    + exists (S n'). split; [ lia | split; [ exact Hpsn | intros j Hj _; lia ] ].
    + assert (Hk' : k <= n').
      { destruct (Nat.eq_dec k (S n')) as [Heq | Hne]; [ subst k; contradiction | lia ]. }
      destruct (IH (ex_intro _ k (conj Hk' Hpk))) as [m [Hm [Hpm Hmax]]].
      exists m. split; [ lia | split; [ exact Hpm |] ].
      intros j Hj Hpj. destruct (Nat.eq_dec j (S n')) as [Heq | Hne];
        [ subst j; contradiction | apply Hmax; [ lia | exact Hpj ] ].
Qed.

Section WidthExists.
  Context {A : Type}.
  Context (R : A -> A -> Prop) `{IsPoset A R}.

  (** A singleton is an antichain. *)
  Lemma singleton_antichain : forall a : A, IsAntichain R (Singleton A a).
  Proof.
    intro a. constructor.
    - exists a. constructor.
    - intros x y Hx Hy _. destruct Hx; destruct Hy; reflexivity.
  Qed.

  Theorem width_exists :
    forall n, cardinal A (Full_set A) n -> Inhabited A (Full_set A) ->
      exists w, inhabited (Width R (Full_set A) w).
  Proof.
    intros n Hn [a0 _].
    set (P := fun k => exists s : Ensemble A,
                IsAntichain R s /\ Included A s (Full_set A) /\ cardinal A s k).
    (* P holds at 1 (a singleton), bounded by n *)
    assert (Hstart : exists k, k <= n /\ P k).
    { exists 1. split.
      - (* 1 <= n: the singleton is included in Full of cardinal n *)
        apply (incl_card_le A (Singleton A a0) (Full_set A) 1 n
                 (singleton_cardinal A a0) Hn).
        intros x _; apply Full_intro.
      - exists (Singleton A a0).
        split; [ apply singleton_antichain |].
        split; [ intros x _; apply Full_intro | apply singleton_cardinal ]. }
    destruct (bounded_max_exists P n Hstart) as [w [Hwn [Hpw Hmax]]].
    destruct Hpw as [la [Hla_anti [Hla_incl Hla_card]]].
    exists w. constructor.
    refine {| width_la := la;
              width_is_largest := {| largest_antichain_is_antichain := Hla_anti;
                                     largest_antichain_included := Hla_incl;
                                     largest_antichain_cardinality := Hla_card;
                                     largest_antichain_is_maximum := _ |} |}.
    intros s ns Hs_anti Hs_incl Hs_card.
    apply Hmax.
    - (* ns <= n *)
      apply (incl_card_le A s (Full_set A) ns n Hs_card Hn). exact Hs_incl.
    - exists s. split; [ exact Hs_anti | split; [ exact Hs_incl | exact Hs_card ] ].
  Qed.

End WidthExists.
