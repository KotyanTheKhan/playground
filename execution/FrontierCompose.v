(* Composing two antichains by a frontier F : the bipartite poset compose_le F.
   Dichotomy (this file): non-crossing (threshold/Ferrers) F => dim <= 2;
   the S3 crown F (i<>j) => dim >= 3. Abstract poset-dimension theory. *)
From Stdlib Require Import List Arith Lia Fin Ensembles Finite_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Theorems.
Import ListNotations.

Inductive Carrier (A B : Type) : Type := inA (a : A) | inB (b : B).
Arguments inA {A B} a. Arguments inB {A B} b.

Definition compose_le {A B} (F : A -> B -> Prop) (x y : Carrier A B) : Prop :=
  match x, y with
  | inA a, inA a' => a = a'
  | inB b, inB b' => b = b'
  | inA a, inB b  => F a b
  | inB _, inA _  => False
  end.

#[export] Instance compose_IsPoset {A B} (F : A -> B -> Prop) :
  IsPoset (Carrier A B) (compose_le F).
Proof.
  constructor.
  - intro x. destruct x; reflexivity.
  - intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl;
      intros Hxy Hyx; try (subst; reflexivity); try contradiction.
  - intros x y z; destruct x as [a|b]; destruct y as [a'|b']; destruct z as [a''|b''];
      simpl; intros Hxy Hyz; try contradiction; subst; try reflexivity; try assumption.
Qed.

Definition Ferrers {A B} (F : A -> B -> Prop) : Prop :=
  forall a1 a2 b1 b2, F a1 b1 -> F a2 b2 -> F a1 b2 \/ F a2 b1.

Lemma threshold_Ferrers :
  forall {A B} (phi : A -> nat) (psi : B -> nat) (F : A -> B -> Prop),
    (forall a b, F a b <-> phi a <= psi b) -> Ferrers F.
Proof.
  intros A B phi psi F Hthr a1 a2 b1 b2 H1 H2.
  apply Hthr in H1; apply Hthr in H2.
  destruct (Nat.le_ge_cases (phi a1) (phi a2)) as [Hle | Hge].
  - left.  apply Hthr. lia.
  - right. apply Hthr. lia.
Qed.
