(* Canonical partial order derived from a meet-semilattice: x ≤ y iff meet x y = x *)

From Posets Require Import PosetClasses LatticeClasses.

Section MeetOrder.
  Context {A : Type} (meet : A -> A -> A) `{IsMeetSemilattice A meet}.

  Definition meet_le : A -> A -> Prop := fun x y => meet x y = x.

  #[export] Instance meet_semilattice_is_poset : IsPoset A meet_le.
  Proof.
    constructor.
    - (* Reflexivity: meet x x = x *)
      intro x. unfold meet_le. apply meet_idem.
    - (* Antisymmetry: meet x y = x ∧ meet y x = y → x = y *)
      intros x y Hxy Hyx. unfold meet_le in *.
      rewrite meet_comm in Hyx.
      rewrite Hxy in Hyx.
      exact Hyx.
    - (* Transitivity: meet x y = x ∧ meet y z = y → meet x z = x *)
      intros x y z Hxy Hyz. unfold meet_le in *.
      (* Goal: meet x z = x.
         We show meet x z = meet (meet x y) z = meet x (meet y z) = meet x y = x *)
      transitivity (meet (meet x y) z).
      + rewrite Hxy. reflexivity.
      + rewrite meet_assoc. rewrite Hyz. exact Hxy.
  Qed.
End MeetOrder.
