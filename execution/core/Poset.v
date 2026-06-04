From Stdlib Require Import Ensembles Finite_sets.
From Posets Require Import PosetClasses FinitePoset.
From Execution Require Import Op Event Edges Rank Finite.

(* hb on a ranked program is a partial order. *)
Instance hb_IsPoset (R : RankedProgram) : IsPoset (Event R) (hb R).
Proof.
  refine {| poset_refl := hb_refl R;
            poset_antisym := hb_antisym R;
            poset_trans := hb_trans R |}.
Qed.

(* and a finite poset of size [total]. *)
Instance hb_IsFinitePoset (R : RankedProgram) :
  IsFinitePoset (Event R) (hb R) (total R).
Proof.
  refine {| fp_is_poset := hb_IsPoset R;
            fp_finite   := event_cardinal R |}.
Qed.

(* The canonical object the rest of the framework passes around. *)
Record ExecPoset := {
  ep_ranked  : RankedProgram;
  ep_size    : nat;
  ep_size_ok : cardinal (Event ep_ranked) (Full_set (Event ep_ranked)) ep_size
}.

Definition ep_carrier (E : ExecPoset) := Event (ep_ranked E).
Definition ep_order   (E : ExecPoset) := hb (ep_ranked E).

(* Smart constructor from any ranked program. *)
Definition exec_of (R : RankedProgram) : ExecPoset :=
  {| ep_ranked  := R;
     ep_size    := total R;
     ep_size_ok := event_cardinal R |}.
