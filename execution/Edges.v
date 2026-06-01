From Stdlib Require Import List Arith Lia Relation_Operators.
From Execution Require Import Op Event.

Section Edges.
  Context (P : Program).

  (* Direct causal edge between two valid events. *)
  Definition edge (a b : Event P) : Prop :=
    let (pa, ia) := proj1_sig a in
    let (pb, ib) := proj1_sig b in
    (* program order: next op in the same process *)
    (pa = pb /\ ib = S ia)
    \/
    (* message: a is a Send matched by recv b *)
    (exists t, op_at P pa ia = Some (Send pb t)
            /\ op_at P pb ib = Some (Recv pa t)).

  (* Execution-poset order = reflexive-transitive closure of edge. *)
  Definition hb (a b : Event P) : Prop := clos_refl_trans (Event P) edge a b.

End Edges.

(* ------------------------------------------------------------------ *)
(* Basic order properties (P explicit)                                  *)
(* ------------------------------------------------------------------ *)

Lemma hb_refl : forall P (a : Event P), hb P a a.
Proof.
  intros P a.
  apply rt_refl.
Qed.

Lemma hb_trans : forall P (a b c : Event P), hb P a b -> hb P b c -> hb P a c.
Proof.
  intros P a b c Hab Hbc.
  eapply rt_trans; eassumption.
Qed.
