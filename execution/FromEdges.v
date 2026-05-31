From Stdlib Require Import List Arith Lia Relation_Operators Eqdep_dec.
From Execution Require Import Op Event Edges Rank Poset.
Import ListNotations.

(* A message: sender process, sender index, receiver process, receiver index, tag. *)
Record EdgeSpec := {
  es_nprocs : nat;
  es_lens   : list nat;                            (* proc_len of each process *)
  es_msgs   : list (nat * nat * nat * nat * nat)   (* (sp, si, rq, rj, tag) *)
}.

(* The op of process p at local index i, induced by the message list. *)
Definition op_at_es (e : EdgeSpec) (p i : nat) : Op :=
  match find (fun m => let '(sp, si, _, _, _) := m in
                       andb (Nat.eqb sp p) (Nat.eqb si i)) (es_msgs e) with
  | Some (_, _, q, _, t) => Send q t
  | None =>
    match find (fun m => let '(_, _, rq, rj, _) := m in
                         andb (Nat.eqb rq p) (Nat.eqb rj i)) (es_msgs e) with
    | Some (sp, _, _, _, t) => Recv sp t
    | None => Local
    end
  end.

Definition prog_of_edgespec (e : EdgeSpec) : Program :=
  {| procs :=
       map (fun p => map (fun i => op_at_es e p i)
                         (seq 0 (nth p (es_lens e) 0)))
           (seq 0 (es_nprocs e)) |}.

(* Wrap an edge-spec program with a caller-supplied rank and its monotonicity proof. *)
Definition edgespec_ranked (e : EdgeSpec) (rk : nat * nat -> nat)
  (Hmono : forall a b : Event (prog_of_edgespec e),
             edge (prog_of_edgespec e) a b ->
             rk (proj1_sig a) < rk (proj1_sig b))
  : RankedProgram :=
  {| rp_prog := prog_of_edgespec e;
     rp_rank := rk;
     rp_rank_mono := Hmono |}.

Definition from_edges (e : EdgeSpec) (rk : nat * nat -> nat)
  (Hmono : forall a b : Event (prog_of_edgespec e),
             edge (prog_of_edgespec e) a b ->
             rk (proj1_sig a) < rk (proj1_sig b))
  : ExecPoset :=
  exec_of (edgespec_ranked e rk Hmono).

(* Equal underlying programs have the same happened-before order (transporting
   events along the program equality). This is the provable "rules <-> edge-set
   agreement": whenever a schedule and an edge-spec yield the same Program, their
   posets coincide. *)
Theorem hb_prog_eq :
  forall (P Q : Program) (H : P = Q) (a b : Event P),
    hb P a b <->
    hb Q (eq_rect P (fun X => Event X) a Q H)
         (eq_rect P (fun X => Event X) b Q H).
Proof.
  intros P Q H a b.
  destruct H.
  simpl.
  tauto.
Qed.
