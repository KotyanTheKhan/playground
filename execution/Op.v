From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition Pid := nat.
Definition Tag := nat.

(* One operation = one event in a process's local chain. *)
Inductive Op : Type :=
  | Local
  | Send (target : Pid) (tag : Tag)
  | Recv (from   : Pid) (tag : Tag).

(* A program: [procs] is per-process operation lists, process p = nth p procs. *)
Record Program := { procs : list (list Op) }.

Definition nprocs (P : Program) : nat := length (procs P).
Definition proc_ops (P : Program) (p : Pid) : list Op := nth p (procs P) [].
Definition proc_len (P : Program) (p : Pid) : nat := length (proc_ops P p).

(* op at (p,i), if present *)
Definition op_at (P : Program) (p i : Pid) : option Op := nth_error (proc_ops P p) i.

(* A send at (p,i) to q with tag t is *matched* by the recv at (q,j):
   op_at P p i = Some (Send q t) and op_at P q j = Some (Recv p t). *)
Definition matched (P : Program) (p i q j : nat) (t : Tag) : Prop :=
  op_at P p i = Some (Send q t) /\ op_at P q j = Some (Recv p t).

(* Well-formedness: every Recv has exactly one matching Send and vice versa,
   and targets are in range. Stated as a record so callers can use fields. *)
Record wf_program (P : Program) : Prop := {
  wf_send_targets :
    forall p i q t, op_at P p i = Some (Send q t) -> q < nprocs P;
  wf_recv_sources :
    forall q j p t, op_at P q j = Some (Recv p t) -> p < nprocs P;
  (* each recv matched by a unique send *)
  wf_recv_matched :
    forall q j p t, op_at P q j = Some (Recv p t) ->
      exists! i, op_at P p i = Some (Send q t);
  (* each send matched by a unique recv *)
  wf_send_matched :
    forall p i q t, op_at P p i = Some (Send q t) ->
      exists! j, op_at P q j = Some (Recv p t)
}.
