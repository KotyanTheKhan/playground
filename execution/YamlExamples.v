(* YAML I/O examples (test-only): real data-file instances, dump byte-fidelity,
   and the S(3,1) poset as an actual IsPoset. *)

From Stdlib Require Import String Ascii List Arith Lia.
From Posets Require Import PosetClasses.
From Execution Require Import Schedule Yaml.
Import ListNotations.
Open Scope string_scope.

Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.

Definition nl_e : string := String (Ascii.ascii_of_nat 10) "".

(* byte-fidelity vs the libnomadim data/*.yaml files *)
Example dump_exec_dim2_eq :
  dump (DocExecution exec_dim2) =
  "execution:" ++ nl_e ++ "  n_procs: 2" ++ nl_e ++ "  syncs:" ++ nl_e ++
  "    - [0, 1]" ++ nl_e.
Proof. vm_compute. reflexivity. Qed.

Example dump_exec_4_eq :
  dump (DocExecution exec_4_canonical) =
  "execution:" ++ nl_e ++ "  n_procs: 4" ++ nl_e ++ "  syncs:" ++ nl_e ++
  "    - [0, 1]" ++ nl_e ++ "    - [1, 2]" ++ nl_e ++ "    - [2, 3]" ++ nl_e ++
  "    - [0, 2]" ++ nl_e.
Proof. vm_compute. reflexivity. Qed.

Example dump_poset_s3_eq :
  dump (DocPoset poset_s3) =
  "poset:" ++ nl_e ++ "  n_vertices: 6" ++ nl_e ++ "  edges:" ++ nl_e ++
  "    - [0, 4]" ++ nl_e ++ "    - [0, 5]" ++ nl_e ++ "    - [1, 3]" ++ nl_e ++
  "    - [1, 5]" ++ nl_e ++ "    - [2, 3]" ++ nl_e ++ "    - [2, 4]" ++ nl_e.
Proof. vm_compute. reflexivity. Qed.

Example exec_dim2_schedule_nprocs : sch_nprocs (schedule_of_yaml exec_dim2) = 2.
Proof. reflexivity. Qed.

(* S(3,1): {0,1,2} are minimals, {3,4,5} maximals; every edge goes low->high. *)
Example poset_s3_is_poset : IsPoset (Vert poset_s3) (yaml_order poset_s3).
Proof.
  apply yaml_order_IsPoset.
  unfold wf_yaml_poset. split.
  - (* range: every edge endpoint < 6 *)
    intros a b Hin. simpl in Hin.
    destruct Hin as [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[]]]]]]];
      injection Heq as Ha Hb; subst a b; cbn; split; lia.
  - (* rank witness: level n := if n <? 3 then 0 else 1 strictly increases on each edge *)
    exists (fun n => if Nat.ltb n 3 then 0 else 1).
    intros a b Hin. simpl in Hin.
    destruct Hin as [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[]]]]]]];
      injection Heq as Ha Hb; subst a b; vm_compute; lia.
Qed.
