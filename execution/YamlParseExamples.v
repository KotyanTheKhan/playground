(* YAML reader examples (test-only): round-trip + messy-input acceptance. *)
From Stdlib Require Import String Ascii List Arith.
From Execution Require Import Yaml YamlLex YamlParse.
Import ListNotations.
Open Scope string_scope.

Definition exec_dim2 : YamlExecution := {| ye_nprocs := 2; ye_syncs := [(0,1)] |}.
Definition exec_4_canonical : YamlExecution :=
  {| ye_nprocs := 4; ye_syncs := [(0,1);(1,2);(2,3);(0,2)] |}.
Definition poset_s3 : YamlPoset :=
  {| yp_nverts := 6; yp_edges := [(0,4);(0,5);(1,3);(1,5);(2,3);(2,4)] |}.

(* read back exactly what we wrote (instance-level round-trip) *)
Example roundtrip_exec_dim2 :
  parse_document (dump (DocExecution exec_dim2)) = Some (DocExecution exec_dim2).
Proof. vm_compute. reflexivity. Qed.

Example roundtrip_exec_4 :
  parse_document (dump (DocExecution exec_4_canonical)) = Some (DocExecution exec_4_canonical).
Proof. vm_compute. reflexivity. Qed.

Example roundtrip_poset_s3 :
  parse_document (dump (DocPoset poset_s3)) = Some (DocPoset poset_s3).
Proof. vm_compute. reflexivity. Qed.

(* leniency: a messy hand-edited variant parses to the SAME document *)
Definition messy_exec : string :=
"# an execution file
execution:
  n_procs:   2

  syncs:
    -  [0,1]   # the only sync
".

Example accept_messy_exec :
  parse_document messy_exec = Some (DocExecution exec_dim2).
Proof. vm_compute. reflexivity. Qed.

Definition messy_poset : string :=
"poset:
  n_vertices: 6
  edges:
    - [0,4]
    - [0, 5]
    -   [1,3]
    - [1, 5]
    - [2,3]
    - [2, 4]
".

Example accept_messy_poset :
  parse_document messy_poset = Some (DocPoset poset_s3).
Proof. vm_compute. reflexivity. Qed.
