(* YAML parser — field/pair parsers + document assembler over cleaned lines. *)
From Stdlib Require Import String Ascii List Arith Lia.
From ExecYaml Require Import Yaml YamlLex.
Import ListNotations.
Open Scope string_scope.

(* split on first ':' *)
Fixpoint split_colon (l : list ascii) : option (list ascii * list ascii) :=
  match l with
  | [] => None
  | c :: r => if is_char c 58 (* ':' *) then Some ([], r)
              else match split_colon r with
                   | Some (k, v) => Some (c :: k, v)
                   | None => None
                   end
  end.
Definition parse_key_value (l : list ascii) : option (list ascii * list ascii) :=
  match split_colon l with
  | Some (k, v) => Some (trim_both k, trim_both v)
  | None => None
  end.

Definition match_key (key : string) (ln : Line) : bool :=
  match parse_key_value (ln_text ln) with
  | Some (k, v) => andb (la_eqb k (list_of_string key))
                        (match v with [] => true | _ => false end)
  | None => false
  end.
Definition parse_nat_field (key : string) (ln : Line) : option nat :=
  match parse_key_value (ln_text ln) with
  | Some (k, v) => if la_eqb k (list_of_string key) then nat_of_digits v else None
  | None => None
  end.

(* lenient "[a, b]" or "a, b" *)
Definition strip_brackets (l : list ascii) : list ascii :=
  let l1 := match l with c :: r => if is_char c 91 (* '[' *) then r else l | [] => l end in
  match rev l1 with
  | c :: r => if is_char c 93 (* ']' *) then rev r else l1
  | [] => l1
  end.
Fixpoint split_comma (l : list ascii) : list ascii * list ascii :=
  match l with
  | [] => ([], [])
  | c :: r => if is_char c 44 (* ',' *) then ([], r)
              else let (a, b) := split_comma r in (c :: a, b)
  end.
Definition parse_pair (l : list ascii) : option (nat * nat) :=
  let inner := strip_brackets (trim_both l) in
  let (a, b) := split_comma inner in
  match nat_of_digits (trim_both a), nat_of_digits (trim_both b) with
  | Some x, Some y => Some (x, y)
  | _, _ => None
  end.

Definition parse_seq_item (ln : Line) : option (nat * nat) :=
  match ln_text ln with
  | c :: r => if is_char c 45 (* '-' *) then parse_pair (trim_both r) else None
  | [] => None
  end.

(* greedily consume leading seq-item lines *)
Fixpoint parse_pairs_block (lines : list Line) : list (nat * nat) * list Line :=
  match lines with
  | ln :: rest =>
      match parse_seq_item ln with
      | Some p => let (ps, leftover) := parse_pairs_block rest in (p :: ps, leftover)
      | None => ([], lines)
      end
  | [] => ([], [])
  end.

Fixpoint parse_exec_fields (fuel : nat) (lines : list Line) (nprocs : option nat)
                           (syncs : option (list (nat * nat))) : option YamlExecution :=
  match fuel with
  | O => None
  | S f =>
    match lines with
    | [] => match nprocs with
            | Some n => Some {| ye_nprocs := n;
                                ye_syncs := match syncs with Some s => s | None => [] end |}
            | None => None
            end
    | ln :: rest =>
        match parse_nat_field "n_procs" ln with
        | Some n => parse_exec_fields f rest (Some n) syncs
        | None => if match_key "syncs" ln
                  then let (ps, leftover) := parse_pairs_block rest in
                       parse_exec_fields f leftover nprocs (Some ps)
                  else parse_exec_fields f rest nprocs syncs   (* lenient: skip unknown *)
        end
    end
  end.

Fixpoint parse_poset_fields (fuel : nat) (lines : list Line) (nverts : option nat)
                            (edges : option (list (nat * nat))) : option YamlPoset :=
  match fuel with
  | O => None
  | S f =>
    match lines with
    | [] => match nverts with
            | Some n => Some {| yp_nverts := n;
                                yp_edges := match edges with Some e => e | None => [] end |}
            | None => None
            end
    | ln :: rest =>
        match parse_nat_field "n_vertices" ln with
        | Some n => parse_poset_fields f rest (Some n) edges
        | None => if match_key "edges" ln
                  then let (ps, leftover) := parse_pairs_block rest in
                       parse_poset_fields f leftover nverts (Some ps)
                  else parse_poset_fields f rest nverts edges
        end
    end
  end.

Definition parse_document (s : string) : option Document :=
  match clean_lines s with
  | ln :: rest =>
      if match_key "execution" ln
      then match parse_exec_fields (length rest) rest None None with
           | Some e => Some (DocExecution e) | None => None end
      else if match_key "poset" ln
      then match parse_poset_fields (length rest) rest None None with
           | Some p => Some (DocPoset p) | None => None end
      else None
  | [] => None
  end.
