(* YAML lexer / line model — leniency layer (comments, indent, blank lines). *)
From Stdlib Require Import String Ascii List Arith Lia.
Import ListNotations.
Open Scope string_scope.

(* ---- char helpers ---- *)
Definition is_space (c : ascii) : bool :=
  orb (Nat.eqb (nat_of_ascii c) 32) (Nat.eqb (nat_of_ascii c) 9).
Definition is_digit (c : ascii) : bool :=
  andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57).
Definition digit_val (c : ascii) : nat := nat_of_ascii c - 48.
Definition is_char (c : ascii) (code : nat) : bool := Nat.eqb (nat_of_ascii c) code.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with EmptyString => [] | String c r => c :: list_of_string r end.
Fixpoint string_of_list (l : list ascii) : string :=
  match l with [] => EmptyString | c :: r => String c (string_of_list r) end.

(* ---- line splitting on '\n' (code 10) ---- *)
Fixpoint split_lines (l : list ascii) : list (list ascii) :=
  match l with
  | [] => [[]]
  | c :: r => if is_char c 10
              then [] :: split_lines r
              else match split_lines r with
                   | [] => [[c]]            (* unreachable; split_lines is always nonempty *)
                   | h :: t => (c :: h) :: t
                   end
  end.

(* ---- per-line cleaning ---- *)
Definition strip_cr (l : list ascii) : list ascii :=
  filter (fun c => negb (is_char c 13)) l.
Fixpoint strip_comment (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: r => if is_char c 35 (* '#' *) then [] else c :: strip_comment r
  end.
Fixpoint measure_indent (l : list ascii) : nat * list ascii :=
  match l with
  | c :: r => if is_space c then let (n, rest) := measure_indent r in (S n, rest)
              else (0, l)
  | [] => (0, [])
  end.
Fixpoint drop_leading_space (l : list ascii) : list ascii :=
  match l with c :: r => if is_space c then drop_leading_space r else l | [] => [] end.
Definition trim_both (l : list ascii) : list ascii :=
  drop_leading_space (rev (drop_leading_space (rev l))).
Definition trim_trailing (l : list ascii) : list ascii :=
  rev (drop_leading_space (rev l)).

Record Line := { ln_indent : nat; ln_text : list ascii }.

Definition clean_one (raw : list ascii) : option Line :=
  let nocr := strip_cr raw in
  let nocomment := strip_comment nocr in
  let (ind, rest) := measure_indent nocomment in
  match trim_trailing rest with
  | [] => None
  | (_ :: _) as t => Some {| ln_indent := ind; ln_text := t |}
  end.

Definition clean_lines (s : string) : list Line :=
  fold_right (fun raw acc => match clean_one raw with Some ln => ln :: acc | None => acc end)
             [] (split_lines (list_of_string s)).

(* ---- lenient decimal ---- *)
Fixpoint nat_of_digits_aux (l : list ascii) (acc : nat) : option nat :=
  match l with
  | [] => Some acc
  | c :: r => if is_digit c then nat_of_digits_aux r (acc * 10 + digit_val c) else None
  end.
Definition nat_of_digits (l : list ascii) : option nat :=
  match l with [] => None | _ => nat_of_digits_aux l 0 end.

(* ---- boolean list-of-ascii equality ---- *)
Fixpoint la_eqb (a b : list ascii) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => andb (Nat.eqb (nat_of_ascii x) (nat_of_ascii y)) (la_eqb a' b')
  | _, _ => false
  end.
