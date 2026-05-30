(** Throwaway extractor: print the canonical 7-edge iso-class shapes among the
    count-6 (4-incomparable-pair) posets, by lexmin edge-encoding over all 120
    relabelings.  Run via [Eval vm_compute]; the output seeds the count-6
    pattern list (like N5Reflect8's six count-8 shapes). Not part of the build's
    logical content. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From Dimension.N5Exhaustive Require Import N5Reflect N5Reflect8.

Definition f2n (i : Fin.t 5) : nat := proj1_sig (Fin.to_nat i).

Definition perm_app (perm : list (Fin.t 5)) (i : Fin.t 5) : Fin.t 5 :=
  nth (f2n i) perm f0.

Definition Mperm (M : M5) (perm : list (Fin.t 5)) : M5 :=
  fun i j => M (perm_app perm i) (perm_app perm j).

Definition encode_edges (M : M5) : list nat :=
  map (fun p => 5 * f2n (fst p) + f2n (snd p))
      (filter (fun p => strict_b M (fst p) (snd p)) all_pairs).

Fixpoint insertn (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: l' => if Nat.leb x y then x :: y :: l' else y :: insertn x l'
  end.
Definition sortn (l : list nat) : list nat := fold_right insertn [] l.

Fixpoint lex_ltb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: l1', y :: l2' =>
      if Nat.ltb x y then true
      else if Nat.ltb y x then false else lex_ltb l1' l2'
  end.

Definition canon (M : M5) : list nat :=
  fold_left (fun acc perm =>
               let e := sortn (encode_edges (Mperm M perm)) in
               if lex_ltb e acc then e else acc)
            all_perms5 (sortn (encode_edges M)).

Definition count6_assigns : list (list (option bool)) := enum_k_none 10 4.

Definition is_c6_poset (a : list (option bool)) : bool :=
  is_poset_b (mat_of a) && Nat.eqb (edge_count_b (mat_of a)) 6.

Definition count6_canons : list (list nat) :=
  nodup (list_eq_dec Nat.eq_dec)
        (map (fun a => canon (mat_of a))
             (filter is_c6_poset count6_assigns)).

(* Decode an edge code n = 5*i+j into the pair (i, j). *)
Definition decode (n : nat) : nat * nat := (Nat.div n 5, Nat.modulo n 5).
Definition count6_shapes : list (list (nat * nat)) :=
  map (map decode) count6_canons.

Eval vm_compute in (List.length count6_canons).
Eval vm_compute in count6_shapes.

(* ---- search a valid 2-realizer (L1,L2 rank vectors) per canonical pattern ---- *)
Definition fin_of_nat (n : nat) : Fin.t 5 := nth n all5 f0.
Definition mat_of_codes (codes : list nat) : M5 :=
  from_edges (map (fun n => (fin_of_nat (Nat.div n 5), fin_of_nat (Nat.modulo n 5))) codes).

Fixpoint idx_of (x : Fin.t 5) (l : list (Fin.t 5)) (acc : nat) : nat :=
  match l with
  | [] => 0
  | y :: l' => if fin5_eqb x y then acc else idx_of x l' (S acc)
  end.
Definition rkvec (perm : list (Fin.t 5)) : list nat :=
  map (fun x => idx_of x perm 0) all5.

Definition is_LE (M : M5) (perm : list (Fin.t 5)) : bool :=
  forallb (fun p => if strict_b M (fst p) (snd p)
                    then Nat.ltb (idx_of (fst p) perm 0) (idx_of (snd p) perm 0)
                    else true) all_pairs.
Definition incomp_pairs (M : M5) : list (Fin.t 5 * Fin.t 5) :=
  filter (fun p => andb (negb (fin5_eqb (fst p) (snd p)))
                        (andb (negb (M (fst p) (snd p))) (negb (M (snd p) (fst p)))))
         all_pairs.
Definition reverses (M : M5) (p1 p2 : list (Fin.t 5)) : bool :=
  forallb (fun pr => negb (Bool.eqb
              (Nat.ltb (idx_of (fst pr) p1 0) (idx_of (snd pr) p1 0))
              (Nat.ltb (idx_of (fst pr) p2 0) (idx_of (snd pr) p2 0))))
          (incomp_pairs M).
Definition find_realizer (M : M5) : option (list nat * list nat) :=
  let les := filter (is_LE M) all_perms5 in
  fold_left (fun acc p1 =>
    match acc with
    | Some _ => acc
    | None => fold_left (fun acc2 p2 =>
                match acc2 with
                | Some _ => acc2
                | None => if reverses M p1 p2 then Some (rkvec p1, rkvec p2) else None
                end) les None
    end) les None.

Eval vm_compute in (map (fun codes => find_realizer (mat_of_codes codes)) count6_canons).
