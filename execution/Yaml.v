(* YAML I/O: datatypes, printer, model bridges *)

From Stdlib Require Import String Ascii List Arith Lia.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts Relation_Operators Operators_Properties.
From Posets Require Import PosetClasses.
From Dimension Require Import Theorems.
Import ListNotations.
Open Scope string_scope.

Record YamlExecution := { ye_nprocs : nat; ye_syncs : list (nat * nat) }.
Record YamlPoset := { yp_nverts : nat; yp_edges : list (nat * nat) }.

Inductive Document :=
  | DocExecution (e : YamlExecution)
  | DocPoset (p : YamlPoset).

Definition wf_yaml_execution (e : YamlExecution) : Prop :=
  0 < ye_nprocs e /\
  (forall a b, List.In (a, b) (ye_syncs e) -> a < ye_nprocs e /\ b < ye_nprocs e /\ a <> b).

(* one decimal digit (0..9) as a Char *)
Definition digit_char (n : nat) : ascii := ascii_of_nat (48 + n).

(* string_of_nat via fuel; no leading zeros; string_of_nat 0 = "0" *)
Fixpoint string_of_nat_aux (fuel n : nat) (acc : string) : string :=
  let acc' := String (digit_char (Nat.modulo n 10)) acc in
  match fuel with
  | 0 => acc'
  | S f => match Nat.div n 10 with
           | 0 => acc'
           | q => string_of_nat_aux f q acc'
           end
  end.

Definition string_of_nat (n : nat) : string := string_of_nat_aux n n "".

Definition nl : string := String (ascii_of_nat 10) "".

Definition pair_line (xy : nat * nat) : string :=
  "    - [" ++ string_of_nat (fst xy) ++ ", " ++ string_of_nat (snd xy) ++ "]" ++ nl.

Definition dump_execution (e : YamlExecution) : string :=
  "execution:" ++ nl ++
  "  n_procs: " ++ string_of_nat (ye_nprocs e) ++ nl ++
  "  syncs:" ++ nl ++
  String.concat "" (map pair_line (ye_syncs e)).

Definition dump_poset (p : YamlPoset) : string :=
  "poset:" ++ nl ++
  "  n_vertices: " ++ string_of_nat (yp_nverts p) ++ nl ++
  "  edges:" ++ nl ++
  String.concat "" (map pair_line (yp_edges p)).

Definition dump (d : Document) : string :=
  match d with DocExecution e => dump_execution e | DocPoset p => dump_poset p end.

(* ------------------------------------------------------------------ *)
(* YAML execution -> Schedule bridge                                    *)
(* ------------------------------------------------------------------ *)

From Execution Require Import Schedule.

Definition schedule_of_yaml (e : YamlExecution) : Schedule :=
  {| sch_nprocs := ye_nprocs e;
     sch_frontiers := map (fun s => [s]) (ye_syncs e) |}.

Lemma schedule_of_yaml_nprocs :
  forall e, sch_nprocs (schedule_of_yaml e) = ye_nprocs e.
Proof. intro e. reflexivity. Qed.

Lemma schedule_of_yaml_nfrontiers :
  forall e, length (sch_frontiers (schedule_of_yaml e)) = length (ye_syncs e).
Proof. intro e. simpl. rewrite length_map. reflexivity. Qed.

(* ---- YAML poset -> finite poset bridge ---- *)

Definition wf_yaml_poset (p : YamlPoset) : Prop :=
  (forall a b, List.In (a, b) (yp_edges p) -> a < yp_nverts p /\ b < yp_nverts p) /\
  (exists rank : nat -> nat,
     forall a b, List.In (a, b) (yp_edges p) -> rank a < rank b).

Definition Vert (p : YamlPoset) : Type := { n : nat | n < yp_nverts p }.

Definition yaml_edge (p : YamlPoset) (x y : Vert p) : Prop :=
  List.In (proj1_sig x, proj1_sig y) (yp_edges p).

Definition yaml_order (p : YamlPoset) : Vert p -> Vert p -> Prop :=
  clos_refl_trans (Vert p) (yaml_edge p).

(* finiteness of the carrier *)
Lemma cardinal_lt_n : forall N : nat, cardinal nat (fun n => n < N) N.
Proof.
  induction N as [|N IH].
  - assert (Heq : (fun n => n < 0) = Empty_set nat).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. unfold Ensembles.In in Hx. lia.
      - intros x Hx. destruct Hx. }
    rewrite Heq. apply card_empty.
  - assert (Heq : (fun n => n < S N) = Add nat (fun n => n < N) N).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. unfold Ensembles.In in Hx.
        destruct (Nat.eq_dec x N) as [He|Hne].
        + right. rewrite He. apply In_singleton.
        + left. unfold Ensembles.In. lia.
      - intros x Hx. destruct Hx as [x Hxl | x Hxs].
        + unfold Ensembles.In in *. lia.
        + inversion Hxs. unfold Ensembles.In. lia. }
    rewrite Heq. apply card_add.
    + exact IH.
    + unfold Ensembles.In. lia.
Qed.

Lemma yaml_vert_finite : forall p, Finite (Vert p) (Full_set (Vert p)).
Proof.
  intro p.
  apply (cardinal_finite (Vert p) (Full_set (Vert p)) (yp_nverts p)).
  exact (cardinal_subtype_full nat (fun n => n < yp_nverts p) (yp_nverts p)
           (cardinal_lt_n (yp_nverts p))).
Qed.

(* antisymmetry via the strict-rank witness, mirroring Rank.v *)
Lemma yaml_order_eq_or_rank_lt :
  forall p (rank : nat -> nat),
    (forall a b, List.In (a, b) (yp_edges p) -> rank a < rank b) ->
    forall x y : Vert p, yaml_order p x y ->
      x = y \/ rank (proj1_sig x) < rank (proj1_sig y).
Proof.
  intros p rank Hrank x y H.
  induction H as [x y Hedge | x | x y z Hxy IHxy Hyz IHyz].
  - right. apply Hrank. exact Hedge.
  - left. reflexivity.
  - destruct IHxy as [He1|Hl1]; destruct IHyz as [He2|Hl2].
    + left. subst. reflexivity.
    + right. subst. exact Hl2.
    + right. subst. exact Hl1.
    + right. lia.
Qed.

Lemma yaml_order_IsPoset : forall p, wf_yaml_poset p -> IsPoset (Vert p) (yaml_order p).
Proof.
  intros p [Hrange [rank Hrank]].
  constructor.
  - (* refl *) intro x. apply rt_refl.
  - (* antisym *) intros x y Hxy Hyx.
    destruct (yaml_order_eq_or_rank_lt p rank Hrank x y Hxy) as [He|Hl].
    + exact He.
    + destruct (yaml_order_eq_or_rank_lt p rank Hrank y x Hyx) as [He2|Hl2].
      * symmetry. exact He2.
      * exfalso. lia.
  - (* trans *) intros x y z Hxy Hyz. eapply rt_trans; eauto.
Qed.
