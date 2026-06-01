(* Transformation A: synchronization-square contraction as dimension-preserving
   block replacement, plus the concrete square / contracted chain blocks. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge Ordinal
                              FullySync FullySyncDimExact
                              FinExtremumDimExamples ChainDim.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* ------------------------------------------------------------------ *)
(* Part 1 — dimension preservation under block replacement            *)
(* ------------------------------------------------------------------ *)

Lemma transform_preserves_dimension :
  forall E blocks dims E' blocks' dims',
    IsFullySync E blocks -> length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    IsFullySync E' blocks' -> length dims' = length blocks' ->
    (forall i, i < length blocks' ->
       PosetDimension (sub_order E' (nth i blocks' (Empty_set _))) (nth i dims' 0)) ->
    (exists a b : ep_carrier E', a <> b) ->
    fold_right Nat.max 0 dims = fold_right Nat.max 0 dims' ->
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
Proof.
  intros E blocks dims E' blocks' dims' Hfs Hld Hd Hge2 Hfs' Hld' Hd' Hge2' Hfold dW dW' HdW HdW'.
  pose proof (fully_sync_dimension E blocks dims Hfs Hld Hd Hge2 dW HdW) as HE.
  pose proof (fully_sync_dimension E' blocks' dims' Hfs' Hld' Hd' Hge2' dW' HdW') as HE'.
  rewrite HE, HE', Hfold. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 2 — the concrete chain blocks                                 *)
(* ------------------------------------------------------------------ *)

(* B_contracted: 2 synchronized points = the 2-element chain (reuse chain2_R). *)
Definition B_contracted_R : bool -> bool -> Prop := chain2_R.

Lemma B_contracted_dim_1 : PosetDimension B_contracted_R 1.
Proof.
  apply (chain_dim_1 B_contracted_R chain2_Hfin).
  - exact chain2_total.
  - exists false, true. exact (fun H => true_neq_false (eq_sym H)).
Qed.

(* B_square: the 4-event synchronization square = a 4-element chain. *)
Definition Sq : Type := { n : nat | n < 4 }.
Definition B_square_R (x y : Sq) : Prop := proj1_sig x <= proj1_sig y.

#[local] Instance B_square_poset : IsPoset Sq B_square_R.
Proof.
  constructor.
  - (* reflexivity *)
    intro x. unfold B_square_R. apply Nat.le_refl.
  - (* antisymmetry *)
    intros x y Hxy Hyx. unfold B_square_R in *.
    assert (Heq : proj1_sig x = proj1_sig y) by (apply Nat.le_antisymm; assumption).
    destruct x as [m Hm]. destruct y as [k Hk]. simpl in Heq. subst k.
    f_equal. apply proof_irrelevance.
  - (* transitivity *)
    intros x y z Hxy Hyz. unfold B_square_R in *.
    apply (Nat.le_trans _ _ _ Hxy Hyz).
Qed.

(* cardinal of a NoDup list, as an ensemble of [nat]. *)
Lemma cardinal_of_NoDup_nat :
  forall (l : list nat),
    NoDup l ->
    cardinal nat (fun x => List.In x l) (length l).
Proof.
  intros l Hnd.
  induction Hnd as [|a l' Hnotin Hnd' IH].
  - assert (Heq : (fun x => List.In x (@nil nat)) = Empty_set nat).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. destruct Hx.
      - intros x Hx. destruct Hx. }
    rewrite Heq. simpl. apply card_empty.
  - assert (Heq : (fun x => List.In x (a :: l')) =
                  Ensembles.Add nat (fun x => List.In x l') a).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. simpl in Hx. destruct Hx as [Hax | Hxl].
        + right. rewrite Hax. apply In_singleton.
        + left. exact Hxl.
      - intros x Hx. destruct Hx as [x Hxl | x Hxs].
        + simpl. right. exact Hxl.
        + inversion Hxs. simpl. left. reflexivity. }
    rewrite Heq. simpl (length _).
    apply card_add; [ exact IH | exact Hnotin ].
Qed.

Lemma B_square_Hfin : Finite Sq (Full_set Sq).
Proof.
  (* cardinal nat (fun n => n < 4) 4, exhibiting the list [0;1;2;3]. *)
  assert (Hcardnat : cardinal nat (fun n => n < 4) 4).
  { assert (Heq : (fun n => n < 4) = (fun x => List.In x [0;1;2;3])).
    { apply Extensionality_Ensembles. split.
      - intros x Hx. unfold Ensembles.In in *.
        assert (Hc : x = 0 \/ x = 1 \/ x = 2 \/ x = 3) by lia.
        destruct Hc as [Hc|[Hc|[Hc|Hc]]]; subst; simpl;
          [ left | right; left | right; right; left
          | right; right; right; left ]; reflexivity.
      - intros x Hx. unfold Ensembles.In in *. simpl in Hx.
        destruct Hx as [H|[H|[H|[H|H]]]]; subst; try lia. }
    rewrite Heq.
    change 4 with (length [0;1;2;3]).
    apply cardinal_of_NoDup_nat.
    repeat apply NoDup_cons;
      try (simpl; intro Hbad;
           repeat (destruct Hbad as [Hbad | Hbad]; [ discriminate Hbad | ]); exact Hbad);
      apply NoDup_nil. }
  pose proof (cardinal_subtype_full nat (fun n => n < 4) 4 Hcardnat) as Hsub.
  (* {x : nat | In nat (fun n => n < 4) x} is definitionally Sq. *)
  apply (cardinal_finite Sq (Full_set Sq) 4).
  exact Hsub.
Qed.

Lemma B_square_dim_1 : PosetDimension B_square_R 1.
Proof.
  apply (chain_dim_1 B_square_R B_square_Hfin).
  - (* totality *)
    intros x y. unfold B_square_R.
    destruct (Nat.le_ge_cases (proj1_sig x) (proj1_sig y)) as [H | H].
    + left. exact H.
    + right. exact H.
  - (* two distinct elements *)
    assert (H0 : 0 < 4) by lia.
    assert (H1 : 1 < 4) by lia.
    exists (exist _ 0 H0), (exist _ 1 H1).
    intro H. assert (Hp : proj1_sig (exist (fun n => n < 4) 0 H0)
                        = proj1_sig (exist (fun n => n < 4) 1 H1))
      by (rewrite H; reflexivity).
    simpl in Hp. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 3 — Transformation A preserves whole-execution dimension      *)
(* ------------------------------------------------------------------ *)

Lemma transform_A_preserves :
  forall E blocks dims E' blocks' dims',
    IsFullySync E blocks -> length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (sub_order E (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : ep_carrier E, a <> b) ->
    IsFullySync E' blocks' -> length dims' = length blocks' ->
    (forall i, i < length blocks' ->
       PosetDimension (sub_order E' (nth i blocks' (Empty_set _))) (nth i dims' 0)) ->
    (exists a b : ep_carrier E', a <> b) ->
    dims = dims' ->
    forall dW dW', PosetDimension (ep_order E) dW -> PosetDimension (ep_order E') dW' ->
      dW = dW'.
Proof.
  intros E blocks dims E' blocks' dims' Hfs Hld Hd Hge2 Hfs' Hld' Hd' Hge2' Hdimseq dW dW' HdW HdW'.
  apply (transform_preserves_dimension E blocks dims E' blocks' dims'
           Hfs Hld Hd Hge2 Hfs' Hld' Hd' Hge2'
           (f_equal (fold_right Nat.max 0) Hdimseq) dW dW' HdW HdW').
Qed.
