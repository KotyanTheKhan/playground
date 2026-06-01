(* execution dimension bridge — DimCriticalPairs (layer 2a) *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset.
From Execution Require Import DimBridge.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

Definition exec_critical_pair (E : ExecPoset) (x y : ep_carrier E) : Prop :=
  IsCriticalPair (ep_order E) x y.

(* Every incomparable pair of an execution contains a critical pair. *)
Lemma exec_incomparable_has_critical_pair :
  forall E (x y : ep_carrier E),
    Incomparable (ep_order E) x y ->
    exists x' y',
      ep_order E x' x /\ ep_order E y y' /\ exec_critical_pair E x' y'.
Proof.
  intros E x y Hinc.
  unfold exec_critical_pair, ep_carrier, ep_order in *.
  pose (Hfin := cardinal_finite (Event (ep_ranked E))
                  (Full_set (Event (ep_ranked E))) (ep_size E) (ep_size_ok E)).
  apply (incomparable_lifting_to_critical_pair
           (hb (ep_ranked E)) Hfin x y Hinc).
Qed.

(* Reversibility characterization, specialized to executions.
   NOTE the HS hypothesis: S must consist of critical pairs (required by the library). *)
Lemma exec_critical_pairs_reversible_iff_no_alt_cycle :
  forall E (S : Ensemble (ep_carrier E * ep_carrier E)),
    (forall p, Ensembles.In _ S p -> exec_critical_pair E (fst p) (snd p)) ->
    ((exists L, IsLinearExtension (ep_order E) L /\
                forall x y, Ensembles.In _ S (x, y) -> L y x)
     <->
     ~ (exists cycle,
          (forall p, List.In p cycle -> Ensembles.In _ S p)
          /\ IsAlternatingCycle (ep_order E) cycle)).
Proof.
  intros E S HS.
  unfold exec_critical_pair, ep_carrier, ep_order in *.
  apply (critical_pairs_reversible_iff_no_alternating_cycle
           (hb (ep_ranked E)) S HS).
Qed.

(* Helper: a two-element (or one-element) realizer has cardinal <= 2. *)
Lemma exec_two_extension_realizer_card :
  forall E (L1 L : ep_carrier E -> ep_carrier E -> Prop),
    exists n,
      cardinal _ (fun K => K = L1 \/ K = L) n /\ n <= 2.
Proof.
  intros E L1 L.
  destruct (classic (L1 = L)) as [Heq | Hneq].
  - (* single element: { K | K = L1 } *)
    exists 1. split; [| lia].
    assert (Hset : (fun K : ep_carrier E -> ep_carrier E -> Prop => K = L1 \/ K = L)
                   = Ensembles.Add _ (Empty_set _) L1).
    { apply Extensionality_Ensembles. split.
      - intros K HK. destruct HK as [-> | ->]; [right; constructor | rewrite <- Heq; right; constructor].
      - intros K HK. destruct HK as [K HK | K HK].
        + inversion HK.
        + destruct HK. left; reflexivity. }
    rewrite Hset.
    apply card_add.
    + apply card_empty.
    + intro Hin. inversion Hin.
  - (* two distinct elements: { K | K = L1 \/ K = L } *)
    exists 2. split; [| lia].
    assert (Hset : (fun K : ep_carrier E -> ep_carrier E -> Prop => K = L1 \/ K = L)
                   = Ensembles.Add _ (Ensembles.Add _ (Empty_set _) L1) L).
    { apply Extensionality_Ensembles. split.
      - intros K HK. destruct HK as [-> | ->].
        + left; right; constructor.
        + right; constructor.
      - intros K HK. destruct HK as [K HK | K HK].
        + destruct HK as [K HK | K HK].
          * inversion HK.
          * destruct HK. left; reflexivity.
        + destruct HK. right; reflexivity. }
    rewrite Hset.
    apply card_add.
    + apply card_add.
      * apply card_empty.
      * intro Hin. inversion Hin.
    + intro Hin.
      destruct Hin as [K Hin | K Hin].
      * inversion Hin.
      * destruct Hin. apply Hneq. reflexivity.
Qed.

(* No alternating cycle of critical pairs  =>  dimension <= 2.
   CAUTION — the hypothesis is STRICTLY STRONGER than [dim <= 2]: it means a single
   linear extension reverses every critical pair, and it FAILS for any poset
   containing an antichain (e.g. the 2-element antichain), so it is rarely usable
   for genuinely 2-dimensional posets. The converse [dim <= 2 -> no alt cycle] is
   FALSE. For a usable [dim <= 2] lever see [barrier_dim_le2] (BarrierDim2.v) and
   the exact-dimension results. See the full caution on [no_alt_cycle] in
   Ordinal.v. *)
Lemma exec_dim_le_2_of_no_alt_cycle :
  forall E,
    ~ (exists cycle,
         (forall p, List.In p cycle -> exec_critical_pair E (fst p) (snd p))
         /\ IsAlternatingCycle (ep_order E) cycle) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof.
  intros E Hno.
  (* The ensemble of all critical pairs. *)
  pose (S_cp := fun p : ep_carrier E * ep_carrier E =>
                  exec_critical_pair E (fst p) (snd p)).
  assert (HS : forall p, Ensembles.In _ S_cp p ->
                         exec_critical_pair E (fst p) (snd p)).
  { intros p Hp. exact Hp. }
  (* Reversibility characterization. *)
  pose proof (exec_critical_pairs_reversible_iff_no_alt_cycle E S_cp HS) as Hiff.
  (* The RHS of Hiff is exactly Hno. *)
  assert (Hrev_exists : exists L, IsLinearExtension (ep_order E) L /\
                        forall x y, Ensembles.In _ S_cp (x, y) -> L y x).
  { apply Hiff.
    intro Hcyc. apply Hno.
    destruct Hcyc as [cycle [Hcyc_in Hcyc_alt]].
    exists cycle. split; [| exact Hcyc_alt].
    intros p Hp. exact (Hcyc_in p Hp). }
  destruct Hrev_exists as [L [HLlin HLrev]].
  (* L reverses every critical pair. *)
  assert (HLrev_cp : forall x y, IsCriticalPair (ep_order E) x y -> L y x).
  { intros x y Hcp. apply (HLrev x y). exact Hcp. }
  (* Second linear extension. *)
  destruct (at_least_one_linear_extension (ep_order E)) as [L1 HL1lin].
  (* The realizer. *)
  pose (realizer := fun K : ep_carrier E -> ep_carrier E -> Prop =>
                      K = L1 \/ K = L).
  assert (Hinh : Ensembles.Inhabited _ realizer).
  { exists L1. left. reflexivity. }
  assert (Hmem : forall K, Ensembles.In _ realizer K ->
                           IsLinearExtension (ep_order E) K).
  { intros K HK. destruct HK as [-> | ->]; assumption. }
  (* Finiteness of the carrier. *)
  pose (Hfin := cardinal_finite (ep_carrier E) (Full_set _)
                  (ep_size E) (ep_size_ok E)).
  (* realizer is a realizer. *)
  assert (Hreal : IsRealizer (ep_order E) realizer).
  { apply (critical_pair_realizer_iff (ep_order E) Hfin realizer Hinh Hmem).
    intros x y Hcp.
    exists L. split.
    - right. reflexivity.
    - apply HLrev_cp. exact Hcp. }
  (* Cardinal of the realizer. *)
  destruct (exec_two_extension_realizer_card E L1 L) as [n [Hcard Hle2]].
  fold realizer in Hcard.
  (* Dimension bound. *)
  destruct (exec_dimension_exists E) as [d [Hd]].
  pose proof (dimension_is_minimum Hd realizer n Hreal Hcard) as Hle.
  exists d. split.
  - constructor. exact Hd.
  - lia.
Qed.
