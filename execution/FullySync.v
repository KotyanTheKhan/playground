(* iterated fully-synchronized decomposition of executions *)

From Stdlib Require Import Ensembles Finite_sets List Arith Lia Classical ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs CriticalPairs Theorems.
From Execution Require Import Op Event Edges Rank Poset DimBridge DimCriticalPairs Frontier Ordinal.
Import ListNotations.

#[local] Existing Instance hb_IsPoset.
#[local] Existing Instance hb_IsFinitePoset.

(* The union of the first [k] blocks (indices [0 .. k-1]). *)
Definition union_upto (E : ExecPoset) (blocks : list (Ensemble (ep_carrier E))) (k : nat)
  : Ensemble (ep_carrier E) :=
  fun x => exists i, i < k /\ Ensembles.In _ (nth i blocks (Empty_set _)) x.

(* A fully-synchronized decomposition: the blocks are nonempty, cover the
   carrier, are pairwise disjoint, and every proper prefix union is a barrier. *)
Definition IsFullySync (E : ExecPoset) (blocks : list (Ensemble (ep_carrier E))) : Prop :=
  (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\
  (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\
  (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
     Ensembles.In _ (nth i blocks (Empty_set _)) x ->
     ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\
  (forall k, 0 < k -> k < length blocks ->
     IsBarrier E (union_upto E blocks k)
                 (fun x => ~ Ensembles.In _ (union_upto E blocks k) x)).

Section FullySync.
  Context (E : ExecPoset) (blocks : list (Ensemble (ep_carrier E))).
  Hypothesis Hfs : IsFullySync E blocks.

  (* Convenient accessors for the four conjuncts. *)
  Let Hne : forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x.
  Proof. apply Hfs. Defined.
  Let Hcover : forall x, exists i, i < length blocks /\
                 Ensembles.In _ (nth i blocks (Empty_set _)) x.
  Proof. apply Hfs. Defined.
  Let Hdisj : forall i j x, i < length blocks -> j < length blocks -> i <> j ->
                Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                ~ Ensembles.In _ (nth j blocks (Empty_set _)) x.
  Proof. apply Hfs. Defined.
  Let Hbar : forall k, 0 < k -> k < length blocks ->
               IsBarrier E (union_upto E blocks k)
                           (fun x => ~ Ensembles.In _ (union_upto E blocks k) x).
  Proof. apply Hfs. Defined.

  (* An element at index [i] is in [union_upto k] iff [i < k]
     (given that [i] is the unique index containing it). *)
  Lemma in_union_upto_intro :
    forall i x k, i < k -> Ensembles.In _ (nth i blocks (Empty_set _)) x ->
      Ensembles.In _ (union_upto E blocks k) x.
  Proof. intros i x k Hik Hxi. exists i. split; assumption. Qed.

  (* If [x] is at index [i] (with [i] valid), and [x ∈ union_upto k],
     then [i < k] — using disjointness. *)
  Lemma in_union_upto_index :
    forall i x k, i < length blocks ->
      Ensembles.In _ (nth i blocks (Empty_set _)) x ->
      Ensembles.In _ (union_upto E blocks k) x -> i < k.
  Proof.
    intros i x k Hi Hxi [j [Hjk Hxj]].
    (* j is a valid index because nth j .. x holds and default is empty. *)
    assert (Hjlen : j < length blocks).
    { destruct (Nat.lt_ge_cases j (length blocks)) as [? | Hge]; [assumption |].
      rewrite nth_overflow in Hxj by lia. inversion Hxj. }
    destruct (Nat.eq_dec i j) as [-> | Hne'].
    - exact Hjk.
    - exfalso. exact (Hdisj i j x Hi Hjlen Hne' Hxi Hxj).
  Qed.

  (* Block index is monotone along the execution order. *)
  Lemma fullysync_block_monotone :
    forall i j x y, i < length blocks -> j < length blocks ->
      Ensembles.In _ (nth i blocks (Empty_set _)) x ->
      Ensembles.In _ (nth j blocks (Empty_set _)) y ->
      ep_order E x y -> i <= j.
  Proof.
    intros i j x y Hi Hj Hxi Hyj Hxy.
    destruct (Nat.le_gt_cases i j) as [Hle | Hgt]; [exact Hle | exfalso].
    (* i > j; take k := i (so 0 < i since j >= 0 < i, and i < length). *)
    assert (Hk0 : 0 < i) by lia.
    pose proof (Hbar i Hk0 Hi) as HB.
    (* y ∈ union_upto i (because j < i). *)
    assert (HyL : Ensembles.In _ (union_upto E blocks i) y).
    { apply (in_union_upto_intro j y i); [lia | assumption]. }
    (* x ∉ union_upto i (x is at index i, not < i, by disjointness). *)
    assert (HxU : ~ Ensembles.In _ (union_upto E blocks i) x).
    { intro Hin. pose proof (in_union_upto_index i x i Hi Hxi Hin). lia. }
    (* Barrier: x in U-side, y in L-side; upper-disjoint-below ⟹ ~ ep_order E x y. *)
    exact (barrier_upper_disjoint_below E _ _ HB x y HxU HyL Hxy).
  Qed.

  (* Each element has a unique block index. *)
  Lemma block_index_unique :
    forall i j x, i < length blocks -> j < length blocks ->
      Ensembles.In _ (nth i blocks (Empty_set _)) x ->
      Ensembles.In _ (nth j blocks (Empty_set _)) x -> i = j.
  Proof.
    intros i j x Hi Hj Hxi Hxj.
    destruct (Nat.eq_dec i j) as [Heq | Hne']; [exact Heq |].
    exfalso. exact (Hdisj i j x Hi Hj Hne' Hxi Hxj).
  Qed.

  (* A critical pair has both endpoints in the same block index. *)
  Lemma fullysync_crit_same_block :
    forall x y i j, i < length blocks -> j < length blocks ->
      Ensembles.In _ (nth i blocks (Empty_set _)) x ->
      Ensembles.In _ (nth j blocks (Empty_set _)) y ->
      IsCriticalPair (ep_order E) x y -> i = j.
  Proof.
    intros x y i j Hi Hj Hxi Hyj Hcp.
    assert (Hinc : Incomparable (ep_order E) x y) by exact Hcp.(critical_incomparable).
    destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
    - (* i < j: barrier at k := j puts x (idx i<j) in L, y (idx j) in U;
         Hbelow gives ep_order E x y, contradicting incomparability. *)
      exfalso.
      assert (Hk0 : 0 < j) by lia.
      pose proof (Hbar j Hk0 Hj) as HB.
      destruct HB as [_ [_ [_ [_ Hbelow]]]].
      assert (HxL : Ensembles.In _ (union_upto E blocks j) x).
      { apply (in_union_upto_intro i x j); [lia | assumption]. }
      assert (HyU : ~ Ensembles.In _ (union_upto E blocks j) y).
      { intro Hin. pose proof (in_union_upto_index j y j Hj Hyj Hin). lia. }
      apply Hinc. left. apply Hbelow; assumption.
    - (* j < i: symmetric, gives ep_order E y x. *)
      exfalso.
      assert (Hk0 : 0 < i) by lia.
      pose proof (Hbar i Hk0 Hi) as HB.
      destruct HB as [_ [_ [_ [_ Hbelow]]]].
      assert (HyL : Ensembles.In _ (union_upto E blocks i) y).
      { apply (in_union_upto_intro j y i); [lia | assumption]. }
      assert (HxU : ~ Ensembles.In _ (union_upto E blocks i) x).
      { intro Hin. pose proof (in_union_upto_index i x i Hi Hxi Hin). lia. }
      apply Hinc. right. apply Hbelow; assumption.
  Qed.

  (* For a pair [p] whose endpoints are critical, the common block index. *)
  (* We work via the cover to extract indices and use the uniqueness/same-block
     lemmas. A helper extracting the chain of relations from a cycle follows. *)

  (* The relations packaged by [check_alternating_cycle]:
     for the cycle [(x0,y0)::rest], with [check_alternating_cycle x0 y0 rest],
     we get [ep_order E x_{m+1} y_m] for consecutive entries and the wrap
     [ep_order E x0 y_last]. The following two helpers extract exactly the
     monotonicity facts we need, threaded through block indices. *)

  (* Block index of an element (as a relation), used to phrase monotonicity. *)
  Definition at_index (i : nat) (x : ep_carrier E) : Prop :=
    i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x.

  Lemma at_index_exists : forall x, exists i, at_index i x.
  Proof. intro x. destruct (Hcover x) as [i [Hi Hin]]. exists i. split; assumption. Qed.

  Lemma at_index_functional :
    forall i j x, at_index i x -> at_index j x -> i = j.
  Proof.
    intros i j x [Hi Hxi] [Hj Hxj]. exact (block_index_unique i j x Hi Hj Hxi Hxj).
  Qed.

  (* check_alternating_cycle, when all pairs are critical and live at indices,
     forces all indices to be equal to the index of [first_x] paired with
     [last_y]. We prove a stronger statement by induction on [rest]. *)

  (* If [ep_order E a b] with [a] at index [ia], [b] at index [ib], then ia <= ib. *)
  Lemma order_index_mono :
    forall a b ia ib, at_index ia a -> at_index ib b -> ep_order E a b -> ia <= ib.
  Proof.
    intros a b ia ib [Hia Ha] [Hib Hb] Hab.
    exact (fullysync_block_monotone ia ib a b Hia Hib Ha Hb Hab).
  Qed.

  (* The core induction: given check_alternating_cycle first_x last_y rest,
     where every pair in [rest] is critical (both endpoints same index), and
     [first_x] is at index [ifx], [last_y] is at index [ily], we conclude that
     for every pair (xi,yi) in rest its common index [k] satisfies
     ily <= k  and  ifx <= (index linking down) ...
     To keep bookkeeping simple we prove: the index of [first_x] is <= the
     index of [last_y], threading the chain. This is the wrap-around closure
     [ep_order E x0 y_last] applied with monotonicity composition. *)

  (* Helper giving: for a cycle, the index of every element appearing as a
     [fst] or [snd] equals a single common value. We prove it by showing
     the index of [first_x] >= index of every element >= index of [first_x]. *)

  (* Chain lemma: check_alternating_cycle first_x last_y rest with all pairs
     critical implies index(first_x) <= index(last_y), AND every pair's index
     lies between index(last_y) and index(first_x). Phrased as: the index of
     last_y is <= index of every pair's index, and each pair's index <= index
     of first_x.  Then closing relation reverses, forcing equality. *)

  Lemma cycle_chain_bounds :
    forall rest first_x last_y ifx ily,
      at_index ifx first_x -> at_index ily last_y ->
      (forall p, List.In p rest -> IsCriticalPair (ep_order E) (fst p) (snd p)) ->
      check_alternating_cycle (ep_order E) first_x last_y rest ->
      (* the terminal relation gives ifx <= ily, and every pair index k in
         rest is sandwiched ifx <= k <= ily. *)
      ifx <= ily /\
      (forall p, List.In p rest ->
         forall k, at_index k (fst p) -> ifx <= k <= ily).
  Proof.
    induction rest as [| q rest IH]; intros first_x last_y ifx ily Hifx Hily Hcrit Hchk.
    - (* nil: check = ep_order E first_x last_y. *)
      simpl in Hchk.
      split.
      + exact (order_index_mono first_x last_y ifx ily Hifx Hily Hchk).
      + intros p Hp. inversion Hp.
    - (* q = (xq, yq); Hchk : ep_order E xq last_y /\ check_alternating_cycle first_x yq rest *)
      destruct q as [xq yq]. simpl in Hchk. destruct Hchk as [Hqlast Hrest].
      (* index of xq, yq: equal (critical pair, by same-block). *)
      assert (Hq_crit : IsCriticalPair (ep_order E) xq yq).
      { exact (Hcrit (xq, yq) (or_introl eq_refl)). }
      destruct (at_index_exists xq) as [ixq Hixq].
      destruct (at_index_exists yq) as [iyq Hiyq].
      assert (Hixy : ixq = iyq).
      { destruct Hixq as [Hixq1 Hixq2]; destruct Hiyq as [Hiyq1 Hiyq2].
        exact (fullysync_crit_same_block xq yq ixq iyq Hixq1 Hiyq1 Hixq2 Hiyq2 Hq_crit). }
      (* ep_order E xq last_y : ixq <= ily. *)
      assert (Hxq_le_ily : ixq <= ily).
      { exact (order_index_mono xq last_y ixq ily Hixq Hily Hqlast). }
      (* Apply IH with last_y := yq (index iyq). *)
      assert (Hcrit_rest : forall p, List.In p rest ->
                IsCriticalPair (ep_order E) (fst p) (snd p)).
      { intros p Hp. apply Hcrit. right. exact Hp. }
      destruct (IH first_x yq ifx iyq Hifx Hiyq Hcrit_rest Hrest)
        as [Hifx_le_iyq Hbounds].
      (* ifx <= iyq = ixq <= ily.  So ifx <= ily. *)
      assert (Hifx_le_ily : ifx <= ily) by lia.
      split; [exact Hifx_le_ily |].
      intros p Hp k Hk.
      destruct Hp as [Heqp | Hp].
      + (* p = (xq, yq); k = index(fst p) = index(xq) = ixq. *)
        subst p. simpl in Hk.
        assert (Hk_eq : k = ixq) by exact (at_index_functional k ixq xq Hk Hixq).
        subst k. lia.
      + (* p in rest: bounds from IH give iyq <= k <= ifx; combine. *)
        destruct (Hbounds p Hp k Hk) as [Hlo Hhi].
        lia.
  Qed.

  (* The whole alternating cycle lives in a single block. *)
  Lemma alt_cycle_in_one_block :
    forall cyc,
      (forall p, List.In p cyc -> IsCriticalPair (ep_order E) (fst p) (snd p)) ->
      IsAlternatingCycle (ep_order E) cyc ->
      exists i, i < length blocks /\
        (forall p, List.In p cyc ->
           Ensembles.In _ (nth i blocks (Empty_set _)) (fst p) /\
           Ensembles.In _ (nth i blocks (Empty_set _)) (snd p)).
  Proof.
    intros cyc Hcrit Halt.
    destruct cyc as [| q rest] eqn:Ecyc.
    - (* empty cycle: IsAlternatingCycle is False. *)
      simpl in Halt. contradiction.
    - destruct q as [x0 y0].
      simpl in Halt. destruct Halt as [_ Hchk].
      (* Indices of x0, y0: equal (critical pair). *)
      assert (Hq_crit : IsCriticalPair (ep_order E) x0 y0).
      { exact (Hcrit (x0, y0) (or_introl eq_refl)). }
      destruct (at_index_exists x0) as [ix0 Hix0].
      destruct (at_index_exists y0) as [iy0 Hiy0].
      assert (Hxy0 : ix0 = iy0).
      { destruct Hix0 as [Hix01 Hix02]; destruct Hiy0 as [Hiy01 Hiy02].
        exact (fullysync_crit_same_block x0 y0 ix0 iy0 Hix01 Hiy01 Hix02 Hiy02 Hq_crit). }
      (* check_alternating_cycle x0 y0 rest with first_x = x0 (ix0), last_y = y0 (iy0). *)
      assert (Hcrit_rest : forall p, List.In p rest ->
                IsCriticalPair (ep_order E) (fst p) (snd p)).
      { intros p Hp. apply Hcrit. right. exact Hp. }
      destruct (cycle_chain_bounds rest x0 y0 ix0 iy0 Hix0 Hiy0 Hcrit_rest Hchk)
        as [Hix0_le_iy0 Hbounds].
      (* ix0 = iy0 already, so all the bounds collapse to ix0. *)
      (* The common index is ix0 = iy0. *)
      exists ix0.
      destruct Hix0 as [Hix01 Hix02].
      split; [exact Hix01 |].
      intros p Hp.
      (* Need fst p, snd p ∈ block ix0. Both have an index; show it equals ix0. *)
      destruct (at_index_exists (fst p)) as [ifp Hifp].
      destruct (at_index_exists (snd p)) as [isp Hisp].
      (* p is critical: index(fst p) = index(snd p). *)
      assert (Hp_crit : IsCriticalPair (ep_order E) (fst p) (snd p)).
      { exact (Hcrit p Hp). }
      assert (Hfp_sp : ifp = isp).
      { destruct Hifp as [Hifp1 Hifp2]; destruct Hisp as [Hisp1 Hisp2].
        exact (fullysync_crit_same_block (fst p) (snd p) ifp isp
                 Hifp1 Hisp1 Hifp2 Hisp2 Hp_crit). }
      (* p is in cyc = (x0,y0)::rest. Either p = (x0,y0) or p in rest. *)
      simpl in Hp.
      assert (Hifp_eq : ifp = ix0).
      { destruct Hp as [Heqp | Hp].
        - (* p = (x0,y0) : fst p = x0, so ifp = ix0. *)
          subst p. simpl in Hifp.
          exact (at_index_functional ifp ix0 x0 Hifp (conj Hix01 Hix02)).
        - (* p in rest: bounds give iy0 <= ifp <= ix0; with ix0 = iy0, ifp = ix0. *)
          destruct (Hbounds p Hp ifp Hifp) as [Hlo Hhi]. lia. }
      (* Conclude both endpoints in block ix0. *)
      destruct Hifp as [Hifp1 Hifp2]; destruct Hisp as [Hisp1 Hisp2].
      rewrite Hifp_eq in Hifp2.
      assert (Hisp_eq : isp = ix0) by lia.
      rewrite Hisp_eq in Hisp2.
      split; assumption.
  Qed.

End FullySync.

(* ---- Lifting a whole-poset alternating cycle into a sub-poset block. ---- *)

(* Lift a list of pairs all of whose endpoints lie in [B] into a list of
   pairs of the subtype, via [List.In]-membership proofs.  We thread the
   membership hypothesis [HallB] through structural recursion using
   [In_cons]/[In_eq] so no informative classical choice is needed. *)

Section LiftCycle.
  Context (E : ExecPoset) (B : Ensemble (ep_carrier E)).

  Definition liftpt (x : ep_carrier E) (Hx : Ensembles.In _ B x)
    : {z : ep_carrier E | Ensembles.In _ B z} := exist _ x Hx.

  (* The check relation transfers: it is the same [ep_order E] on projections. *)
  Lemma check_alt_lift :
    forall (sub : list ({z | Ensembles.In _ B z} * {z | Ensembles.In _ B z}))
           (fx ly : {z | Ensembles.In _ B z}),
      check_alternating_cycle (ep_order E) (proj1_sig fx) (proj1_sig ly)
        (map (fun q => (proj1_sig (fst q), proj1_sig (snd q))) sub) ->
      check_alternating_cycle (sub_order E B) fx ly sub.
  Proof.
    induction sub as [| q sub IH]; intros fx ly Hchk.
    - simpl in *. unfold sub_order. exact Hchk.
    - destruct q as [xq yq]. simpl in Hchk. destruct Hchk as [Hrel Hrest].
      simpl. split.
      + unfold sub_order. exact Hrel.
      + exact (IH fx yq Hrest).
  Qed.

  (* Full transfer: a non-empty lifted list whose projection is an alternating
     cycle of [ep_order E], and all of whose subtype pairs are critical for
     [sub_order E B], is an alternating cycle of [sub_order E B]. *)
  Lemma is_alt_cycle_lift :
    forall (sx0 sy0 : {z | Ensembles.In _ B z})
           (srest : list ({z | Ensembles.In _ B z} * {z | Ensembles.In _ B z})),
      (forall p, List.In p ((sx0, sy0) :: srest) ->
         IsCriticalPair (sub_order E B) (fst p) (snd p)) ->
      check_alternating_cycle (ep_order E) (proj1_sig sx0) (proj1_sig sy0)
        (map (fun q => (proj1_sig (fst q), proj1_sig (snd q))) srest) ->
      IsAlternatingCycle (sub_order E B) ((sx0, sy0) :: srest).
  Proof.
    intros sx0 sy0 srest Hcrit Hchk.
    unfold IsAlternatingCycle.
    cbv match.
    split.
    - exact Hcrit.
    - exact (check_alt_lift srest sx0 sy0 Hchk).
  Qed.
End LiftCycle.

(* No alternating cycle propagates from blocks to the whole execution. *)
Lemma fully_sync_no_alt_cycle :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks -> no_alt_cycle _ (sub_order E blk)) ->
    no_alt_cycle _ (ep_order E).
Proof.
  intros E blocks Hfs Hblocks.
  intros [cyc [Hcrit Halt]].
  (* The cycle lives in a single block index i. *)
  destruct (alt_cycle_in_one_block E blocks Hfs cyc Hcrit Halt)
    as [i [Hi Hin]].
  set (B := nth i blocks (Empty_set (ep_carrier E))).
  (* B is one of the blocks (nth_In). *)
  assert (HBin : List.In B blocks) by (apply nth_In; exact Hi).
  (* B has no alternating cycle. *)
  apply (Hblocks B HBin).
  (* We construct the lifted cycle in sub_order E B.  To carry the membership
     proofs we recurse on cyc with a "all endpoints in B" hypothesis. *)
  (* Define the lifted list and prove it is an alternating cycle. *)
  assert (HallB : forall p, List.In p cyc ->
            Ensembles.In _ B (fst p) /\ Ensembles.In _ B (snd p)) by exact Hin.
  (* Build the lifted cycle by recursion preserving membership proofs. *)
  revert Hcrit Halt HallB.
  (* General lifting lemma over an arbitrary list, then specialize. *)
  assert (Hlift :
    forall (l : list (ep_carrier E * ep_carrier E)),
      (forall p, List.In p l -> IsCriticalPair (ep_order E) (fst p) (snd p)) ->
      (forall p, List.In p l ->
         Ensembles.In _ B (fst p) /\ Ensembles.In _ B (snd p)) ->
      exists sub : list ({z | Ensembles.In _ B z} * {z | Ensembles.In _ B z}),
        map (fun q => (proj1_sig (fst q), proj1_sig (snd q))) sub = l /\
        (forall p, List.In p sub ->
           IsCriticalPair (sub_order E B) (fst p) (snd p))).
  { induction l as [| p l IH]; intros Hcr Hmem.
    - exists nil. split; [reflexivity | intros q Hq; inversion Hq].
    - destruct p as [xp yp].
      assert (Hp_mem : Ensembles.In _ B xp /\ Ensembles.In _ B yp).
      { exact (Hmem (xp, yp) (or_introl eq_refl)). }
      destruct Hp_mem as [Hxp Hyp].
      assert (Hp_crit : IsCriticalPair (ep_order E) xp yp).
      { exact (Hcr (xp, yp) (or_introl eq_refl)). }
      destruct (IH (fun q Hq => Hcr q (or_intror Hq))
                   (fun q Hq => Hmem q (or_intror Hq)))
        as [sub [Hmap Hcrsub]].
      exists ((exist _ xp Hxp, exist _ yp Hyp) :: sub).
      split.
      + simpl. rewrite Hmap. reflexivity.
      + intros q Hq. destruct Hq as [Heq | Hq].
        * subst q. simpl.
          exact (critical_pair_in_block E B xp yp Hxp Hyp Hp_crit).
        * exact (Hcrsub q Hq). }
  intros Hcrit Halt HallB.
  destruct (Hlift cyc Hcrit HallB) as [sub [Hmap Hcrsub]].
  (* Now [sub] is the lifted cycle.  Show IsAlternatingCycle (sub_order E B) sub. *)
  destruct cyc as [| q0 rest] eqn:Ecyc.
  - simpl in Halt. contradiction.
  - (* sub is non-nil because its projection equals a cons. *)
    destruct sub as [| sq0 srest] eqn:Esub.
    + simpl in Hmap. discriminate Hmap.
    + (* The head of sub projects to q0. *)
      destruct sq0 as [sx0 sy0].
      simpl in Hmap. injection Hmap as Hhead Htail.
      destruct q0 as [x0 y0]. simpl in Hhead.
      (* Hhead : (proj1_sig sx0, proj1_sig sy0) = (x0, y0) *)
      injection Hhead as Hx0 Hy0.
      simpl in Halt. destruct Halt as [_ Hchk].
      exists ((sx0, sy0) :: srest).
      split.
      * (* every pair critical in the sub-poset *)
        exact Hcrsub.
      * (* IsAlternatingCycle (sub_order E B) ((sx0,sy0)::srest) *)
        apply (is_alt_cycle_lift E B sx0 sy0 srest Hcrsub).
        (* Goal: check_alternating_cycle (ep_order E)
                   (proj1_sig sx0) (proj1_sig sy0) (map proj srest). *)
        rewrite Hx0, Hy0, Htail.
        exact Hchk.
Qed.

(* No-alt-cycle in every block ⟹ whole execution has dimension ≤ 2. *)
Lemma fully_sync_dim2 :
  forall E blocks, IsFullySync E blocks ->
    (forall blk, List.In blk blocks -> no_alt_cycle _ (sub_order E blk)) ->
    exists d, exec_has_dimension E d /\ d <= 2.
Proof.
  intros E blocks Hfs Hblocks.
  apply exec_dim_le_2_of_no_alt_cycle.
  pose proof (fully_sync_no_alt_cycle E blocks Hfs Hblocks) as Hno.
  unfold no_alt_cycle in Hno.
  intro Hex. apply Hno.
  destruct Hex as [cycle [Hin Halt]].
  exists cycle. split; [| exact Halt].
  intros p Hp. unfold exec_critical_pair in Hin. exact (Hin p Hp).
Qed.
