(* exact n-way ordinal-partition dimension

   Part 1: a singleton-union prefix sub-lemma.  If the union [L] of a nonempty
   prefix [pre] (blocks nonempty, pairwise disjoint) has at most one element,
   then [pre] is a single block and its per-block dimension fold is 0. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Arith Lia Classical
                          ProofIrrelevance.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems AntichainComplement.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim FinExtremumDim FinFullySync.
Import ListNotations.

(* If the union L of a nonempty prefix `pre` (blocks nonempty, pairwise disjoint)
   has at most one element, then `pre` is a single block and its dims-fold is 0. *)
Lemma singleton_union_one_block :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (pre : list (Ensemble A)) (predims : list nat) (L : Ensemble A),
    pre <> [] ->
    length predims = length pre ->
    (forall i, i < length pre -> exists x, Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    (forall i j x, i < length pre -> j < length pre -> i <> j ->
       Ensembles.In _ (nth i pre (Empty_set _)) x ->
       ~ Ensembles.In _ (nth j pre (Empty_set _)) x) ->
    (forall i, i < length pre ->
       PosetDimension (fin_sub_order R (nth i pre (Empty_set _))) (nth i predims 0)) ->
    (forall x, Ensembles.In _ L x <->
       exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    (forall u v : {z | Ensembles.In _ L z}, u = v) ->
    fold_right Nat.max 0 predims = 0.
Proof.
  intros A R HR pre predims L Hne Hlen Hnonempty Hdisj Hdims HLeq Hone.
  (* Step 1: length pre = 1. *)
  assert (Hlen1 : length pre = 1).
  { destruct (Nat.eq_dec (length pre) 1) as [He | Hne1]; [exact He |].
    (* length pre <> 1 and pre <> [] => length pre >= 2 *)
    assert (Hge2 : 2 <= length pre).
    { destruct pre as [|B0 [|B1 rest]]; simpl in *; [contradiction Hne; reflexivity | lia | lia]. }
    (* indices 0 and 1 both valid *)
    assert (H0 : 0 < length pre) by lia.
    assert (H1 : 1 < length pre) by lia.
    destruct (Hnonempty 0 H0) as [x0 Hx0].
    destruct (Hnonempty 1 H1) as [x1 Hx1].
    (* both in L *)
    assert (Hx0L : Ensembles.In _ L x0).
    { apply HLeq. exists 0. split; [exact H0 | exact Hx0]. }
    assert (Hx1L : Ensembles.In _ L x1).
    { apply HLeq. exists 1. split; [exact H1 | exact Hx1]. }
    (* lift into the subtype, use all-equal *)
    pose (u0 := exist (fun z => Ensembles.In _ L z) x0 Hx0L).
    pose (u1 := exist (fun z => Ensembles.In _ L z) x1 Hx1L).
    assert (Hu : u0 = u1) by apply Hone.
    assert (Hx01 : x0 = x1).
    { change x0 with (proj1_sig u0). change x1 with (proj1_sig u1). rewrite Hu. reflexivity. }
    (* contradiction: x1 in block 0 (via x0=x1) and x1 in block 1, disjoint *)
    subst x0.
    pose proof (Hdisj 0 1 x1 H0 H1 ltac:(lia) Hx0) as Hnot1.
    contradiction. }
  (* turn length pre = 1 into pre = [B0] *)
  destruct pre as [|B0 [|B1 rest]]; simpl in Hlen1; try lia.
  clear Hlen1 Hne.
  (* predims has length 1 too *)
  simpl in Hlen.
  destruct predims as [|d0 [|d1 prest]]; simpl in Hlen; try lia.
  clear Hlen.
  (* L = B0 elementwise *)
  assert (HLB0 : forall x, Ensembles.In _ L x <-> Ensembles.In _ B0 x).
  { intro x. rewrite HLeq. split.
    - intros [i [Hi Hin]]. simpl in Hi.
      assert (i = 0) by lia. subst i. simpl in Hin. exact Hin.
    - intro Hin. exists 0. split; [simpl; lia | simpl; exact Hin]. }
  (* the block B0 has at most one element *)
  assert (HoneB0 : forall u v : {z | Ensembles.In _ B0 z}, u = v).
  { intros u v. destruct u as [xu Hu]. destruct v as [xv Hv].
    assert (HxuL : Ensembles.In _ L xu) by (apply HLB0; exact Hu).
    assert (HxvL : Ensembles.In _ L xv) by (apply HLB0; exact Hv).
    assert (Heq : exist (fun z => Ensembles.In _ L z) xu HxuL
                  = exist (fun z => Ensembles.In _ L z) xv HxvL) by apply Hone.
    assert (Hxx : xu = xv).
    { change xu with (proj1_sig (exist (fun z => Ensembles.In _ L z) xu HxuL)).
      change xv with (proj1_sig (exist (fun z => Ensembles.In _ L z) xv HxvL)).
      rewrite Heq. reflexivity. }
    subst xv.
    f_equal. apply proof_irrelevance. }
  (* singleton block => dimension 0 *)
  pose proof (@fin_singleton_dim0 _ (fin_sub_order R B0) (fin_sub_order_poset R B0) HoneB0)
    as Hdim0.
  (* the recorded dimension d0 of block 0 *)
  assert (Hd0dim : PosetDimension (fin_sub_order R B0) d0).
  { pose proof (Hdims 0 ltac:(simpl; lia)) as Hd.
    simpl in Hd. exact Hd. }
  (* uniqueness => d0 = 0 *)
  assert (Hd0 : d0 = 0).
  { apply (@fin_posdim_unique _ (fin_sub_order R B0) (fin_sub_order_poset R B0)
             d0 0 Hd0dim Hdim0). }
  subst d0.
  simpl. reflexivity.
Qed.

(* Like [restricted_block_dim2] but yielding a bare [PosetDimension] witness,
   so it can discharge a Type-sorted dimension goal in the induction. *)
Lemma restricted_block_dim_exact :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (L B : Ensemble A),
    (forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    forall d, PosetDimension (fin_sub_order R B) d ->
      PosetDimension
        (fin_sub_order (fin_sub_order R L) (restrict_block L B)) d.
Proof.
  intros A R HR L B Hsub d Hd.
  pose proof (fin_sub_order_poset R B) as HposB.
  pose proof (fin_sub_order_poset R L) as HposL.
  pose proof (fin_sub_order_poset (fin_sub_order R L) (restrict_block L B)) as HposTgt.
  pose (f := fun s : {z | Ensembles.In _ B z} =>
               let (x, HxB) := s in
               exist (fun w : {z | Ensembles.In _ L z} =>
                        Ensembles.In _ (restrict_block L B) w)
                     (exist (fun z => Ensembles.In _ L z) x (Hsub x HxB))
                     HxB).
  pose (g := fun w : {w : {z | Ensembles.In _ L z}
                      | Ensembles.In _ (restrict_block L B) w} =>
               exist (fun z => Ensembles.In _ B z)
                     (proj1_sig (proj1_sig w)) (proj2_sig w)).
  apply (dimension_iso
           {z | Ensembles.In _ B z}
           {w : {z | Ensembles.In _ L z}
            | Ensembles.In _ (restrict_block L B) w}
           (fin_sub_order R B)
           (fin_sub_order (fin_sub_order R L) (restrict_block L B))
           f g).
  - intro s. destruct s as [x HxB]. unfold f, g. cbn. reflexivity.
  - intro w. destruct w as [[x HxL] Hw]. unfold f, g. cbn.
    generalize (Hsub x Hw); intro HxL'.
    replace HxL' with HxL by apply proof_irrelevance.
    reflexivity.
  - intros s s'. destruct s as [x HxB]. destruct s' as [x' Hx'B].
    unfold f, fin_sub_order. simpl. reflexivity.
  - exact Hd.
Qed.

(* fold_right Nat.max over a list with one element appended. *)
Lemma fold_right_max_app :
  forall (l : list nat) (x : nat),
    fold_right Nat.max 0 (l ++ [x]) = Nat.max (fold_right Nat.max 0 l) x.
Proof.
  induction l as [|a l IHl]; intro x; simpl.
  - lia.
  - rewrite IHl. lia.
Qed.

(* The exact n-way ordinal-partition dimension theorem, carrier-quantified for
   strong induction.  The dimension of the whole order equals
   [Nat.max 1 (fold_right Nat.max 0 dims)] where [dims] lists the per-block
   dimensions of the ordinal partition. *)
Lemma fin_fully_sync_dimension_aux :
  forall n (A : Type) (R : A -> A -> Prop) (HR : IsPoset A R)
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)) (dims : list nat),
    length blocks <= n -> length dims = length blocks ->
    @fin_ordinal_partition A R blocks ->
    (forall i, i < length blocks ->
       PosetDimension (@fin_sub_order A R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : A, a <> b) ->
    forall dW, PosetDimension R dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims).
Proof.
  induction n as [|n IHn];
    intros A R HR Hfin blocks dims Hlen Hlendims Hpart Hdims Hge2 dW HdW.
  - (* base: length blocks <= 0 => blocks = [] => carrier empty, contradicting Hge2 *)
    exfalso. destruct Hge2 as [a [b _]].
    destruct Hpart as [_ [Hcov _]].
    destruct (Hcov a) as [i [Hi _]]. simpl in Hi.
    apply Nat.le_0_r in Hlen. apply length_zero_iff_nil in Hlen. subst blocks.
    simpl in Hi. lia.
  - (* step: write blocks as pre ++ [Bk] (or []) *)
    destruct blocks as [|b0 bs] eqn:Hbl.
    + (* blocks = [] : carrier empty, contradicting Hge2 *)
      exfalso. destruct Hge2 as [a [b _]].
      destruct Hpart as [_ [Hcov _]].
      destruct (Hcov a) as [i [Hi _]]. simpl in Hi. lia.
    + assert (Hneq : b0 :: bs <> []) by discriminate.
      rewrite <- Hbl in *. clear Hbl b0 bs.
      destruct (exists_last Hneq) as [pre [Bk Heq]]. subst blocks.
      assert (Hlenpre : length pre <= n).
      { rewrite length_app in Hlen. simpl in Hlen. lia. }
      (* peel dims as predims ++ [dk] *)
      assert (Hlenpre1 : length pre + 1 = length (pre ++ [Bk])).
      { rewrite length_app. reflexivity. }
      assert (Hdimsne : dims <> []).
      { intro Hc. subst dims. simpl in Hlendims.
        rewrite length_app in Hlendims. simpl in Hlendims. lia. }
      destruct (exists_last Hdimsne) as [predims [dk Hdeq]]. subst dims.
      assert (Hlenpredims : length predims = length pre).
      { rewrite length_app in Hlendims. rewrite length_app in Hlendims.
        simpl in Hlendims. lia. }
      (* per-block dimension for Bk *)
      assert (HnthBk : nth (length pre) (pre ++ [Bk]) (Empty_set _) = Bk).
      { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
      assert (HnthdkB : nth (length pre) (predims ++ [dk]) 0 = dk).
      { rewrite app_nth2 by lia. rewrite Hlenpredims. rewrite Nat.sub_diag.
        reflexivity. }
      assert (HBkidx : length pre < length (pre ++ [Bk])).
      { rewrite length_app. simpl. lia. }
      assert (Hdk : PosetDimension (fin_sub_order R Bk) dk).
      { pose proof (Hdims (length pre) HBkidx) as Hd.
        rewrite HnthBk in Hd. rewrite HnthdkB in Hd. exact Hd. }
      (* per-block dimension for prefix entries *)
      assert (Hdimspre : forall i, i < length pre ->
                PosetDimension (fin_sub_order R (nth i pre (Empty_set _)))
                               (nth i predims 0)).
      { intros i Hi.
        assert (Hi' : i < length (pre ++ [Bk])).
        { rewrite length_app. simpl. lia. }
        pose proof (Hdims i Hi') as Hd.
        rewrite app_nth1 in Hd by exact Hi.
        rewrite app_nth1 in Hd by (rewrite Hlenpredims; exact Hi).
        exact Hd. }
      destruct pre as [|p0 ps] eqn:Hpre.
      * (* pre = [] : blocks = [Bk], Bk is full, dims = [dk] *)
        (* predims = [] *)
        assert (Hpd : predims = []).
        { apply length_zero_iff_nil. exact Hlenpredims. }
        subst predims.
        assert (Hfoldeq : fold_right Nat.max 0 ([] ++ [dk]) = dk).
        { simpl. apply Nat.max_0_r. }
        rewrite Hfoldeq.
        assert (HBkfull : forall x, Ensembles.In _ Bk x).
        { intro x. destruct Hpart as [_ [Hcov _]].
          destruct (Hcov x) as [i [Hi Hxi]]. simpl in Hi.
          assert (i = 0) by lia. subst i. simpl in Hxi. exact Hxi. }
        (* lift Bk's dimension to R *)
        pose proof (fin_block_iso_full R Bk HBkfull dk (inhabits Hdk)) as [HdkR].
        assert (HdWdk : dW = dk).
        { apply (@fin_posdim_unique _ R HR dW dk HdW HdkR). }
        assert (Hdk1 : 1 <= dk).
        { rewrite <- HdWdk. apply (dim_ge_1_of_two R dW HdW Hge2). }
        rewrite HdWdk. apply eq_sym. apply Nat.max_r. exact Hdk1.
      * (* pre <> [] : barrier L | Bk, recurse via IHn *)
        assert (Hpreneq : p0 :: ps <> []) by discriminate.
        rewrite <- Hpre in *. clear Hpre p0 ps.
        set (L := fun x => exists i, i < length pre /\
                          Ensembles.In _ (nth i pre (Empty_set _)) x).
        assert (Hbar : fin_is_barrier R L Bk)
          by exact (fin_prefix_barrier R pre Bk Hpreneq Hpart).
        pose proof (fin_sub_order_poset R L) as HposL.
        (* L has a dimension dL *)
        destruct (fin_dim_exists (fin_sub_order R L)
                    (fin_sub_order_finite R Hfin L)) as [dL [HdL]].
        (* exact barrier dimension formula *)
        pose proof (fin_barrier_dimension_full R Hfin L Bk Hbar dL dk dW HdL Hdk HdW)
          as HdWeq.
        (* unfold the fold over predims ++ [dk] *)
        rewrite (fold_right_max_app predims dk).
        (* split on whether L has two distinct elements *)
        destruct (classic (exists u v : {z | Ensembles.In _ L z}, u <> v))
          as [HL2 | HL1].
        -- (* L has >= 2 elements: recurse with IHn *)
           assert (HdLeq : dL = Nat.max 1 (fold_right Nat.max 0 predims)).
           { apply (IHn {z | Ensembles.In _ L z}
                       (fin_sub_order R L)
                       (fin_sub_order_poset R L)
                       (fin_sub_order_finite R Hfin L)
                       (map (restrict_block L) pre)
                       predims).
             - rewrite length_map. exact Hlenpre.
             - rewrite length_map. exact Hlenpredims.
             - exact (fin_prefix_restricted_partition R pre Bk Hpart).
             - intros i Hi'.
               rewrite length_map in Hi'.
               rewrite (nth_map_restrict R L pre i Hi').
               (* prefix block (nth i pre ∅) ⊆ L *)
               assert (HBsub : forall x, Ensembles.In _ (nth i pre (Empty_set _)) x ->
                                         Ensembles.In _ L x).
               { intros x HxB. exists i. split; [exact Hi' | exact HxB]. }
               exact (restricted_block_dim_exact R L (nth i pre (Empty_set _)) HBsub
                        (nth i predims 0) (Hdimspre i Hi')).
             - exact HL2.
             - exact HdL. }
           rewrite HdWeq. rewrite HdLeq. lia.
        -- (* L has <= 1 element: singleton, so dL = 0 and fold predims = 0 *)
           assert (Hone : forall u v : {z | Ensembles.In _ L z}, u = v).
           { intros u v. destruct (classic (u = v)) as [He | Hne].
             - exact He.
             - exfalso. apply HL1. exists u, v. exact Hne. }
           (* singleton => dimension 0 *)
           pose proof (@fin_singleton_dim0 _ (fin_sub_order R L)
                         (fin_sub_order_poset R L) Hone) as Hdim0.
           assert (HdL0 : dL = 0).
           { apply (@fin_posdim_unique _ (fin_sub_order R L)
                      (fin_sub_order_poset R L) dL 0 HdL Hdim0). }
           (* fold over predims = 0, via singleton_union_one_block *)
           assert (Hfold0 : fold_right Nat.max 0 predims = 0).
           { apply (singleton_union_one_block R pre predims L Hpreneq Hlenpredims).
             - (* nonempty *)
               intros i Hi.
               destruct Hpart as [Hne _].
               assert (Hi' : i < length (pre ++ [Bk])).
               { rewrite length_app. simpl. lia. }
               assert (Hin : List.In (nth i (pre ++ [Bk]) (Empty_set _)) (pre ++ [Bk])).
               { apply nth_In. exact Hi'. }
               rewrite app_nth1 in Hin by exact Hi.
               exact (Hne _ Hin).
             - (* disjoint *)
               intros i j x Hi Hj Hij HxiIn.
               destruct Hpart as [_ [_ [Hdisj _]]].
               assert (Hi' : i < length (pre ++ [Bk])).
               { rewrite length_app. simpl. lia. }
               assert (Hj' : j < length (pre ++ [Bk])).
               { rewrite length_app. simpl. lia. }
               pose proof (Hdisj i j x Hi' Hj' Hij) as Hd.
               rewrite app_nth1 in Hd by exact Hi.
               rewrite app_nth1 in Hd by exact Hj.
               exact (Hd HxiIn).
             - (* prefix dims *)
               exact Hdimspre.
             - (* L = union of pre *)
               intro x. unfold L. reflexivity.
             - exact Hone. }
           rewrite HdWeq. rewrite HdL0. rewrite Hfold0. lia.
Qed.

Lemma fin_fully_sync_dimension :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)) (dims : list nat),
    fin_ordinal_partition R blocks ->
    length dims = length blocks ->
    (forall i, i < length blocks ->
       PosetDimension (fin_sub_order R (nth i blocks (Empty_set _))) (nth i dims 0)) ->
    (exists a b : A, a <> b) ->
    forall dW, PosetDimension R dW -> dW = Nat.max 1 (fold_right Nat.max 0 dims).
Proof.
  intros A R HR Hfin blocks dims Hpart Hlendims Hdims Hge2 dW HdW.
  exact (fin_fully_sync_dimension_aux (length blocks) A R HR Hfin blocks dims
           (le_n _) Hlendims Hpart Hdims Hge2 dW HdW).
Qed.
