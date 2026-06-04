(* generic n-way ordinal-partition dim<=2 theorem

   Part 1: the generic ordinal-partition predicate, subtype-finiteness, and
   the full-block order-isomorphism lever.  Later tasks append to this file. *)

From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts List Image Arith Lia Classical
                          ProofIrrelevance FunctionalExtensionality PropExtensionality.
From Posets Require Import PosetClasses FinitePoset.
From Dimension Require Import DimDefs Theorems.
From Execution Require Import DimIso FinPosetDimSurgery FinPosetDim.
Import ListNotations.

Section FinFullySync.
  Context {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}.
  Context (Hfin : Finite A (Full_set A)).

  (* A finite ordinal partition of (A,R): a list of nonempty blocks that
     covers A, is pairwise disjoint, and is ordinally stacked (everything in
     an earlier block is below everything in a later block under R). *)
  Definition fin_ordinal_partition (blocks : list (Ensemble A)) : Prop :=
    (forall blk, List.In blk blocks -> exists x, Ensembles.In _ blk x) /\
    (forall x, exists i, i < length blocks /\ Ensembles.In _ (nth i blocks (Empty_set _)) x) /\
    (forall i j x, i < length blocks -> j < length blocks -> i <> j ->
       Ensembles.In _ (nth i blocks (Empty_set _)) x ->
       ~ Ensembles.In _ (nth j blocks (Empty_set _)) x) /\
    (forall i j, i < j -> j < length blocks ->
       forall x y, Ensembles.In _ (nth i blocks (Empty_set _)) x ->
                   Ensembles.In _ (nth j blocks (Empty_set _)) y -> R x y).

  (* Restrict a block [B] to the subtype carried by [L]. *)
  Definition restrict_block (L B : Ensemble A) : Ensemble {z | Ensembles.In _ L z} :=
    fun z => Ensembles.In _ B (proj1_sig z).
End FinFullySync.

(* The subtype carrier of any subset of a finite carrier is itself finite. *)
Lemma fin_sub_order_finite :
  forall {A : Type} (R : A -> A -> Prop) (Hfin : Finite A (Full_set A)) (L : Ensemble A),
    Finite {z : A | Ensembles.In _ L z} (Full_set {z | Ensembles.In _ L z}).
Proof.
  intros A R Hfin L.
  (* L is finite, being a subset of the finite Full_set A. *)
  assert (HLfin : Finite A L).
  { apply Finite_downward_closed with (Full_set A).
    - exact Hfin.
    - intros x _. apply Full_intro. }
  destruct (finite_cardinal _ _ HLfin) as [m Hm].
  apply (cardinal_finite _ _ m).
  exact (cardinal_subtype_full A L m Hm).
Qed.

(* If a block [B] is all of [A], then the subtype order on [B] is order-iso to
   [R], so any dimension witness for the block lifts to one for (A,R). *)
Lemma fin_block_iso_full :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (B : Ensemble A),
    (forall x, Ensembles.In _ B x) ->
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
              inhabited (PosetDimension R d).
Proof.
  intros A R HR B HBfull d [Hd].
  (* maps between A and {z | In B z} *)
  pose (f := fun x : A => exist (fun z => Ensembles.In _ B z) x (HBfull x)).
  pose (g := @proj1_sig A (fun z => Ensembles.In _ B z)).
  apply inhabits.
  (* The block-subtype carries [fin_sub_order_poset R B]. *)
  pose proof (fin_sub_order_poset R B) as Hsubpos.
  (* Transport the dimension witness from the block order to R using the
     inverse iso (f' := g, g' := f). *)
  apply (dimension_iso {z | Ensembles.In _ B z} A
           (fin_sub_order R B) R g f).
  - (* f' (g' z) = z, i.e. f (g z) = z *)
    intro z. destruct z as [x Hx]. unfold f, g. simpl.
    f_equal. apply proof_irrelevance.
  - (* g' (f' x) = x, i.e. g (f x) = x *)
    intro x. unfold f, g. reflexivity.
  - (* order iso: fin_sub_order R B z z' <-> R (g z) (g z') *)
    intros z z'. unfold fin_sub_order, g. reflexivity.
  - exact Hd.
Qed.

(* A prefix block (B ⊆ L), restricted to the L-subtype, has the same dimension. *)
Lemma restricted_block_dim2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (L B : Ensemble A),
    (forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    forall d, inhabited (PosetDimension (fin_sub_order R B) d) ->
      inhabited (PosetDimension
                  (fin_sub_order (fin_sub_order R L) (restrict_block L B)) d).
Proof.
  intros A R HR L B Hsub d [Hd].
  apply inhabits.
  (* Make the two subtype-poset instances available to resolution. *)
  pose proof (fin_sub_order_poset R B) as HposB.
  pose proof (fin_sub_order_poset R L) as HposL.
  pose proof (fin_sub_order_poset (fin_sub_order R L) (restrict_block L B)) as HposTgt.
  (* source carrier: {z | In B z}; target carrier:
     {w : {z | In L z} | In (restrict_block L B) w}. *)
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
  - (* g (f s) = s *)
    intro s. destruct s as [x HxB]. unfold f, g. cbn.
    reflexivity.
  - (* f (g w) = w *)
    intro w. destruct w as [[x HxL] Hw]. unfold f, g. cbn.
    (* goal: exist _ (exist _ x (Hsub x Hw)) Hw = exist _ (exist _ x HxL) Hw *)
    (* The inner [In L x] proofs differ; replace [Hsub x Hw] by [HxL]. *)
    generalize (Hsub x Hw); intro HxL'.
    replace HxL' with HxL by apply proof_irrelevance.
    reflexivity.
  - (* order iso *)
    intros s s'. destruct s as [x HxB]. destruct s' as [x' Hx'B].
    unfold f, fin_sub_order. simpl. reflexivity.
  - exact Hd.
Qed.

(* The prefix of an ordinal partition, restricted to its union L, is an ordinal
   partition of the L-subtype. *)
Lemma nth_map_restrict :
  forall {A : Type} (R : A -> A -> Prop) (L : Ensemble A)
         (pre : list (Ensemble A)) (i : nat),
    i < length pre ->
    nth i (map (restrict_block L) pre) (Empty_set _)
    = restrict_block L (nth i pre (Empty_set _)).
Proof.
  intros A R L pre i Hi.
  rewrite (nth_indep (map (restrict_block L) pre) (Empty_set _)
             (restrict_block L (Empty_set _))).
  - rewrite map_nth. reflexivity.
  - rewrite length_map. exact Hi.
Qed.

Lemma restrict_partition :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R} (L : Ensemble A) (pre : list (Ensemble A)),
    (forall B, List.In B pre -> forall x, Ensembles.In _ B x -> Ensembles.In _ L x) ->
    fin_ordinal_partition R pre ->
    (forall x, Ensembles.In _ L x <->
       exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x) ->
    fin_ordinal_partition (fin_sub_order R L) (map (restrict_block L) pre).
Proof.
  intros A R HR L pre Hsub Hpart HLeq.
  destruct Hpart as [Hne [Hcov [Hdis Hbel]]].
  unfold fin_ordinal_partition.
  repeat split.
  - (* nonempty *)
    intros blk Hblk.
    apply in_map_iff in Hblk. destruct Hblk as [B [HBeq HBin]]. subst blk.
    destruct (Hne B HBin) as [x HxB].
    pose (HxL := Hsub B HBin x HxB).
    exists (exist (fun z => Ensembles.In _ L z) x HxL).
    unfold restrict_block. simpl. exact HxB.
  - (* cover *)
    intro z. destruct z as [x HxL].
    destruct (proj1 (HLeq x) HxL) as [i [Hi Hxi]].
    exists i. split.
    + rewrite length_map. exact Hi.
    + rewrite (nth_map_restrict R L pre i Hi).
      unfold restrict_block. simpl. exact Hxi.
  - (* disjoint *)
    intros i j z Hi Hj Hij Hzi Hzj.
    rewrite length_map in Hi, Hj.
    rewrite (nth_map_restrict R L pre i Hi) in Hzi.
    rewrite (nth_map_restrict R L pre j Hj) in Hzj.
    unfold restrict_block in Hzi, Hzj. simpl in Hzi, Hzj.
    apply (Hdis i j (proj1_sig z) Hi Hj Hij Hzi Hzj).
  - (* below *)
    intros i j Hij Hj x y Hxi Hyj.
    rewrite length_map in Hj.
    assert (Hi : i < length pre) by lia.
    rewrite (nth_map_restrict R L pre i Hi) in Hxi.
    rewrite (nth_map_restrict R L pre j Hj) in Hyj.
    unfold restrict_block in Hxi, Hyj. simpl in Hxi, Hyj.
    unfold fin_sub_order.
    apply (Hbel i j Hij Hj (proj1_sig x) (proj1_sig y) Hxi Hyj).
Qed.

(* ------------------------------------------------------------------ *)
(* Base case helper: when the carrier is empty, the empty set of linear
   extensions realizes R, so the dimension is 0.                       *)
(* ------------------------------------------------------------------ *)

Lemma fin_empty_carrier_realizer :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R},
    (forall x : A, False) ->
    @IsRealizer A R (Empty_set (A -> A -> Prop)).
Proof.
  intros A R HR Hempty.
  constructor.
  - (* realizer_linear: vacuous, no L in the empty realizer *)
    intros L HL. destruct HL.
  - (* realizer_intersection *)
    intros x y. exfalso. exact (Hempty x).
Qed.

Lemma fin_empty_carrier_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)),
    (forall x : A, False) ->
    exists d, inhabited (PosetDimension R d) /\ d <= 2.
Proof.
  intros A R HR Hfin Hempty.
  destruct (fin_dim_exists R Hfin) as [d [Hd]].
  exists d. split.
  - exact (inhabits Hd).
  - (* the empty realizer (cardinality 0) bounds d below: d <= 0 *)
    assert (Hle0 : d <= 0).
    { apply (dimension_is_minimum Hd (Empty_set (A -> A -> Prop)) 0).
      - exact (fin_empty_carrier_realizer R Hempty).
      - exact (card_empty (A -> A -> Prop)). }
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Step-case helper: the union L of a nonempty prefix together with the
   final block Bk forms a barrier (L below Bk).                        *)
(* ------------------------------------------------------------------ *)

Lemma fin_prefix_barrier :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (pre : list (Ensemble A)) (Bk : Ensemble A),
    pre <> [] ->
    @fin_ordinal_partition A R (pre ++ [Bk]) ->
    fin_is_barrier R
      (fun x => exists i, i < length pre /\ Ensembles.In _ (nth i pre (Empty_set _)) x)
      Bk.
Proof.
  intros A R HR pre Bk Hpre Hpart.
  set (L := fun x => exists i, i < length pre /\
                    Ensembles.In _ (nth i pre (Empty_set _)) x).
  destruct Hpart as [Hne [Hcov [Hdis Hbel]]].
  assert (Hlen : length (pre ++ [Bk]) = length pre + 1) by (rewrite length_app; reflexivity).
  (* nth on (pre ++ [Bk]): index < length pre hits pre; index = length pre hits Bk *)
  assert (Hnth_pre : forall i, i < length pre ->
            nth i (pre ++ [Bk]) (Empty_set _) = nth i pre (Empty_set _)).
  { intros i Hi. rewrite app_nth1 by exact Hi. reflexivity. }
  assert (Hnth_Bk : nth (length pre) (pre ++ [Bk]) (Empty_set _) = Bk).
  { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  unfold fin_is_barrier. repeat split.
  - (* cover: every x is in L or in Bk *)
    intro x. destruct (Hcov x) as [i [Hi Hxi]].
    rewrite Hlen in Hi.
    destruct (Nat.lt_ge_cases i (length pre)) as [Hlt | Hge].
    + left. exists i. split; [exact Hlt|].
      rewrite Hnth_pre in Hxi by exact Hlt. exact Hxi.
    + right. assert (Hieq : i = length pre) by lia. subst i.
      rewrite Hnth_Bk in Hxi. exact Hxi.
  - (* disjoint: not both in L and Bk *)
    intros x [HxL HxBk]. destruct HxL as [i [Hi Hxi]].
    (* x in pre-block i (i < length pre) and x in Bk = block (length pre) *)
    apply (Hdis i (length pre) x).
    + rewrite Hlen. lia.
    + rewrite Hlen. lia.
    + lia.
    + rewrite Hnth_pre by exact Hi. exact Hxi.
    + rewrite Hnth_Bk. exact HxBk.
  - (* inhabited L: prefix is nonempty, its block 0 is nonempty *)
    assert (Hpos : 0 < length pre).
    { destruct pre; [contradiction | simpl; lia]. }
    destruct (Hne (nth 0 (pre ++ [Bk]) (Empty_set _))) as [x Hx].
    { apply nth_In. rewrite Hlen. lia. }
    exists x. exists 0. split; [exact Hpos|].
    rewrite Hnth_pre in Hx by exact Hpos. exact Hx.
  - (* inhabited Bk *)
    destruct (Hne Bk) as [y Hy].
    { apply in_or_app. right. left. reflexivity. }
    exists y. exact Hy.
  - (* L below Bk *)
    intros x y HxL HyBk. destruct HxL as [i [Hi Hxi]].
    apply (Hbel i (length pre)).
    + exact Hi.
    + rewrite Hlen. lia.
    + rewrite Hnth_pre by exact Hi. exact Hxi.
    + rewrite Hnth_Bk. exact HyBk.
Qed.

(* ------------------------------------------------------------------ *)
(* Step-case helper: the prefix [pre], restricted to its own union L,
   is an ordinal partition of the L-subtype.  Assembled directly from
   the ordinal partition of [pre ++ [Bk]] (note: [pre] alone is NOT an
   ordinal partition of A — its cover clause would be false).         *)
(* ------------------------------------------------------------------ *)

Lemma fin_prefix_restricted_partition :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (pre : list (Ensemble A)) (Bk : Ensemble A),
    @fin_ordinal_partition A R (pre ++ [Bk]) ->
    let L := fun x => exists i, i < length pre /\
                      Ensembles.In _ (nth i pre (Empty_set _)) x in
    fin_ordinal_partition (fin_sub_order R L) (map (restrict_block L) pre).
Proof.
  intros A R HR pre Bk Hpart L.
  pose proof (fin_sub_order_poset R L) as HposL.
  destruct Hpart as [Hne [Hcov [Hdis Hbel]]].
  assert (Hlen : length (pre ++ [Bk]) = length pre + 1) by (rewrite length_app; reflexivity).
  assert (Hnth_pre : forall i, i < length pre ->
            nth i (pre ++ [Bk]) (Empty_set _) = nth i pre (Empty_set _)).
  { intros i Hi. rewrite app_nth1 by exact Hi. reflexivity. }
  unfold fin_ordinal_partition. repeat split.
  - (* nonempty *)
    intros blk Hblk.
    apply in_map_iff in Hblk. destruct Hblk as [B [HBeq HBin]]. subst blk.
    (* B is the i-th prefix block for some i < length pre *)
    apply In_nth with (d := Empty_set _) in HBin.
    destruct HBin as [i [Hi HBeq]].
    destruct (Hne B) as [x HxB].
    { apply in_or_app. left. rewrite <- HBeq. apply nth_In. exact Hi. }
    assert (HxL : Ensembles.In _ L x).
    { exists i. split; [exact Hi|]. rewrite HBeq. exact HxB. }
    exists (exist (fun z => Ensembles.In _ L z) x HxL).
    unfold restrict_block. simpl. exact HxB.
  - (* cover *)
    intro z. destruct z as [x HxL].
    destruct HxL as [i [Hi Hxi]].
    exists i. split.
    + rewrite length_map. exact Hi.
    + rewrite (nth_map_restrict R L pre i Hi).
      unfold restrict_block. simpl. exact Hxi.
  - (* disjoint *)
    intros i j z Hi Hj Hij Hzi Hzj.
    rewrite length_map in Hi, Hj.
    rewrite (nth_map_restrict R L pre i Hi) in Hzi.
    rewrite (nth_map_restrict R L pre j Hj) in Hzj.
    unfold restrict_block in Hzi, Hzj. simpl in Hzi, Hzj.
    apply (Hdis i j (proj1_sig z)).
    + rewrite Hlen. lia.
    + rewrite Hlen. lia.
    + exact Hij.
    + rewrite Hnth_pre by exact Hi. exact Hzi.
    + rewrite Hnth_pre by exact Hj. exact Hzj.
  - (* below *)
    intros i j Hij Hj x y Hxi Hyj.
    rewrite length_map in Hj.
    assert (Hi : i < length pre) by lia.
    rewrite (nth_map_restrict R L pre i Hi) in Hxi.
    rewrite (nth_map_restrict R L pre j Hj) in Hyj.
    unfold restrict_block in Hxi, Hyj. simpl in Hxi, Hyj.
    unfold fin_sub_order.
    apply (Hbel i j).
    + exact Hij.
    + rewrite Hlen. lia.
    + rewrite Hnth_pre by exact Hi. exact Hxi.
    + rewrite Hnth_pre by exact Hj. exact Hyj.
Qed.

(* ------------------------------------------------------------------ *)
(* The n-way induction theorem.  Carrier-quantified strong induction on
   a length bound, so the recursive call at the L-sub-poset (a DIFFERENT
   carrier) is a legitimate instance of the induction hypothesis.      *)
(* ------------------------------------------------------------------ *)

Lemma fin_fully_sync_dim_le2_aux :
  forall n (A : Type) (R : A -> A -> Prop) (HR : IsPoset A R)
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)),
    length blocks <= n ->
    @fin_ordinal_partition A R blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (@fin_sub_order A R blk) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
Proof.
  induction n as [|n IHn]; intros A R HR Hfin blocks Hlen Hpart Hblocks.
  - (* base: length blocks <= 0 => blocks = [] => carrier empty *)
    apply Nat.le_0_r in Hlen. apply length_zero_iff_nil in Hlen. subst blocks.
    apply (fin_empty_carrier_dim_le2 R Hfin).
    (* every x is in some block of [], impossible *)
    intro x. destruct Hpart as [_ [Hcov _]].
    destruct (Hcov x) as [i [Hi _]]. simpl in Hi. lia.
  - (* step: write blocks as pre ++ [Bk] (or []) *)
    destruct blocks as [|b0 bs] eqn:Hbl.
    + (* blocks = [] : carrier empty, as in base *)
      apply (fin_empty_carrier_dim_le2 R Hfin).
      intro x. destruct Hpart as [_ [Hcov _]].
      destruct (Hcov x) as [i [Hi _]]. simpl in Hi. lia.
    + assert (Hneq : b0 :: bs <> []) by discriminate.
      rewrite <- Hbl in *. clear Hbl b0 bs.
      destruct (exists_last Hneq) as [pre [Bk Heq]]. subst blocks.
      assert (Hlenpre : length pre <= n).
      { rewrite length_app in Hlen. simpl in Hlen. lia. }
      destruct pre as [|p0 ps] eqn:Hpre.
      * (* pre = [] : blocks = [Bk], Bk is full *)
        simpl.
        assert (HBkfull : forall x, Ensembles.In _ Bk x).
        { intro x. destruct Hpart as [_ [Hcov _]].
          destruct (Hcov x) as [i [Hi Hxi]]. simpl in Hi.
          assert (i = 0) by lia. subst i. simpl in Hxi. exact Hxi. }
        destruct (Hblocks Bk) as [d [Hd Hle]].
        { left. reflexivity. }
        exists d. split.
        -- exact (fin_block_iso_full R Bk HBkfull d Hd).
        -- exact Hle.
      * (* pre <> [] : barrier L | Bk, recurse on L via IHn *)
        assert (Hpreneq : p0 :: ps <> []) by discriminate.
        rewrite <- Hpre in *. clear Hpre p0 ps.
        set (L := fun x => exists i, i < length pre /\
                          Ensembles.In _ (nth i pre (Empty_set _)) x).
        assert (Hbar : fin_is_barrier R L Bk)
          by exact (fin_prefix_barrier R pre Bk Hpreneq Hpart).
        apply (fin_barrier_dim_le2 R Hfin L Bk Hbar).
        -- (* L sub-block dim <= 2: recurse *)
           apply (IHn {z | Ensembles.In _ L z}
                      (fin_sub_order R L)
                      (fin_sub_order_poset R L)
                      (fin_sub_order_finite R Hfin L)
                      (map (restrict_block L) pre)).
           ++ (* length bound *)
              rewrite length_map. exact Hlenpre.
           ++ (* partition of the L-subtype *)
              exact (fin_prefix_restricted_partition R pre Bk Hpart).
           ++ (* block dims in the L-subtype *)
              intros blk Hblk.
              apply in_map_iff in Hblk.
              destruct Hblk as [B [HBeq HBin]]. subst blk.
              assert (HBsub : forall x, Ensembles.In _ B x -> Ensembles.In _ L x).
              { apply In_nth with (d := Empty_set _) in HBin.
                destruct HBin as [i [Hi HBeq]].
                intros x HxB. exists i. split; [exact Hi|].
                rewrite HBeq. exact HxB. }
              destruct (Hblocks B) as [d [Hd Hle]].
              { apply in_or_app. left. exact HBin. }
              exists d. split.
              ** exact (restricted_block_dim2 R L B HBsub d Hd).
              ** exact Hle.
        -- (* Bk sub-block dim <= 2 *)
           apply (Hblocks Bk).
           apply in_or_app. right. left. reflexivity.
Qed.

Lemma fin_fully_sync_dim_le2 :
  forall {A : Type} (R : A -> A -> Prop) {HR : IsPoset A R}
         (Hfin : Finite A (Full_set A)) (blocks : list (Ensemble A)),
    fin_ordinal_partition R blocks ->
    (forall blk, List.In blk blocks ->
       exists d, inhabited (PosetDimension (fin_sub_order R blk) d) /\ d <= 2) ->
    (exists d, inhabited (PosetDimension R d) /\ d <= 2).
Proof.
  intros A R HR Hfin blocks Hpart Hblocks.
  exact (fin_fully_sync_dim_le2_aux (length blocks) A R HR Hfin blocks
           (le_n _) Hpart Hblocks).
Qed.
