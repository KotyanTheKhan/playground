From Stdlib Require Import Fin List Arith Lia Ensembles Finite_sets Finite_sets_facts Constructive_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs Theorems.
Import ListNotations.

(* ===================================================================== *)
(*  Step 1: decidable forall over Fin.t n                                *)
(* ===================================================================== *)

Fixpoint all_finT (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S m => Fin.F1 :: List.map (fun x => Fin.FS x) (all_finT m)
  end.

Lemma all_finT_complete : forall n (x : Fin.t n), List.In x (all_finT n).
Proof.
  induction n; intro x.
  - inversion x.
  - apply (Fin.caseS' x).
    + left; reflexivity.
    + intro p. right. apply List.in_map. apply IHn.
Qed.

Definition forallb_finT {n} (f : Fin.t n -> bool) : bool :=
  List.forallb f (all_finT n).

Lemma forallb_finT_spec {n} (f : Fin.t n -> bool) :
  forallb_finT f = true <-> forall x, f x = true.
Proof.
  unfold forallb_finT. rewrite List.forallb_forall. split.
  - intros H x. apply H. apply all_finT_complete.
  - intros H x _. apply H.
Qed.

Definition forallb_finT2 {n} (f : Fin.t n -> Fin.t n -> bool) : bool :=
  forallb_finT (fun x => forallb_finT (fun y => f x y)).

Lemma forallb_finT2_spec {n} (f : Fin.t n -> Fin.t n -> bool) :
  forallb_finT2 f = true <-> forall x y, f x y = true.
Proof.
  unfold forallb_finT2. rewrite forallb_finT_spec. split.
  - intros H x y. specialize (H x). rewrite forallb_finT_spec in H. apply H.
  - intros H x. apply forallb_finT_spec. intro y. apply H.
Qed.

Definition forallb_finT3 {n} (f : Fin.t n -> Fin.t n -> Fin.t n -> bool) : bool :=
  forallb_finT (fun x => forallb_finT2 (fun y z => f x y z)).

Lemma forallb_finT3_spec {n} (f : Fin.t n -> Fin.t n -> Fin.t n -> bool) :
  forallb_finT3 f = true <-> forall x y z, f x y z = true.
Proof.
  unfold forallb_finT3. rewrite forallb_finT_spec. split.
  - intros H x y z. specialize (H x). rewrite forallb_finT2_spec in H. apply H.
  - intros H x. apply forallb_finT2_spec. intros y z. apply H.
Qed.

(* ===================================================================== *)
(*  Finiteness of the full Fin.t n carrier (needed for Dushnik-Miller)   *)
(* ===================================================================== *)

(* The full set of Fin.t n equals the image (as an ensemble) of the
   enumeration list [all_finT n].  We build [Finite] by induction on the
   list, mirroring how crown3 enumerates its carrier with [Add]. *)

Definition list_to_set {A} (l : list A) : Ensemble A :=
  fun x => List.In x l.

Lemma list_to_set_finite {A} (l : list A) :
  Finite A (list_to_set l).
Proof.
  induction l as [|a l IH].
  - replace (list_to_set []) with (Empty_set A).
    + apply Empty_is_finite.
    + apply Extensionality_Ensembles; split.
      * intros x Hx. destruct Hx.
      * intros x Hx. destruct Hx.
  - destruct (classic (List.In a l)) as [Hin | Hnin].
    + replace (list_to_set (a :: l)) with (list_to_set l).
      * exact IH.
      * apply Extensionality_Ensembles; split.
        -- intros x Hx. right. exact Hx.
        -- intros x [Heq | Hx]; [ subst; exact Hin | exact Hx ].
    + replace (list_to_set (a :: l)) with (Add A (list_to_set l) a).
      * apply Add_preserves_Finite. exact IH.
      * apply Extensionality_Ensembles; split.
        -- intros x [x' Hx' | x' Hx'].
           ++ right. exact Hx'.
           ++ apply Singleton_inv in Hx'. left. exact Hx'.
        -- intros x [Heq | Hx].
           ++ right. subst x. apply In_singleton.
           ++ left. exact Hx.
Qed.

Lemma finT_full_finite : forall n,
  Finite (Fin.t n) (Full_set (Fin.t n)).
Proof.
  intro n.
  replace (Full_set (Fin.t n)) with (list_to_set (all_finT n)).
  - apply list_to_set_finite.
  - apply Extensionality_Ensembles; split.
    + intros x _. constructor.
    + intros x _. apply all_finT_complete.
Qed.

(* ===================================================================== *)
(*  Step 3: the reflection bridge                                        *)
(* ===================================================================== *)

Section Bridge.
  Context {n : nat}.
  Context (Rb : Fin.t n -> Fin.t n -> bool).
  Context (k1 k2 : Fin.t n -> nat).

  Definition Rrel (x y : Fin.t n) : Prop := Rb x y = true.
  Definition Lk (k : Fin.t n -> nat) (x y : Fin.t n) : Prop := k x <= k y.

  Context (HPoset : IsPoset (Fin.t n) Rrel).
  Context (Hinj1 : forall x y, k1 x = k1 y -> x = y).
  Context (Hinj2 : forall x y, k2 x = k2 y -> x = y).
  Context (Hext : forall x y, Rb x y = true -> k1 x <= k1 y /\ k2 x <= k2 y).
  Context (Hint : forall x y, k1 x <= k1 y -> k2 x <= k2 y -> Rb x y = true).
  Context (Hdiff : exists x y, k1 x <= k1 y /\ ~ (k2 x <= k2 y)).

  #[local] Existing Instance HPoset.

  (* Each key order Lk is a linear extension of Rrel, given that key k is
     monotone along Rb. *)
  Lemma Lk_linext (k : Fin.t n -> nat)
        (Hinj : forall x y, k x = k y -> x = y)
        (Hmono : forall x y, Rb x y = true -> k x <= k y) :
    IsLinearExtension Rrel (Lk k).
  Proof.
    constructor.
    - (* IsTotalOrder *)
      constructor.
      + (* IsPoset (Lk k) *)
        constructor.
        * intro x. unfold Lk. lia.
        * intros x y Hxy Hyx. unfold Lk in *. apply Hinj. lia.
        * intros x y z Hxy Hyz. unfold Lk in *. lia.
      + (* total_comparable *)
        intros x y. unfold Lk. lia.
    - (* linear_extends *)
      intros x y HR. unfold Rrel in HR. unfold Lk. apply Hmono. exact HR.
  Qed.

  Definition realizer2 : Ensemble (Fin.t n -> Fin.t n -> Prop) :=
    fun L => L = Lk k1 \/ L = Lk k2.

  Lemma realizer2_isrealizer : IsRealizer Rrel realizer2.
  Proof.
    constructor.
    - (* realizer_linear *)
      intros L HL. destruct HL as [-> | ->].
      + apply (Lk_linext k1 Hinj1). intros x y H. apply (Hext x y H).
      + apply (Lk_linext k2 Hinj2). intros x y H. apply (Hext x y H).
    - (* realizer_intersection *)
      intros x y. split.
      + intros HR L HL. destruct HL as [-> | ->].
        * apply (linear_extends (Lk_linext k1 Hinj1 (fun a b h => proj1 (Hext a b h)))). exact HR.
        * apply (linear_extends (Lk_linext k2 Hinj2 (fun a b h => proj2 (Hext a b h)))). exact HR.
      + intros Hall. unfold Rrel.
        assert (HL1 : Lk k1 x y).
        { apply Hall. left. reflexivity. }
        assert (HL2 : Lk k2 x y).
        { apply Hall. right. reflexivity. }
        unfold Lk in HL1, HL2. apply Hint; assumption.
  Qed.

  (* The two key orders are distinct, witnessed by Hdiff. *)
  Lemma Lk_distinct : Lk k1 <> Lk k2.
  Proof.
    destruct Hdiff as [x [y [Hle Hnle]]].
    intro Heq.
    assert (Hk2 : Lk k2 x y).
    { rewrite <- Heq. unfold Lk. exact Hle. }
    unfold Lk in Hk2. contradiction.
  Qed.

  Lemma realizer2_card2 : cardinal (Fin.t n -> Fin.t n -> Prop) realizer2 2.
  Proof.
    set (T := Fin.t n -> Fin.t n -> Prop).
    replace realizer2
      with (Add T (Add T (Empty_set T) (Lk k1)) (Lk k2)).
    - apply card_add.
      + apply card_add.
        * apply card_empty.
        * intro Hb. destruct Hb.
      + intro Hb. apply Add_inv in Hb. destruct Hb as [Hb | Hb].
        * destruct Hb.
        * apply Lk_distinct. exact Hb.
    - apply Extensionality_Ensembles; split.
      + intros L HL. destruct HL as [L HL | L HL].
        * destruct HL as [L HL | L HL].
          -- destruct HL.
          -- apply Singleton_inv in HL. left. symmetry. exact HL.
        * apply Singleton_inv in HL. right. symmetry. exact HL.
      + intros L [-> | ->].
        * left. right. apply In_singleton.
        * right. apply In_singleton.
  Qed.

  Theorem realizer_keys_dim_le2 :
    exists d, inhabited (PosetDimension Rrel d) /\ d <= 2.
  Proof.
    destruct (finite_cardinal _ _ (finT_full_finite n)) as [m Hm].
    destruct (dushnik_miller_exists Rrel m Hm) as [d [Hd]].
    exists d. split.
    - exact (inhabits Hd).
    - apply (dimension_is_minimum Hd realizer2 2).
      + exact realizer2_isrealizer.
      + exact realizer2_card2.
  Qed.

End Bridge.

(* ===================================================================== *)
(*  Step 4: proof-of-concept on the 4-element 2-chain (0<1, 2<3)         *)
(* ===================================================================== *)

Module TwoChainPOC.

  Definition Rb4 (x y : Fin.t 4) : bool :=
    match proj1_sig (Fin.to_nat x), proj1_sig (Fin.to_nat y) with
    | 0,0|1,1|2,2|3,3|0,1|2,3 => true | _,_ => false end.

  Definition k1 (x : Fin.t 4) : nat :=
    match proj1_sig (Fin.to_nat x) with 0=>0|1=>1|2=>2|3=>3|_=>0 end.

  Definition k2 (x : Fin.t 4) : nat :=
    match proj1_sig (Fin.to_nat x) with 0=>2|1=>3|2=>0|3=>1|_=>0 end.

  (* IsPoset laws by boolean reflection. *)
  Lemma Rb4_refl : forall x, Rb4 x x = true.
  Proof.
    apply forallb_finT_spec. vm_compute. reflexivity.
  Qed.

  Lemma Rb4_antisym : forall x y, Rb4 x y = true -> Rb4 y x = true -> x = y.
  Proof.
    intros x y Hxy Hyx.
    assert (Hdec : forall x y : Fin.t 4,
      implb (Rb4 x y && Rb4 y x) (Fin.eqb x y) = true).
    { apply forallb_finT2_spec. vm_compute. reflexivity. }
    apply Fin.eqb_eq.
    specialize (Hdec x y). rewrite Hxy, Hyx in Hdec. exact Hdec.
  Qed.

  Lemma Rb4_trans : forall x y z,
    Rb4 x y = true -> Rb4 y z = true -> Rb4 x z = true.
  Proof.
    intros x y z Hxy Hyz.
    assert (Htr : forall x y z : Fin.t 4,
      implb (Rb4 x y && Rb4 y z) (Rb4 x z) = true).
    { apply forallb_finT3_spec. vm_compute. reflexivity. }
    specialize (Htr x y z). rewrite Hxy, Hyz in Htr. exact Htr.
  Qed.

  Instance Rb4_IsPoset : IsPoset (Fin.t 4) (fun x y => Rb4 x y = true).
  Proof.
    constructor.
    - exact Rb4_refl.
    - exact Rb4_antisym.
    - exact Rb4_trans.
  Qed.

  (* Injectivity of each key by reflection. *)
  Lemma k1_inj : forall x y, k1 x = k1 y -> x = y.
  Proof.
    intros x y H.
    assert (Hdec : forall x y : Fin.t 4,
      implb (Nat.eqb (k1 x) (k1 y)) (Fin.eqb x y) = true).
    { apply forallb_finT2_spec. vm_compute. reflexivity. }
    apply Fin.eqb_eq. specialize (Hdec x y).
    rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
  Qed.

  Lemma k2_inj : forall x y, k2 x = k2 y -> x = y.
  Proof.
    intros x y H.
    assert (Hdec : forall x y : Fin.t 4,
      implb (Nat.eqb (k2 x) (k2 y)) (Fin.eqb x y) = true).
    { apply forallb_finT2_spec. vm_compute. reflexivity. }
    apply Fin.eqb_eq. specialize (Hdec x y).
    rewrite (proj2 (Nat.eqb_eq _ _) H) in Hdec. exact Hdec.
  Qed.

  (* Monotone extension: Rb4 x y = true -> k1 x <= k1 y /\ k2 x <= k2 y. *)
  Lemma ext_keys : forall x y,
    Rb4 x y = true -> k1 x <= k1 y /\ k2 x <= k2 y.
  Proof.
    intros x y H.
    assert (Hb : forall x y : Fin.t 4,
      implb (Rb4 x y) (Nat.leb (k1 x) (k1 y) && Nat.leb (k2 x) (k2 y)) = true).
    { apply forallb_finT2_spec. vm_compute. reflexivity. }
    specialize (Hb x y). rewrite H in Hb. simpl in Hb.
    apply andb_prop in Hb. destruct Hb as [H1 H2].
    split; apply Nat.leb_le; assumption.
  Qed.

  (* Intersection: k1 x <= k1 y -> k2 x <= k2 y -> Rb4 x y = true. *)
  Lemma int_keys : forall x y,
    k1 x <= k1 y -> k2 x <= k2 y -> Rb4 x y = true.
  Proof.
    intros x y H1 H2.
    assert (Hb : forall x y : Fin.t 4,
      implb (Nat.leb (k1 x) (k1 y) && Nat.leb (k2 x) (k2 y)) (Rb4 x y) = true).
    { apply forallb_finT2_spec. vm_compute. reflexivity. }
    specialize (Hb x y).
    rewrite (proj2 (Nat.leb_le _ _) H1), (proj2 (Nat.leb_le _ _) H2) in Hb.
    simpl in Hb. exact Hb.
  Qed.

  Theorem poc_dim_le2 :
    exists d, inhabited (PosetDimension
       (fun x y => Rb4 x y = true) d) /\ d <= 2.
  Proof.
    apply (realizer_keys_dim_le2 Rb4 k1 k2).
    - exact Rb4_IsPoset.
    - exact k1_inj.
    - exact k2_inj.
    - exact ext_keys.
    - exact int_keys.
    - (* Hdiff: pick element 0 (key1=0,key2=2) and element 2 (key1=2,key2=0):
         k1 0 = 0 <= k1 2 = 2 but ~ (k2 0 = 2 <= k2 2 = 0). *)
      exists Fin.F1, (Fin.FS (Fin.FS Fin.F1)).
      vm_compute. split; lia.
  Qed.

End TwoChainPOC.
