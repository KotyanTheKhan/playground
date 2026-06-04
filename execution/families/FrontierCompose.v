(* Composing two antichains by a frontier F : the bipartite poset compose_le F.
   Dichotomy (this file): non-crossing (threshold/Ferrers) F => dim <= 2;
   the S3 crown F (i<>j) => dim >= 3. Abstract poset-dimension theory. *)
From Stdlib Require Import List Arith Lia Fin Ensembles Finite_sets
                           Finite_sets_facts Constructive_sets Classical.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs CriticalPairs Theorems.
Import ListNotations.

Inductive Carrier (A B : Type) : Type := inA (a : A) | inB (b : B).
Arguments inA {A B} a. Arguments inB {A B} b.

Definition compose_le {A B} (F : A -> B -> Prop) (x y : Carrier A B) : Prop :=
  match x, y with
  | inA a, inA a' => a = a'
  | inB b, inB b' => b = b'
  | inA a, inB b  => F a b
  | inB _, inA _  => False
  end.

#[export] Instance compose_IsPoset {A B} (F : A -> B -> Prop) :
  IsPoset (Carrier A B) (compose_le F).
Proof.
  constructor.
  - intro x. destruct x; reflexivity.
  - intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl;
      intros Hxy Hyx; try (subst; reflexivity); try contradiction.
  - intros x y z; destruct x as [a|b]; destruct y as [a'|b']; destruct z as [a''|b''];
      simpl; intros Hxy Hyz; try contradiction; subst; try reflexivity; try assumption.
Qed.

Definition Ferrers {A B} (F : A -> B -> Prop) : Prop :=
  forall a1 a2 b1 b2, F a1 b1 -> F a2 b2 -> F a1 b2 \/ F a2 b1.

Lemma threshold_Ferrers :
  forall {A B} (phi : A -> nat) (psi : B -> nat) (F : A -> B -> Prop),
    (forall a b, F a b <-> phi a <= psi b) -> Ferrers F.
Proof.
  intros A B phi psi F Hthr a1 a2 b1 b2 H1 H2.
  apply Hthr in H1; apply Hthr in H2.
  destruct (Nat.le_ge_cases (phi a1) (phi a2)) as [Hle | Hge].
  - left.  apply Hthr. lia.
  - right. apply Hthr. lia.
Qed.

(* ===================================================================== *)
(* POSITIVE direction: a non-crossing (threshold) frontier preserves     *)
(* dim <= 2, via an explicit 2-realizer (M1, M2).                        *)
(* ===================================================================== *)

Definition idxF {m} (a : Fin.t m) : nat := proj1_sig (Fin.to_nat a).

Lemma idxF_inj {m} (a a' : Fin.t m) : idxF a = idxF a' -> a = a'.
Proof. unfold idxF. apply Fin.to_nat_inj. Qed.

Definition M1 {mA mB} (phi : Fin.t mA -> nat) (psi : Fin.t mB -> nat)
  (x y : Carrier (Fin.t mA) (Fin.t mB)) : Prop :=
  match x, y with
  | inA a, inA a' => phi a < phi a' \/ (phi a = phi a' /\ idxF a <= idxF a')
  | inB b, inB b' => psi b < psi b' \/ (psi b = psi b' /\ idxF b <= idxF b')
  | inA a, inB b  => phi a <= psi b
  | inB b, inA a  => psi b < phi a
  end.

Definition M2 {mA mB} (phi : Fin.t mA -> nat) (psi : Fin.t mB -> nat)
  (x y : Carrier (Fin.t mA) (Fin.t mB)) : Prop :=
  match x, y with
  | inA a, inA a' => phi a' < phi a \/ (phi a' = phi a /\ idxF a' <= idxF a)
  | inB b, inB b' => psi b' < psi b \/ (psi b' = psi b /\ idxF b' <= idxF b)
  | inA a, inB b  => True
  | inB b, inA a  => False
  end.

Theorem threshold_dim_le2 :
  forall {mA mB} (phi : Fin.t mA -> nat) (psi : Fin.t mB -> nat)
         (F : Fin.t mA -> Fin.t mB -> Prop),
    (forall a b, F a b <-> phi a <= psi b) ->
    forall d, PosetDimension (compose_le F) d -> d <= 2.
Proof.
  intros mA mB phi psi F Hthr d Hdim.
  set (R := compose_le F).
  set (L1 := M1 phi psi).
  set (L2 := M2 phi psi).
  (* ---- L1 is a linear extension of R ---- *)
  assert (HL1 : IsLinearExtension R L1).
  { constructor.
    - constructor.
      + constructor.
        * (* refl *) intro x; destruct x as [a|b]; simpl; right; split; reflexivity.
        * (* antisym *) intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl;
            intros Hxy Hyx.
          -- (* inA inA *)
             destruct Hxy as [Hlt1|[He1 Hi1]]; destruct Hyx as [Hlt2|[He2 Hi2]]; try lia.
             f_equal. apply idxF_inj. lia.
          -- (* inA inB *) exfalso; lia.
          -- (* inB inA *) exfalso; lia.
          -- (* inB inB *)
             destruct Hxy as [Hlt1|[He1 Hi1]]; destruct Hyx as [Hlt2|[He2 Hi2]]; try lia.
             f_equal. apply idxF_inj. lia.
        * (* trans *) intros x y z; destruct x as [a|b]; destruct y as [a'|b'];
            destruct z as [a''|b'']; simpl; intros Hxy Hyz;
            try (destruct Hxy as [Hxy|[Hxy ?]]); try (destruct Hyz as [Hyz|[Hyz ?]]);
            solve [ left; lia | right; split; lia | lia ].
      + (* total *) intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl.
        * destruct (lt_eq_lt_dec (phi a) (phi a')) as [[Hl|He]|Hg].
          -- left; left; exact Hl.
          -- destruct (Nat.le_ge_cases (idxF a) (idxF a')); [left|right]; right; split; lia.
          -- right; left; exact Hg.
        * destruct (Nat.le_gt_cases (phi a) (psi b')); [left|right]; lia.
        * destruct (Nat.le_gt_cases (phi a') (psi b)); [right|left]; lia.
        * destruct (lt_eq_lt_dec (psi b) (psi b')) as [[Hl|He]|Hg].
          -- left; left; exact Hl.
          -- destruct (Nat.le_ge_cases (idxF b) (idxF b')); [left|right]; right; split; lia.
          -- right; left; exact Hg.
    - (* extends *) intros x y Hr; unfold R, compose_le in Hr;
        destruct x as [a|b]; destruct y as [a'|b']; simpl.
      + subst a'; right; split; reflexivity.
      + apply Hthr; exact Hr.
      + contradiction.
      + subst b'; right; split; reflexivity. }
  (* ---- L2 is a linear extension of R ---- *)
  assert (HL2 : IsLinearExtension R L2).
  { constructor.
    - constructor.
      + constructor.
        * (* refl *) intro x; destruct x as [a|b]; simpl; right; split; reflexivity.
        * (* antisym *) intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl;
            intros Hxy Hyx.
          -- destruct Hxy as [Hlt1|[He1 Hi1]]; destruct Hyx as [Hlt2|[He2 Hi2]]; try lia.
             f_equal. apply idxF_inj. lia.
          -- contradiction.
          -- contradiction.
          -- destruct Hxy as [Hlt1|[He1 Hi1]]; destruct Hyx as [Hlt2|[He2 Hi2]]; try lia.
             f_equal. apply idxF_inj. lia.
        * (* trans *) intros x y z; destruct x as [a|b]; destruct y as [a'|b'];
            destruct z as [a''|b'']; simpl; intros Hxy Hyz;
            try exact I; try contradiction;
            try (destruct Hxy as [Hxy|[Hxy ?]]); try (destruct Hyz as [Hyz|[Hyz ?]]);
            solve [ left; lia | right; split; lia | lia ].
      + (* total *) intros x y; destruct x as [a|b]; destruct y as [a'|b']; simpl.
        * destruct (lt_eq_lt_dec (phi a') (phi a)) as [[Hl|He]|Hg].
          -- left; left; exact Hl.
          -- destruct (Nat.le_ge_cases (idxF a') (idxF a)); [left|right]; right; split; lia.
          -- right; left; exact Hg.
        * left; exact I.
        * right; exact I.
        * destruct (lt_eq_lt_dec (psi b') (psi b)) as [[Hl|He]|Hg].
          -- left; left; exact Hl.
          -- destruct (Nat.le_ge_cases (idxF b') (idxF b)); [left|right]; right; split; lia.
          -- right; left; exact Hg.
    - (* extends *) intros x y Hr; unfold R, compose_le in Hr;
        destruct x as [a|b]; destruct y as [a'|b']; simpl.
      + subst a'; right; split; reflexivity.
      + exact I.
      + contradiction.
      + subst b'; right; split; reflexivity. }
  (* ---- intersection characterization ---- *)
  assert (Hcap : forall x y, R x y <-> (L1 x y /\ L2 x y)).
  { intros x y; destruct x as [a|b]; destruct y as [a'|b']; unfold R, compose_le, L1, L2, M1, M2.
    - (* inA inA *) split.
      + intro Heq; subst a'; split; right; split; reflexivity.
      + intros [H1 H2].
        destruct H1 as [Hlt1|[He1 Hi1]]; destruct H2 as [Hlt2|[He2 Hi2]]; try lia.
        apply idxF_inj; lia.
    - (* inA inB *) split.
      + intro HF; split; [apply Hthr; exact HF | exact I].
      + intros [H1 _]; apply Hthr; exact H1.
    - (* inB inA *) split.
      + intro Hf; contradiction.
      + intros [_ H2]; contradiction.
    - (* inB inB *) split.
      + intro Heq; subst b'; split; right; split; reflexivity.
      + intros [H1 H2].
        destruct H1 as [Hlt1|[He1 Hi1]]; destruct H2 as [Hlt2|[He2 Hi2]]; try lia.
        apply idxF_inj; lia. }
  (* ---- the 2-element realizer ---- *)
  pose (T := Carrier (Fin.t mA) (Fin.t mB) -> Carrier (Fin.t mA) (Fin.t mB) -> Prop).
  pose (RS := fun L : T => L = L1 \/ L = L2).
  assert (HReal : IsRealizer R RS).
  { constructor.
    - intros L HL; unfold Ensembles.In, RS in HL; destruct HL as [-> | ->]; assumption.
    - intros x y. split.
      + intro Hxy. pose proof (proj1 (Hcap x y) Hxy) as [HA HB].
        intros L HL; unfold Ensembles.In, RS in HL; destruct HL as [-> | ->]; assumption.
      + intro Hall. apply (proj2 (Hcap x y)). split;
          [ apply (Hall L1) | apply (Hall L2) ];
          unfold Ensembles.In, RS; [left | right]; reflexivity. }
  (* ---- cardinality of the realizer <= 2 ---- *)
  assert (Hcard : exists nc, cardinal T RS nc /\ nc <= 2).
  { destruct (classic (L1 = L2)) as [Heq | Hne].
    - exists 1. split; [|lia].
      assert (Hset : RS = Ensembles.Add T (Ensembles.Empty_set T) L1).
      { apply Extensionality_Ensembles; split; intros L HL; unfold Ensembles.In, RS in *.
        * destruct HL as [-> | ->]; [right; constructor | rewrite <- Heq; right; constructor].
        * destruct HL as [L' HL'|L' HL']; [destruct HL' | apply Singleton_inv in HL'; left; symmetry; exact HL']. }
      rewrite Hset. apply card_add; [apply card_empty | intro Hb; destruct Hb].
    - exists 2. split; [|lia].
      assert (Hset : RS = Ensembles.Add T (Ensembles.Add T (Ensembles.Empty_set T) L1) L2).
      { apply Extensionality_Ensembles; split; intros L HL; unfold Ensembles.In, RS in *.
        * destruct HL as [He | He]; subst L; [left; right; constructor | right; constructor].
        * destruct HL as [L' [L'' HL''|L'' HL'']|L' HL'];
            [ destruct HL'' | apply Singleton_inv in HL''; left; symmetry; exact HL''
            | apply Singleton_inv in HL'; right; symmetry; exact HL' ]. }
      rewrite Hset. apply card_add;
        [ apply card_add; [apply card_empty | intro Hb; destruct Hb]
        | intro Hb; destruct Hb as [L' Hb|L' Hb]; [destruct Hb | apply Singleton_inv in Hb; apply Hne; exact Hb] ]. }
  destruct Hcard as [nc [Hnc Hnc2]].
  pose proof (dimension_is_minimum Hdim RS nc HReal Hnc) as Hle. lia.
Qed.

(* ===================================================================== *)
(* NEGATIVE direction: the S3 crown frontier (i <> j) forces dim >= 3.    *)
(* ===================================================================== *)

Definition crownF (a b : Fin.t 3) : Prop := a <> b.
Definition crown3 : Carrier (Fin.t 3) (Fin.t 3) -> Carrier (Fin.t 3) (Fin.t 3) -> Prop
  := compose_le crownF.

#[export] Instance crown3_IsPoset : IsPoset (Carrier (Fin.t 3) (Fin.t 3)) crown3
  := compose_IsPoset crownF.

(* The three concrete elements of [Fin.t 3]. *)
Definition c0 : Fin.t 3 := Fin.F1.
Definition c1 : Fin.t 3 := Fin.FS Fin.F1.
Definition c2 : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

Lemma fin3_cases : forall i : Fin.t 3, i = c0 \/ i = c1 \/ i = c2.
Proof.
  intro i.
  apply (Fin.caseS' i); [ left; reflexivity | intro p ].
  apply (Fin.caseS' p); [ right; left; reflexivity | intro q ].
  apply (Fin.caseS' q); [ right; right; reflexivity | intro r ].
  exact (Fin.case0 (fun _ => _) r).
Qed.

(* The six carrier elements; the carrier is finite. *)
Lemma crown_carrier_finite :
  Finite (Carrier (Fin.t 3) (Fin.t 3)) (Full_set (Carrier (Fin.t 3) (Fin.t 3))).
Proof.
  set (E := Carrier (Fin.t 3) (Fin.t 3)).
  set (six :=
    Add E (Add E (Add E (Add E (Add E (Add E (Empty_set E)
      (inA c0)) (inA c1)) (inA c2)) (inB c0)) (inB c1)) (inB c2)).
  assert (Heq : Full_set E = six).
  { apply Extensionality_Ensembles; split.
    - intros x _. unfold six, E.
      destruct x as [a|b].
      + destruct (fin3_cases a) as [-> | [-> | ->]].
        * left; left; left; left; left; right; constructor. (* inA c0: layer1, 5 left *)
        * left; left; left; left; right; constructor.       (* inA c1: layer2, 4 left *)
        * left; left; left; right; constructor.             (* inA c2: layer3, 3 left *)
      + destruct (fin3_cases b) as [-> | [-> | ->]].
        * left; left; right; constructor.                   (* inB c0: layer4, 2 left *)
        * left; right; constructor.                         (* inB c1: layer5, 1 left *)
        * right; constructor.                               (* inB c2: layer6, 0 left *)
    - intros x _. constructor. }
  rewrite Heq. unfold six.
  repeat (apply Add_preserves_Finite). apply Empty_is_finite.
Qed.

Lemma crown_critical : forall i : Fin.t 3, IsCriticalPair crown3 (inA i) (inB i).
Proof.
  intro i. constructor.
  - (* incomparable: ~ (crown3 (inA i)(inB i) \/ crown3 (inB i)(inA i)) *)
    unfold crown3, compose_le, crownF. intros [H|H]; [ exact (H eq_refl) | exact H ].
  - (* down: vacuous *)
    intros a [Hle Hne]. destruct a as [a'|b']; simpl in Hle.
    + subst a'. exfalso; apply Hne; reflexivity.
    + contradiction.
  - (* up: vacuous *)
    intros b [Hle Hne]. destruct b as [a'|b']; simpl in Hle.
    + contradiction.
    + subst b'. exfalso; apply Hne; reflexivity.
Qed.

Lemma crown_alt_cycle : forall i j : Fin.t 3, i <> j ->
  IsAlternatingCycle crown3 [(inA i, inB i); (inA j, inB j)].
Proof.
  intros i j Hij. unfold IsAlternatingCycle. split.
  - intros p [<-|[<-|[]]]; simpl; apply crown_critical.
  - simpl. split; [ exact (fun H => Hij (eq_sym H)) | exact Hij ].
Qed.

Theorem crown3_dim_ge_3 : forall d, PosetDimension crown3 d -> 3 <= d.
Proof.
  intros d Hdim.
  set (r := dimension_realizer Hdim).
  pose proof (dimension_is_realizer Hdim) as HR.
  pose proof (dimension_cardinality Hdim) as Hcard.
  set (E := Carrier (Fin.t 3) (Fin.t 3)).
  (* ---- r is inhabited ---- *)
  assert (Hinhab : Inhabited (E -> E -> Prop) r).
  { destruct (classic (forall L, In (E -> E -> Prop) r L -> L (inA c0) (inB c0)))
      as [Hall | Hnall].
    - (* if every L put inA c0 <= inB c0 then crown3 would hold; but it's False *)
      exfalso.
      assert (Hfalse : crown3 (inA c0) (inB c0)).
      { apply (proj2 (realizer_intersection HR (inA c0) (inB c0))). exact Hall. }
      unfold crown3, compose_le, crownF in Hfalse. exact (Hfalse eq_refl).
    - apply not_all_ex_not in Hnall. destruct Hnall as [L HL].
      apply imply_to_and in HL. destruct HL as [HLin _].
      exact (Inhabited_intro _ _ L HLin). }
  (* ---- per-pair reverser ---- *)
  pose proof (proj1 (critical_pair_realizer_iff crown3 crown_carrier_finite
                       r Hinhab (realizer_linear HR)) HR) as Hrev.
  destruct (Hrev (inA c0) (inB c0) (crown_critical c0)) as [L0 [HL0in HL0rev]].
  destruct (Hrev (inA c1) (inB c1) (crown_critical c1)) as [L1 [HL1in HL1rev]].
  destruct (Hrev (inA c2) (inB c2) (crown_critical c2)) as [L2 [HL2in HL2rev]].
  (* ---- distinctness of L0, L1, L2 ---- *)
  assert (Hdistinct : forall (i j : Fin.t 3) (Li Lj : E -> E -> Prop),
            i <> j ->
            In (E -> E -> Prop) r Li -> Li (inB i) (inA i) ->
            In (E -> E -> Prop) r Lj -> Lj (inB j) (inA j) ->
            Li <> Lj).
  { intros i j Li Lj Hij HLiin HLirev HLjin HLjrev Heq.
    set (S := fun p : E * E => p = (inA i, inB i) \/ p = (inA j, inB j)).
    assert (HS : forall p, In (E * E) S p -> IsCriticalPair crown3 (fst p) (snd p)).
    { intros [x y] [Hp|Hp]; injection Hp as -> ->; simpl; apply crown_critical. }
    pose proof (proj1 (critical_pairs_reversible_iff_no_alternating_cycle
                         crown3 S HS)) as Hfwd.
    apply Hfwd.
    - exists Li. split.
      + exact (realizer_linear HR Li HLiin).
      + intros x y [Hp|Hp]; injection Hp as -> ->.
        * exact HLirev.
        * rewrite Heq. exact HLjrev.
    - exists [(inA i, inB i); (inA j, inB j)]. split.
      + intros p [<-|[<-|[]]]; [ left | right ]; reflexivity.
      + exact (crown_alt_cycle i j Hij). }
  assert (Hc01 : c0 <> c1) by discriminate.
  assert (Hc02 : c0 <> c2) by discriminate.
  assert (Hc12 : c1 <> c2) by discriminate.
  assert (Hne01 : L0 <> L1) by (apply (Hdistinct c0 c1); assumption).
  assert (Hne02 : L0 <> L2) by (apply (Hdistinct c0 c2); assumption).
  assert (Hne12 : L1 <> L2) by (apply (Hdistinct c1 c2); assumption).
  (* ---- pigeonhole: 3 distinct linear extensions => 3 <= d ---- *)
  set (Three := Add (E -> E -> Prop)
                  (Add (E -> E -> Prop)
                     (Add (E -> E -> Prop) (Empty_set (E -> E -> Prop)) L0) L1) L2).
  assert (HcardThree : cardinal (E -> E -> Prop) Three 3).
  { unfold Three. apply card_add.
    - apply card_add.
      + apply card_add; [ apply card_empty | intro Hb; destruct Hb ].
      + intro Hb. destruct Hb as [L' Hb | L' Hb].
        * destruct Hb.
        * apply Singleton_inv in Hb. apply Hne01; congruence.
    - intro Hb. destruct Hb as [L' [L'' Hb | L'' Hb] | L' Hb].
      + destruct Hb.
      + apply Singleton_inv in Hb. apply Hne02; congruence.
      + apply Singleton_inv in Hb. apply Hne12; congruence. }
  assert (HincThree : Included (E -> E -> Prop) Three r).
  { unfold Three. intros M HM.
    destruct HM as [M HM2 | M Hb].
    - destruct HM2 as [M HM1 | M Hb].
      + destruct HM1 as [M HM0 | M Hb].
        * destruct HM0.
        * apply Singleton_inv in Hb; subst; exact HL0in.
      + apply Singleton_inv in Hb; subst; exact HL1in.
    - apply Singleton_inv in Hb; subst; exact HL2in. }
  exact (incl_card_le (E -> E -> Prop) Three r 3 d HcardThree Hcard HincThree).
Qed.

(* the crown poset HAS a dimension (Dushnik-Miller, finite carrier) ... *)
Lemma crown3_dim_exists : exists d, inhabited (PosetDimension crown3 d).
Proof.
  destruct (finite_cardinal _ _ crown_carrier_finite) as [n Hn].
  exact (dushnik_miller_exists crown3 n Hn).
Qed.

(* ... and it is at least 3: connecting two 3-antichains by the S3 crown frontier
   raises dimension from 2 to >= 3 (closed, unconditional). *)
Lemma crown3_dim_ge_3_closed : exists d, inhabited (PosetDimension crown3 d) /\ 3 <= d.
Proof.
  destruct crown3_dim_exists as [d [Hd]].
  exists d. split; [ exact (inhabits Hd) | exact (crown3_dim_ge_3 d Hd) ].
Qed.
