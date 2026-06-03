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
