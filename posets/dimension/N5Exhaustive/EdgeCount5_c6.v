(** Count-5 iso-class pattern 6 for the n=5 dispatcher.  Auto-generated. *)

From Stdlib Require Import List Classical Arith Lia.
From Stdlib Require Import ClassicalDescription.
From Posets Require Import PosetClasses.
From Dimension Require Import DimDefs N5Realizers.
From Dimension.N5Exhaustive Require Import EdgeCount EdgeCount8_cover EdgeCount8_eccov.
From ZornsLemma Require Import EnsemblesExplicit.
From Stdlib Require Import Ensembles Finite_sets Finite_sets_facts.

Section EdgeCount5_c6.
  Context {B : Type}.
  Context (R2 : B -> B -> Prop) `{HR2 : IsPoset B R2}.

  Lemma n5_edge_count_5_c6 :
    cardinal B (Full_set B) 5 ->
    forall (a b c d e : B),
      a <> b -> a <> c -> a <> d -> a <> e ->
      b <> c -> b <> d -> b <> e ->
      c <> d -> c <> e -> d <> e ->
      (forall x : B, x = a \/ x = b \/ x = c \/ x = d \/ x = e) ->
      edge_count_5 R2 a b c d e = 5 ->
      forall (p q r s t : B),
        p <> q -> p <> r -> p <> s -> p <> t ->
        q <> r -> q <> s -> q <> t -> r <> s -> r <> t -> s <> t ->
        R2 p q -> R2 p r -> R2 q r -> R2 s r -> R2 s t ->
        exists rl : Ensemble (B -> B -> Prop),
          IsRealizer R2 rl /\ cardinal (B -> B -> Prop) rl 2.
  Proof.
    intros Hcard a b c d e
           Hab Hac Had Hae Hbc Hbd Hbe Hcd Hce Hde Hcov Hec
           p q r s t
           Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst
           HRpq HRpr HRqr HRsr HRst.
    pose proof (five_distinct_cover p q r s t Hcard
                  Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst) as Hcovpt.
    assert (Hec' : edge_count_5 R2 p q r s t = 5).
    { rewrite <- (edge_count_5_cover_invariant R2 a b c d e p q r s t Hcov
                    Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst). exact Hec. }
    assert (HR_only : forall x y, R2 x y -> x <> y -> (x = p /\ y = q) \/ (x = p /\ y = r) \/ (x = q /\ y = r) \/ (x = s /\ y = r) \/ (x = s /\ y = t)).
    { intros x y HRxy Hxyne.
      assert (strict_indicator R2 p q = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      assert (strict_indicator R2 p r = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      assert (strict_indicator R2 q r = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      assert (strict_indicator R2 s r = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      assert (strict_indicator R2 s t = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      assert (strict_indicator R2 x y = 1) by (apply strict_indicator_eq_1; (assumption || congruence)).
      unfold edge_count_5 in Hec'.
      destruct (Hcovpt x) as [Hx|[Hx|[Hx|[Hx|Hx]]]];
      destruct (Hcovpt y) as [Hy|[Hy|[Hy|[Hy|Hy]]]];
      subst; try (exfalso; congruence);
      try (left; split; reflexivity);
      try (right; left; split; reflexivity);
      try (right; right; left; split; reflexivity);
      try (right; right; right; left; split; reflexivity);
      try (right; right; right; right; split; reflexivity);
      try lia. }
    set (rk1 := fun z : B =>
      if excluded_middle_informative (z = p) then 0
      else if excluded_middle_informative (z = q) then 1
      else if excluded_middle_informative (z = r) then 3
      else if excluded_middle_informative (z = s) then 2 else 4).
    set (rk2 := fun z : B =>
      if excluded_middle_informative (z = p) then 2
      else if excluded_middle_informative (z = q) then 3
      else if excluded_middle_informative (z = r) then 4
      else if excluded_middle_informative (z = s) then 0 else 1).
    assert (V1p : rk1 p = 0) by (unfold rk1; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V1q : rk1 q = 1) by (unfold rk1; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V1r : rk1 r = 3) by (unfold rk1; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V1s : rk1 s = 2) by (unfold rk1; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V1t : rk1 t = 4) by (unfold rk1; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V2p : rk2 p = 2) by (unfold rk2; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V2q : rk2 q = 3) by (unfold rk2; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V2r : rk2 r = 4) by (unfold rk2; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V2s : rk2 s = 0) by (unfold rk2; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    assert (V2t : rk2 t = 1) by (unfold rk2; repeat (destruct (excluded_middle_informative _); [solve [reflexivity | exfalso; congruence] | ]); solve [reflexivity | exfalso; congruence]).
    apply (n5_two_realizer_framework R2 p q r s t
             Hpq Hpr Hps Hpt Hqr Hqs Hqt Hrs Hrt Hst Hcovpt rk1 rk2).
    all: try (rewrite ?V1p, ?V1q, ?V1r, ?V1s, ?V1t, ?V2p, ?V2q, ?V2r, ?V2s, ?V2t;
              intro Heq; lia).
    - intros u v HR. destruct (classic (u = v)) as [E|Hne]; [subst; apply le_n|].
      destruct (HR_only u v HR Hne) as [[Hu Hv]|[[Hu Hv]|[[Hu Hv]|[[Hu Hv]|[Hu Hv]]]]];
        subst; rewrite ?V1p, ?V1q, ?V1r, ?V1s, ?V1t; lia.
    - intros u v HR. destruct (classic (u = v)) as [E|Hne]; [subst; apply le_n|].
      destruct (HR_only u v HR Hne) as [[Hu Hv]|[[Hu Hv]|[[Hu Hv]|[[Hu Hv]|[Hu Hv]]]]];
        subst; rewrite ?V2p, ?V2q, ?V2r, ?V2s, ?V2t; lia.
    - intros u v H1 H2.
      destruct (Hcovpt u) as [Hu|[Hu|[Hu|[Hu|Hu]]]];
      destruct (Hcovpt v) as [Hv|[Hv|[Hv|[Hv|Hv]]]];
        subst;
        first [ assumption | apply poset_refl
              | exfalso;
                rewrite ?V1p, ?V1q, ?V1r, ?V1s, ?V1t in H1;
                rewrite ?V2p, ?V2q, ?V2r, ?V2s, ?V2t in H2; lia ].
    - exists p, s. rewrite V1p, V1s, V2p, V2s. split; lia.
  Qed.

End EdgeCount5_c6.
