(* Poset instance for happened-before relation *)
Require Import Posets.PosetClasses.
Require Import EventStructure.
Require Import CausalRelation.
From Stdlib Require Import Lia.

(* ========== Helper Lemmas ========== *)
Require Import CausalRelationProps.

(* ========== Poset Instance ========== *)

(* Happened-before is a partial order (poset) *)
Instance happened_before_poset (h : History) : IsPoset Event (happened_before h).
Proof.
  constructor.
  - (* reflexivity *)
    intro e. apply hb_refl.
  - (* antisymmetry *)
    intros e1 e2 H1 H2.
    (* Induction on H1 *)
    induction H1 as [e | e1 e2 Hlocal | e1 e2 Hmsg | e1 e2 e3 Hhb12 IH1 Hhb23 IH2].
    + (* hb_refl: e = e1 = e2 *)
      reflexivity.
    + (* hb_local: same_process_before e1 e2 *)
      exfalso.
      eapply same_process_before_no_hb_back; eauto.
    + (* hb_message: message_link h e1 e2 *)
      exfalso.
      eapply message_link_no_hb_back; eauto.
    + (* hb_trans: e1 ≺ e2 ≺ e3, and we have e3 ≺ e1 *)
      (* We have IH1: e2 ≺ e1 -> e1 = e2
         and IH2: e3 ≺ e1 -> e2 = e3
         From e2 ≺ e3 and e3 ≺ e1, we get e2 ≺ e1 by transitivity *)
      assert (Hbe21 : happened_before h e2 e1).
      { eapply hb_trans; eauto. }
      (* Apply IH1 to get e1 = e2 *)
      specialize (IH1 Hbe21).
      subst e2.
      (* Now we have e1 ≺ e3 and e3 ≺ e1, apply IH2 *)
      apply IH2.
      exact H2.
  - (* transitivity *)
    intros e1 e2 e3 H1 H2.
    apply hb_trans with e2; assumption.
Qed.
