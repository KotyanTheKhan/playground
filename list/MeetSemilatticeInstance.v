(* Meet semilattice instance for lists *)
Require Import Posets.PosetClasses.
Require Import Posets.LatticeClasses.
Require Import Structure.
Require Import Operations.
Require Import Helpers.
From Hammer Require Import Hammer.

Instance list_meet_semilattice : IsMeetSemilattice List list_meet.
Proof.
  constructor.
  - (* meet_assoc *)
    intros x y z. unfold list_meet.
    destruct (list_leb x y) eqn:Exy;
    destruct (list_leb y z) eqn:Eyz;
    destruct (list_leb x z) eqn:Exz.
    + (* x ≤ y, y ≤ z, x ≤ z *)
      hauto lq:on.
    + (* x ≤ y, y ≤ z, ¬(x ≤ z) - IMPOSSIBLE *)
      exfalso. apply (list_leb_trans x y z) in Exy; auto. rewrite Exy in Exz. discriminate.
    + (* x ≤ y, ¬(y ≤ z), x ≤ z *)
      hauto lq:on.
    + (* x ≤ y, ¬(y ≤ z), ¬(x ≤ z) *)
      destruct (list_leb z y) eqn:Ezy.
      * (* z ≤ y - then we have x ≤ y and z ≤ y, so need to compare x and z *)
        destruct (list_leb z x) eqn:Ezx.
        -- (* z ≤ x ≤ y, so min(min(x,y),z) = min(x,z) = z and min(x,min(y,z)) = min(x,z) = z *)
           hauto lq:on.
        -- (* x < z ≤ y contradicts ¬(x ≤ z) *)
           exfalso. destruct (list_leb_total x z) as [H | H]; rewrite H in *; discriminate.
      * hauto lq:on.
    + (* ¬(x ≤ y), y ≤ z, x ≤ z *)
      destruct (list_leb y x) eqn:Eyx.
      * (* y ≤ x and y ≤ z *)
        hauto lq:on.
      * (* ¬(y ≤ x) and ¬(x ≤ y) - IMPOSSIBLE by totality *)
        exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
    + (* ¬(x ≤ y), y ≤ z, ¬(x ≤ z) *)
      destruct (list_leb y x) eqn:Eyx.
      * hauto lq:on.
      * exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
    + (* ¬(x ≤ y), ¬(y ≤ z), x ≤ z *)
      destruct (list_leb z y) eqn:Ezy.
      * destruct (list_leb y x) eqn:Eyx.
        -- destruct (list_leb z x) eqn:Ezx.
           ++ (* ¬(x ≤ y), ¬(y ≤ z), x ≤ z, z ≤ y, y ≤ x, z ≤ x *)
              (* First prove z = x using antisymmetry of Ezx and Exz *)
              assert (Hzx: z = x) by (apply list_leb_antisym; auto).
              (* Now rewrite to make both sides equal *)
              rewrite Hzx. simpl. reflexivity.
           ++ exfalso. apply (list_leb_trans z y x) in Ezy; auto. rewrite Ezy in Ezx. discriminate.
        -- exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
      * destruct (list_leb y x) eqn:Eyx.
        -- (* ¬(x ≤ y), ¬(y ≤ z), x ≤ z, ¬(z ≤ y), y ≤ x *)
           (* This case is IMPOSSIBLE: we have  Eyz=false (¬(y≤z)) and Ezy=false (¬(z≤y)) which violates totality *)
           exfalso. destruct (list_leb_total y z) as [H | H]; rewrite H in *; discriminate.
        -- exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
    + (* ¬(x ≤ y), ¬(y ≤ z), ¬(x ≤ z) *)
      destruct (list_leb y x) eqn:Eyx.
      * destruct (list_leb z y) eqn:Ezy.
        -- destruct (list_leb z x) eqn:Ezx.
           ++ hauto lq:on.
           ++ exfalso. apply (list_leb_trans z y x) in Ezy; auto. rewrite Ezy in Ezx. discriminate.
        -- hauto lq:on.
      * exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
  - (* meet_comm *)
    intros x y. unfold list_meet.
    destruct (list_leb x y) eqn:Exy.
    + destruct (list_leb y x) eqn:Eyx.
      * apply (list_leb_antisym x y Exy Eyx).
      * reflexivity.
    + destruct (list_leb y x) eqn:Eyx.
      * reflexivity.
      * exfalso. destruct (list_leb_total x y) as [H | H]; rewrite H in *; discriminate.
  - (* meet_idem *)
    intro x. unfold list_meet.
    rewrite list_leb_refl. reflexivity.
Qed.
