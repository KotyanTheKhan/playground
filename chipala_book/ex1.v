From Stdlib Require Import List Bool Arith.
From ChipalaBook Require Import CpdtTactics.
Require Extraction.

From Hammer Require Import Hammer.

Set Hammer Print.
Set Hammer Debug.
(* Set Hammer ATPLimit 120. *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
match b with
| Plus => plus
| Times => mult
end.

Fixpoint expDenote (e : exp) : nat :=
match e with
| Const n => n
| Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
end.

Eval simpl in expDenote (Const 42).

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Inductive Instr : Set :=
| iConst : nat -> Instr
| iBinop : binop -> Instr.

Definition Stack := list nat.

Definition instrDenote (i : Instr) (s : Stack) : option Stack :=
  match i with
  | iConst n => Some (n :: s)
  | iBinop b =>
    match s with
    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
    | _ => None
    end
  end.

Definition Prog := list Instr.

Fixpoint progDenote (p : Prog) (s : Stack) : option Stack :=
  match p with
  | nil => Some s
  | i :: p' =>
    match instrDenote i s with
    | None => None
    | Some s' => progDenote p' s'
    end
  end.

Fixpoint compile (e : exp) : Prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).

Eval simpl in compile (Binop Plus (Const 2) (Const 2)).

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in progDenote (compile (Const 42)) nil.

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil.


Lemma compile_correct' : 
  forall e p s, 
  progDenote (compile e ++ p) s = 
  progDenote p (expDenote e :: s).
Proof.
  induction e.
  intros.
  unfold expDenote.
  unfold progDenote.
  simpl.
  fold progDenote.
  reflexivity.

  intros.
  unfold compile.
  fold compile.
  unfold expDenote.
  fold expDenote.
  rewrite <- app_assoc.
  rewrite IHe2.
  rewrite <- app_assoc.
  rewrite IHe1.
  simpl.
  fold progDenote.
  reflexivity.
Qed.

Lemma compile_correct'' : 
  forall e s p, 
  progDenote (compile e ++ p) s =
  progDenote p (expDenote e :: s).
Proof.
  induction e; crush.
  (* intros.
  apply (compile_correct' e p s). *)

Qed.


Theorem compile_correct : 
  forall e, progDenote (compile e) nil = 
  Some (expDenote e :: nil).
Proof.
  intros.
  rewrite <- (app_nil_r (compile e)).

  rewrite compile_correct''.
  simpl.
  reflexivity.
  
  (* apply (compile_correct'' e nil nil). *)
Qed.


(* ================ *)

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
  | TPlus : tbinop Nat Nat Nat
  | TTimes : tbinop Nat Nat Nat
  | TEq : forall t, tbinop t t Bool
  | TLt : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
  | TNConst : nat -> texp Nat
  | TBConst : bool -> texp Bool
  | TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.
  
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
: typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => Nat.eqb
  | TEq Bool => eqb
  | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1 ) (texpDenote e2 )
  end.

Eval simpl in texpDenote (TNConst 42).

Eval simpl in texpDenote (TBConst true).

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

(* ================== *)

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
  | TiNConst : forall s, nat -> tinstr s (Nat :: s)
  | TiBConst : forall s, bool -> tinstr s (Bool :: s)
  | TiBinop : forall arg1 arg2 res s,
    tbinop arg1 arg2 res
    -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
  | TNil : forall s, tprog s s
  | TCons : forall s1 s2 s3,
    tinstr s1 s2
    -> tprog s2 s3
    -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts' 
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s =>
      let '(arg1 , (arg2 , s')) := s in
      ((tbinopDenote b) arg1 arg2 , s')
end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
  | TNil _ => fun s => s
  | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
  | TNil _ => fun p' => p'
  | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TiNConst _ n) (TNil _)
  | TBConst b => TCons (TiBConst _ b) (TNil _)
  | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _) 
    (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.

Print tcompile.

Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.

Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
(TNConst 2)) (TNConst 7)) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2)
(TNConst 2)) (TNConst 7)) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
(TNConst 7)) nil) tt.

Lemma tconcat_correct'': 
  forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts), 
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
Proof.
  induction p; crush.
  (* intros.
  induction p.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHp.
    reflexivity. *)
Qed.

Hint Rewrite tconcat_correct''.

Lemma tcompile_correct': 
  forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
Proof.
  induction e; crush.
  (* induction e.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite tconcat_correct''.
    rewrite IHe2.
    rewrite tconcat_correct''.
    rewrite IHe1.
    simpl.
    reflexivity. *)
Qed.

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct: 
  forall t (e : texp t), tprogDenote (tcompile e nil) tt = 
  (texpDenote e, tt).
Proof.
  crush.
  (* induction e.
  - simpl; reflexivity.
  - simpl.
    reflexivity.
  - 
    unfold tcompile.
    fold tcompile.
    rewrite tconcat_correct''.
    rewrite tcompile_correct'.
    rewrite tconcat_correct''.
    rewrite tcompile_correct'.
    simpl.
    reflexivity. *)
Qed.

Extraction tcompile.

Check (fun x : nat => x).

Check (fun x : True => x).

Check I.

Check (fun _ : False => I).

Check (fun x : False => x).

Inductive unit : Set :=
  | tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
  (* sauto. *)
  intros.
  destruct x.
  reflexivity.
Qed.

Check unit_ind.


Inductive tree : Type :=
  | Leaf : tree
  | Node : nat -> tree -> tree -> tree.

Fixpoint tree_height (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ l r => 1 + max (tree_height l) (tree_height r)
  end.

From Stdlib Require Import Lia.

Theorem tree_height_nonneg : forall t, tree_height t >= 0.
Proof.
  intros t.
  induction t.
  - simpl. lia.
  - simpl. lia.
Qed.

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node v l r => 1 + (size l) + (size r)
  end.

Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node v l r => Node v (mirror r) (mirror l)
  end.

Theorem size_mirror : forall t : tree,
  size (mirror t) = size t.
Proof.
  intros t.
  induction t as [| v l IHl r IHr].
  - (* Case: t = Leaf *)
    simpl. reflexivity.
  - (* Case: t = Node v l r *)
    simpl. 
    (* Goal: 1 + size (mirror r) + size (mirror l) = 1 + size l + size r *)
    rewrite IHl.
    rewrite IHr.
    (* Goal: 1 + size r + size l = 1 + size l + size r *)
    lia. (* Using automation for addition commutativity *)
Qed.

Inductive balanced : tree -> Prop :=
  | bal_Leaf : balanced Leaf
  | bal_Node : forall v l r, 
      balanced l -> 
      balanced r -> 
      balanced (Node v l r).

Lemma balanced_left : forall v l r,
  balanced (Node v l r) -> balanced l.
Proof.
  intros v l r H.
  inversion H as [ | v' l' r' H_left H_right ].
  (* H_left : balanced l' *)
  (* H_right : balanced r' *)
  (* Coq also derived that l = l' *)
  assumption.
Qed.

Lemma leaf_not_node : forall v l r,
  Leaf <> Node v l r.
Proof.
  intros x l r H.
  inversion H. (* Solves the goal immediately *)
Qed.

Theorem mirror_mirror_manual : forall t : tree, 
  mirror (mirror t) = t.
Proof.
  (* info_auto 30. *)
  induction t; simpl; congruence.
  (* intros t.
  induction t as [| v l IHl r IHr].
  - (* Case: t = Leaf *)
    simpl. reflexivity.
  - (* Case: t = Node v l r *)
    simpl.
    rewrite IHr.
    rewrite IHl.
    reflexivity. *)
Qed.

(* Imagine we add transitivity to our hint database *)
(* Section TransitivityHint.

  Hypothesis trans : forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
  Hint Resolve trans : my_db. (* Try this only as a last resort *).
  Hint Resolve direct_fact : my_db.  (* Try this first *)

  Goal 1 = 2.
  Proof.
    debug auto 10 with my_db.
  Qed.

End TransitivityHint. *)

Definition double (n : nat) := n + n.

Lemma rewrite_example : forall (x y : nat), x = y -> x + x = y + y.
Proof.
  intros x y H. (* H : x = y |- x + x = y + y *)
  rewrite H.    (* Goal becomes: y + y = y + y *)
  reflexivity.
Qed.

Lemma subst_example : forall (x y z : nat), x = y -> y = z -> x = z.
Proof.
  intros x y z H1 H2. (* H1 : x = y, H2 : y = z |- x = z *)
  rewrite H1.            (* Replaces x with y everywhere. H1 is removed. *)
  (* Context is now: H2 : y = z |- y = z *)
  assumption.
Qed.

Lemma add_assoc : 
  forall n m p : nat, 
  (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - (* Base Case: n = 0 *)
    simpl. 
    reflexivity.
  - (* Inductive Step: n = S n' *)
    simpl. 
    rewrite IHn'. 
    reflexivity.
Qed.

Lemma bracket_example : 
  forall n m : nat, 
  (n + m) = n + m.
Proof.
  reflexivity.
Qed.

Lemma distributive_example :
  forall a b c : nat,
  a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  - (* Base Case: a = 0 *)
    simpl. 
    reflexivity.
  - (* Inductive Step: a = S a' *)
    simpl.
    lia.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n, ev n -> ev (S (S n)).

Lemma no_ev_1 : ~ ev 1.
Proof.
  intros H.
  inversion H. (* Coq sees that neither ev_0 nor ev_SS can produce 'ev 1' *)
Qed.

Lemma neq: ~ (0 = 1).
Proof.
  intros H.
  discriminate H.
Qed.