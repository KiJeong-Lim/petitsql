Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Program.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.

Module Utils.

  Lemma lt_strongInd (P : nat -> Prop)
    (IND : forall n : nat, forall IH : forall m : nat, m < n -> P m, P n)
    : forall n : nat, P n.
  Proof.
    intros n. eapply IND. induction n as [ | n IH].
    - intros m H_lt. inversion H_lt.
    - intros m H_lt. eapply IND.
      intros i i_lt_m. eapply IH. lia.
  Defined.

  Lemma acc_lt
    : forall x : nat, Acc Nat.lt x.
  Proof. exact (lt_strongInd (@Acc nat Nat.lt) (@Acc_intro nat Nat.lt)). Defined.

  Lemma acc_rel {A : Type} {B : Type} (f : A -> B) (R : B -> B -> Prop)
    (R_wf : forall y : B, Acc R y)
    : forall x : A, Acc (fun lhs : A => fun rhs : A => R (f lhs) (f rhs)) x.
  Proof.
    intros x. remember (f x) as y eqn: y_eq_f_x.
    revert x y_eq_f_x. induction (R_wf y) as [y' hyp_wf IH].
    intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
    subst y'. eapply IH; [exact (f_x_R_f_x') | reflexivity].
  Defined.

End Utils.

Export Utils.

Module P.

  Import ListNotations.

  Definition parser (A : Type) : Type := string -> option (A * string).

  Definition runParser {A : Type} (p : parser A) (s : string) : option (A * string) := p s.

  Class Monad (M : Type -> Type) : Type :=
    { pure {A : Type} : A -> M A
    ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
    }.

  Global Infix " >>= " := bind (left associativity, at level 90).

  Global Instance parserMonad : Monad parser :=
    { pure {A} := fun x : A => fun s : string => Some (x, s)
    ; bind {A} {B} := fun m : parser A => fun k : A -> parser B => fun s : string =>
      match m s with
      | None => None
      | Some (x, s') => k x s'
      end
    }.

  Definition empty {A : Type} : parser A :=
    fun s : string => None.

  Definition alt {A : Type} (p1 : parser A) (p2 : parser A) : parser A := fun s : string =>
    match p1 s with
    | None => p2 s
    | Some (x, s') => Some (x, s')
    end.

  Global Infix " <|> " := alt (left associativity, at level 50).

  Definition isLt {A : Type} (p : parser A) : Prop :=
    forall s : string,
    match p s with
    | None => True
    | Some (x, s') => length s' < length s
    end.

  Definition isLe {A : Type} (p : parser A) : Prop :=
    forall s : string,
    match p s with
    | None => True
    | Some (x, s') => length s' <= length s
    end.

  Definition some {A : Type}
    (p1 : parser A)
    (p1_isLt : isLt p1)
    : {p : parser (list A) | isLe p}.
  Proof.
    enough (TO_SHOW : forall s : string, {ret : option (list A * string) | match ret with None => True | Some (x, s') => length s' <= length s end}).
    { exact (@exist (parser (list A)) isLe (fun s => proj1_sig (TO_SHOW s)) (fun s => proj2_sig (TO_SHOW s))). }
    enough (MAIN : forall s : string, Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s -> {ret : option (list A * string) | match ret with None => True | Some (x, s') => length s' <= length s end}).
    { intros s. exact (MAIN s (Utils.acc_rel length Nat.lt acc_lt s)). }
    apply (@Acc_rect string (fun s1 : string => fun s2 : string => length s1 < length s2) (fun s : string => {ret : option (list A * string) | match ret with None => True | Some (x, s') => length s' <= length s end})).
    intros s _ IH. destruct (p1 s) as [[x s'] | ] eqn: H_p1_s.
    - pose proof (p1_isLt s) as s_isLongerThan_s'.
      rewrite H_p1_s in s_isLongerThan_s'.
      destruct (IH s' s_isLongerThan_s') as [[[xs s''] | ] H_ps] eqn: H_ps_s'.
      + exists (Some ((x :: xs), s'')). lia.
      + exists (Some ([], s')). lia.
    - exists (None). trivial.
  Defined.

End P.

Module Hs.

  Inductive strSQLElem : Set :=
  | Text : string -> strSQLElem
  | Hole : string -> strSQLElem.

  Inductive value : Set :=
  | ColName : string -> value
  | StrVal  : string -> value
  | Var     : string -> value.

  Inductive term : Set := 
  | equalTerm : value -> value -> term.

  Inductive pred : Set := 
  | orPred : pred -> pred -> pred
  | termPred : term -> pred.

  Inductive cols : Set :=
  | star : cols
  | colNames : list string -> cols.

  Inductive sql : Set :=
  | sqlSFW : cols -> string -> option pred -> sql.

  Fixpoint normPred_measure (p : pred) {struct p} : nat :=
    match p with
    | termPred t => 0
    | orPred p1 p2 => 1 + (2 * normPred_measure p1 + normPred_measure p2)
    end.

  #[program]
  Fixpoint normPred (p : pred) {measure (normPred_measure p)} : pred :=
    match p with
    | termPred t => termPred t
    | orPred (termPred t1) p2 => orPred (termPred t1) (normPred p2)
    | orPred (orPred p11 p12) p2 => normPred (orPred p11 (orPred p12 p2))
    end.
  Next Obligation. simpl. lia. Defined.

  Lemma normPred_unfold (p : pred) :
    normPred p =
    match p with
    | termPred t => termPred t
    | orPred (termPred t1) p2 => orPred (termPred t1) (normPred p2)
    | orPred (orPred p11 p12) p2 => normPred (orPred p11 (orPred p12 p2))
    end.
  Proof with eauto.
    unfold normPred at 1. rewrite fix_sub_eq.
    - destruct p as [[? ? | ?] | ?]...
    - intros. destruct x as [[? ? | ?] | ?]; simpl... rewrite H...
  Qed.

  (* Eval compute in (normPred (orPred (orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (termPred (equalTerm (ColName "C") (ColName "D")))) (termPred (equalTerm (ColName "E") (ColName "F"))))). *)
  (* = orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (orPred (termPred (equalTerm (ColName "C") (ColName "D"))) (termPred (equalTerm (ColName "E") (ColName "F")))) : pred *)

End Hs.
