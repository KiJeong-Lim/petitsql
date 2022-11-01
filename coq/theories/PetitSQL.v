Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Program.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.

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
