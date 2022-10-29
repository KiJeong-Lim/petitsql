Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Import IfNotations.

Require Import Coq.Strings.String.


Inductive strSQLElem : Type :=
  Text : string -> strSQLElem
| Hole : string -> strSQLElem.

Inductive value : Type :=
  ColName : string -> value
| StrVal  : string -> value
| Var     : string -> value.       


Inductive term : Type := 
  equalTerm : value -> value -> term.

Inductive pred : Type := 
  orPred : pred -> pred -> pred
| termPred : term -> pred.

Inductive cols : Type :=
  star : cols
| colNames : list string -> cols.

Inductive sql : Type :=
  sqlSFW : cols -> string -> option pred -> sql.

Fixpoint normPred (p : pred) : pred :=
  match p with
    termPred t => termPred t
  | orPred (termPred t1) p2 => orPred (termPred t1) (normPred p2)
  | orPred (orPred p11 p12) p2 => normPred (orPred p11 (orPred p12 p2))
  end

(* normPred 0 p = p *)
(* normPred (S m) (termPred t) = termPred t *)
(* normPred (S m) (orPred (termPred t) p) = orPred (termPred t) (normPred m p) *)
(* normPred (S m) (orPred (p1 p2) p3) = normpred m (orPred p1 (orPred p2 p3)) *)

(* Fixpoint normPred (n : nat) (p : pred) : pred := *)
(*   match n with  *)
(*     0 => p *)
(*   | S m => match p with *)
(*              termPred t => termPred t *)
(*            | orPred (termPred t) p =>  orPred (termPred t) (normPred m p) *)
(*            | orPred (orPred p1 p2) p3 => normPred m (orPred p1 (orPred p2 p3)) *)
(*            end *)
(*   end. *)

Fixpoint auxNormPred (p q : pred) : pred :=
  match p with
    termPred t => orPred (termPred t) q
  | orPred p1 p2 => auxNormPred p1 (auxNormPred p2 q)
  end.

Fixpoint normPred (p : pred) : pred :=
  match p with
    termPred t => termPred t
  | orPred (termPred t1) p2 => orPred (termPred t1) (normPred p2)
  | orPred (orPred p11 p12) p2 => auxNormPred p11 (auxNormPred p12 p2)
  end.


