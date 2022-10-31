Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Module T. (* For Haskell types *)

  Definition Char : Set := ascii.

  Definition String : Set := string.

  Definition Parser (a : Type) : Type := T.String -> list (a * T.String).

End T.

Module P. (* For petitsql/app/ParserLib.hs *)

  Import ListNotations IfNotations.

  Definition pure {A : Type} (v : A) : T.Parser A :=
    fun inp => [(v,inp)].

  Definition failure {A : Type} : T.Parser A :=
    fun inp => [].

  Definition item : T.Parser T.Char :=
    fun inp =>
    match inp with
    | EmptyString => []
    | String x xs => [(x,xs)]
    end.

  Definition parse {A : Type} (p : T.Parser A) (inp : T.String) : list (A * T.String) := p inp.

  Definition bind {A : Type} {B : Type} (m : T.Parser A) (k : A -> T.Parser B) : T.Parser B :=
    fun inp => concat (map (fun '(v,out) => k v out) (m inp)).

  Global Infix " >>= " := bind (left associativity, at level 90).

  Definition alt {A : Type} (p : T.Parser A) (q : T.Parser A) : T.Parser A :=
    fun inp => parse p inp ++ parse q inp.

  Global Infix " +++ " := alt (left associativity, at level 50).

  Definition sat (p : T.Char -> bool) : T.Parser T.Char :=
    item >>= fun x => if p x then pure x else failure.

(** Fail to define: -- Cannot guess decreasing argument of fix.

  Fixpoint many {A : Type} (p : T.Parser A) : T.Parser (list A) :=
    many1 p +++ pure []
  with many1 {A : Type} (p : T.Parser A) : T.Parser (list A) :=
    p >>= fun v => many p >>= fun vs => pure (v :: vs).

*)

End P.

Module Hs. (* For petitsql/app/PetitSQL.hs *)

  Import IfNotations.

  Inductive strSQLElem : Type :=
  | Text : string -> strSQLElem
  | Hole : string -> strSQLElem.

  Inductive value : Type :=
  | ColName : string -> value
  | StrVal  : string -> value
  | Var     : string -> value.       

  Inductive term : Type := 
  | equalTerm : value -> value -> term.

  Inductive pred : Type := 
  | orPred : pred -> pred -> pred
  | termPred : term -> pred.

  Inductive cols : Type :=
  | star : cols
  | colNames : list string -> cols.

  Inductive sql : Type :=
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
    - destruct p as [[ | ] | ]...
    - intros. destruct x as [[ | ] | ]; simpl... rewrite H...
  Qed.

  (* Eval compute in (normPred (orPred (orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (termPred (equalTerm (ColName "C") (ColName "D")))) (termPred (equalTerm (ColName "E") (ColName "F"))))). *)
  (* = orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (orPred (termPred (equalTerm (ColName "C") (ColName "D"))) (termPred (equalTerm (ColName "E") (ColName "F")))) : pred *)

End Hs.
