Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Program.
Require Import Coq.Program.Wf.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.

Module Utils.

  Import ListNotations.

  Class isSetoid (A : Type) : Type :=
    { eqProp (lhs : A) (rhs : A) : Prop
    ; eqProp_Equivalence :> Equivalence eqProp
    }.

  #[global]
  Infix " == " := eqProp (no associativity, at level 70) : type_scope.

  #[global, program]
  Instance arrow_isSetoid {A : Type} {B : Type} (B_isSetoid : isSetoid B) : isSetoid (arrow A B) :=
    { eqProp (f1 : A -> B) (f2 : A -> B) := forall x : A, f1 x == f2 x }.
  Next Obligation.
    split.
    - intros f1 x. reflexivity.
    - intros f1 f2 f1_eq_f2 x. rewrite f1_eq_f2 with (x := x). reflexivity.
    - intros f1 f2 f3 f1_eq_f2 f2_eq_f3 x. rewrite f1_eq_f2 with (x := x). rewrite f2_eq_f3 with (x := x). reflexivity.
  Qed.

  Class Monad (M : Type -> Type) : Type :=
    { pure {A : Type} : A -> M A
    ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
    }.

  #[global]
  Infix " >>= " := bind (left associativity, at level 90).

  #[global]
  Instance option_isMonad : Monad option :=
    { pure {A} (x : A) := Some x
    ; bind {A} {B} (m : option A) (k : A -> option B) :=
      match m with
      | Some x => k x
      | None => None
      end
    }.

  #[global]
  Instance list_isMonad : Monad list :=
    { pure {A} (x : A) := [x]
    ; bind {A} {B} (m : list A) (k : A -> list B) := List.concat (List.map k m)
    }.

  Class Alternative (F : Type -> Type) : Type :=
    { empty {A : Type} : F A
    ; alt {A : Type} : F A -> F A -> F A
    }.

  #[global]
  Infix " <|> " := alt (left associativity, at level 50).

  #[global]
  Instance option_isAlternative : Alternative option :=
    { empty {A} := None
    ; alt {A} (m1 : option A) (m2 : option A) :=
      match m1 with
      | Some x1 => Some x1
      | None => m2
      end
    }.

  #[global]
  Instance list_isAlternative : Alternative list :=
    { empty {A} := []
    ; alt {A} (xs1 : list A) (xs2 : list A) := xs1 ++ xs2
    }.

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

  Definition parserT (M : Type -> Type) (A : Type) : Type := string -> M (prod A string).

  #[global]
  Instance parserT_isMonad {M : Type -> Type} (M_isMonad : Monad M) : Monad (parserT M) :=
    { pure {A} := curry pure
    ; bind {A} {B} (m : parserT M A) (k : A -> parserT M B) := fun s : string => m s >>= uncurry k
    }.

  #[global]
  Instance parserT_isAlternative {M : Type -> Type} (M_isAlternative : Alternative M) : Alternative (parserT M) :=
    { empty {A} := fun s : string => empty
    ; alt {A} (p1 : parserT M A) (p2 : parserT M A) := fun s : string => p1 s <|> p2 s
    }.

  Definition parser : Type -> Type := parserT option.

  Definition eqP {A : Type} (lhs : parser A) (rhs : parser A) : Prop :=
    forall s : string, lhs s = rhs s.

  #[global]
  Instance eqP_Equivalence {A : Type}
    : Equivalence (@eqP A).
  Proof.
    split.
    - intros x s. reflexivity.
    - intros x y x_eq_y s. rewrite x_eq_y with (s := s). reflexivity.
    - intros x y z x_eq_y y_eq_z s. rewrite x_eq_y with (s := s). rewrite y_eq_z with (s := s). reflexivity.
  Qed.

  #[global]
  Instance parser_isSetoid {A : Type} : isSetoid (parser A) :=
    { eqProp := eqP
    ; eqProp_Equivalence := eqP_Equivalence
    }.

  #[global]
  Add Parametric Morphism {A : Type}
    : (@alt parser (parserT_isAlternative option_isAlternative) A) with signature (eqProp ==> eqProp ==> eqProp) as alt_lifts_eqP.
  Proof. intros lhs1 rhs1 lhs1_eq_rhs1 lhs2 rhs2 lhs2_eq_rhs2 s. simpl. rewrite lhs1_eq_rhs1 with (s := s). rewrite lhs2_eq_rhs2 with (s := s). reflexivity. Qed.

  #[global]
  Add Parametric Morphism {A : Type} {B : Type}
    : (@bind parser (parserT_isMonad option_isMonad) A B) with signature (eqProp ==> eqProp (isSetoid := arrow_isSetoid parser_isSetoid) ==> eqProp) as bind_lifts_eqP.
  Proof. intros m1 m2 m1_eq_m2 k1 k2 k1_eq_k2 s. simpl. rewrite m1_eq_m2 with (s := s). destruct (m2 s) as [[x s'] | ]; simpl; trivial. eapply k1_eq_k2. Qed.

  Definition isLt {A : Type} (p : parser A) : Prop :=
    forall s : string,
    match p s with
    | Some (x, s') => length s' < length s
    | None => True
    end.

  Definition isLe {A : Type} (p : parser A) : Prop :=
    forall s : string,
    match p s with
    | Some (x, s') => length s' <= length s
    | None => True
    end.

  Definition satisfy (p : ascii -> bool) : parser ascii :=
    fun s : string =>
    match s with
    | EmptyString => None
    | String ch s' => if p ch then Some (ch, s') else None
    end.

  Lemma satisfy_isLt (p : ascii -> bool)
    : isLt (satisfy p).
  Proof.
    intros s. unfold satisfy. destruct s as [ | ch s']; trivial.
    destruct (p ch); trivial. simpl. red. reflexivity.
  Qed.

  #[program]
  Fixpoint some {A : Type} (p : parser A) (p_isLt : isLt p) (s : string) {measure (length s)} : option (list A * string) :=
    match p s with
    | None => None
    | Some (x, s') =>
      match some p p_isLt s' with
      | None => Some ([x], s')
      | Some (xs, s'') => Some (x :: xs, s'')
      end
    end.
  Next Obligation. pose proof (p_isLt s) as H. rewrite <- Heq_anonymous in H. assumption. Defined.

  Example some_example1
    : (some (satisfy (fun ch : ascii => true)) (satisfy_isLt _) "abc"%string)
    = Some (["a"%char; "b"%char; "c"%char], ""%string).
  Proof. reflexivity. Qed.

  Example some_example2
    : (some (satisfy (fun ch : ascii => Ascii.eqb ch "a"%char)) (satisfy_isLt _) "abc"%string)
    = Some (["a"%char], "bc"%string).
  Proof. reflexivity. Qed.

  Example some_example3
    : (some (satisfy (fun ch : ascii => Ascii.eqb ch "b"%char)) (satisfy_isLt _) "abc"%string)
    = None.
  Proof. reflexivity. Qed.

  Lemma some_unfold {A : Type} (p : parser A) (p_isLt : isLt p) (s : string) :
    some p p_isLt s =
    match p s with
    | None => None
    | Some (x, s') =>
      match some p p_isLt s' with
      | None => Some ([x], s')
      | Some (xs, s'') => Some (x :: xs, s'')
      end
    end.
  Proof.
    unfold some at 1. unfold some_func. rewrite WfExtensionality.fix_sub_eq_ext.
    destruct (p s) as [[x s'] | ] eqn: OBS_p_s; simpl.
    - rewrite OBS_p_s. destruct (some p p_isLt s') as [[xs s''] | ] eqn: OBS_some_p_s'.
      + unfold some in OBS_some_p_s'. unfold some_func in OBS_some_p_s'.
        rewrite OBS_some_p_s'. reflexivity.
      + unfold some in OBS_some_p_s'. unfold some_func in OBS_some_p_s'.
        rewrite OBS_some_p_s'. reflexivity.
    - rewrite OBS_p_s. reflexivity.
  Qed.

  Lemma some_isLt {A : Type} (p : parser A)
    (p_isLt : isLt p)
    : isLt (some p p_isLt).
  Proof.
    intros s.
    assert (H_Acc : Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s) by exact (Utils.acc_rel String.length lt Utils.acc_lt s).
    induction H_Acc as [s _ IH]. rewrite some_unfold. pose proof (p_isLt s) as length_s_gt_length_s'. destruct (p s) as [[x s'] | ]; trivial. specialize (IH s' length_s_gt_length_s'). destruct (some p p_isLt s') as [[xs s''] | ]; lia.
  Qed.

  Definition many {A : Type} (p : parser A) (p_isLt : isLt p) : parser (list A) := some p p_isLt <|> pure [].

  Theorem some_spec {A : Type} (p : parser A) (p_isLt : isLt p)
    : some p p_isLt == (p >>= fun x => many p p_isLt >>= fun xs => pure (x :: xs)).
  Proof.
    intros s. rewrite some_unfold at 1. unfold many. simpl. destruct (p s) as [[x s'] | ]; try reflexivity.
    simpl. destruct (some p p_isLt s') as [[xs s''] | ]; try reflexivity.
  Qed.

  Theorem many_spec {A : Type} (p : parser A) (p_isLt : isLt p)
    : many p p_isLt == some p p_isLt <|> pure [].
  Proof. reflexivity. Qed.

  Lemma some_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
    (p1_eq_p2 : p1 == p2)
    : some p1 p1_isLt == some p2 p2_isLt.
  Proof.
    intros s.
    assert (H_Acc : Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s) by exact (Utils.acc_rel String.length lt Utils.acc_lt s).
    induction H_Acc as [s _ IH]. do 2 rewrite some_unfold.
    pose proof (p1_eq_p2 s) as p1_s_eq_p2_s. rewrite p1_s_eq_p2_s. destruct (p2 s) as [[x s'] | ]; trivial.
    rewrite IH; trivial. pose proof (p1_isLt s) as length_s_gt_length_s'. rewrite p1_s_eq_p2_s in length_s_gt_length_s'. assumption.
  Qed.

  Lemma many_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
    (p1_eq_p2 : p1 == p2)
    : many p1 p1_isLt == many p2 p2_isLt.
  Proof. unfold many. rewrite some_lifts_eqP with (p1_isLt := p1_isLt) (p2_isLt := p2_isLt); try assumption. reflexivity. Qed.

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

  Example normPred_example1
    : (normPred (orPred (orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (termPred (equalTerm (ColName "C") (ColName "D")))) (termPred (equalTerm (ColName "E") (ColName "F")))))
    = orPred (termPred (equalTerm (ColName "A") (ColName "B"))) (orPred (termPred (equalTerm (ColName "C") (ColName "D"))) (termPred (equalTerm (ColName "E") (ColName "F")))).
  Proof. reflexivity. Qed.

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

End Hs.
