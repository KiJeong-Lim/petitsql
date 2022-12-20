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
Require Import Coq.Strings.BinaryString.
Require Import Coq.Strings.Byte.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.

Module StringNotations.

Notation char := ascii.

Notation " '[' ']' " := (EmptyString) : string_scope.

Notation " ch '::' str " := (String (ch)%char (str)%string) : string_scope.

End StringNotations.

Module Prelude.

Import StringNotations ListNotations.

#[universes(polymorphic=yes)]
Definition REFERENCE_HOLDER@{lv} {STATEMENT_Type : Type@{lv}} (REFERENCED_STATEMENT : unit -> STATEMENT_Type) : STATEMENT_Type := REFERENCED_STATEMENT tt.
Notation " '<<' STATEMENT_REFERENCE ':' STATEMENT '>>' " := (REFERENCE_HOLDER (fun STATEMENT_REFERENCE : unit => match STATEMENT_REFERENCE with tt => STATEMENT end)) (STATEMENT_REFERENCE name, STATEMENT at level 200, at level 70, no associativity) : type_scope.
Ltac unnw := unfold REFERENCE_HOLDER in *.

Ltac des_ifs := repeat
  match goal with
  | |- context[ match ?x with _ => _ end ] =>
    match (type of x) with
    | { _ } + { _ } => destruct x
    | _ => let H_OBS := fresh "H_OBS" in destruct x as [] eqn: H_OBS
    end
  | H : context[ match ?x with _ => _ end ] |- _ =>
    match (type of x) with
    | { _ } + { _ } => destruct x
    | _ => let H_OBS := fresh "H_OBS" in destruct x as [] eqn: H_OBS
    end
  end.

Definition dollar {A : Set} {B : Set} (f : A -> B) (x : A) : B := f x.

Infix " $ " := dollar (right associativity, at level 100) : program_scope.

Class hasEqDec (A : Type) : Type := eq_dec (lhs : A) (rhs : A) : {lhs = rhs} + {lhs <> rhs}.

Definition eqb {A : Type} {hasEqDec : hasEqDec A} (lhs : A) (rhs : A) : bool :=
  if Prelude.eq_dec lhs rhs then true else false.

#[global]
Instance nat_hasEqDec : hasEqDec nat := Nat.eq_dec.

#[global]
Instance Z_hasEqDec : hasEqDec Z := Z.eq_dec.

#[global]
Instance string_hasEqDec : hasEqDec string := string_dec.

#[global]
Instance list_hasEqDec {A : Type} (A_hasEqDec : hasEqDec A) : hasEqDec (list A) := @list_eq_dec A A_hasEqDec.

Class isSetoid (A : Type) : Type :=
  { eqProp (lhs : A) (rhs : A) : Prop
  ; eqProp_Equivalence :> Equivalence eqProp
  }.

Infix " == " := eqProp (no associativity, at level 70) : type_scope.

#[global, program]
Instance arrow_isSetoid {A : Type} {B : Type} (B_isSetoid : isSetoid B) : isSetoid (arrow A B) :=
  { eqProp (f1 : arrow A B) (f2 : arrow A B) := forall x : A, f1 x == f2 x }.
Next Obligation.
  split.
  - intros f1 x. reflexivity.
  - intros f1 f2 f1_eq_f2 x. rewrite f1_eq_f2 with (x := x). reflexivity.
  - intros f1 f2 f3 f1_eq_f2 f2_eq_f3 x. rewrite f1_eq_f2 with (x := x). rewrite f2_eq_f3 with (x := x). reflexivity.
Qed.

#[global]
Instance string_isSetoid : isSetoid string :=
  { eqProp := @eq string
  ; eqProp_Equivalence := eq_equivalence
  }.

Definition liftRel_option {A : Type} (R : A -> A -> Prop) (lhs : option A) (rhs : option A) : Prop :=
  match lhs, rhs with
  | Some lhs', Some rhs' => R lhs' rhs'
  | None, None => True
  | _, _ => False
  end.

#[global, program]
Instance option_isSetoid {A : Type} (A_isSetoid : isSetoid A) : isSetoid (option A) :=
  { eqProp := liftRel_option eqProp }.
Next Obligation.
  split.
  - intros [x | ]; cbn; try tauto.
    reflexivity.
  - intros [x | ] [y | ]; cbn; try tauto.
    intros x_eq_y. symmetry; assumption.
  - intros [x | ] [y | ] [z | ]; cbn; try tauto.
    intros x_eq_y y_eq_z. etransitivity; eassumption.
Qed.

#[global, program]
Instance list_isSetoid {A : Type} (A_isSetoid : isSetoid A) : isSetoid (list A) :=
  { eqProp (lhs : list A) (rhs : list A) := forall i : nat, liftRel_option eqProp (nth_error lhs i) (nth_error rhs i) }.
Next Obligation.
  split.
  - intros xs i.
    destruct (nth_error xs i) as [xs_i | ] eqn: OBS_xs_i; cbn in *; try tauto.
    reflexivity.
  - intros xs ys xs_eq_ys i. specialize xs_eq_ys with (i := i). 
    destruct (nth_error xs i) as [xs_i | ] eqn: OBS_xs_i; destruct (nth_error ys i) as [ys_i | ] eqn: OBS_ys_i; cbn in *; try tauto.
    symmetry; assumption.
  - intros xs ys zs xs_eq_ys ys_eq_zs i. specialize xs_eq_ys with (i := i). specialize ys_eq_zs with (i := i). 
    destruct (nth_error xs i) as [xs_i | ] eqn: OBS_xs_i; destruct (nth_error ys i) as [ys_i | ] eqn: OBS_ys_i; cbn in *; destruct (nth_error zs i) as [zs_i | ] eqn: OBS_zs_i; try tauto.
    etransitivity; eassumption.
Qed.

Class isMonad (M : Type -> Type) : Type :=
  { pure {A : Type} : A -> M A
  ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
  }.

Infix " >>= " := bind (left associativity, at level 90).

#[global]
Instance option_isMonad : isMonad option :=
  { pure {A} (x : A) := Some x
  ; bind {A} {B} (m : option A) (k : A -> option B) :=
    match m with
    | Some x => k x
    | None => None
    end
  }.

#[global]
Instance list_isMonad : isMonad list :=
  { pure {A} (x : A) := [x]
  ; bind {A} {B} (m : list A) (k : A -> list B) := List.concat (List.map k m)
  }.

Class isAlternative (F : Type -> Type) : Type :=
  { empty {A : Type} : F A
  ; alt {A : Type} : F A -> F A -> F A
  }.

Infix " <|> " := alt (left associativity, at level 50).

#[global]
Instance option_isAlternative : isAlternative option :=
  { empty {A} := None
  ; alt {A} (m1 : option A) (m2 : option A) :=
    match m1 with
    | Some x1 => Some x1
    | None => m2
    end
  }.

#[global]
Instance list_isAlternative : isAlternative list :=
  { empty {A} := []
  ; alt {A} (xs1 : list A) (xs2 : list A) := xs1 ++ xs2
  }.

Fixpoint sequenceM {M : Type -> Type} {isMonad : isMonad M} {A : Type} (ms : list (M A)) : M (list A) :=
  match ms with
  | [] => pure []
  | m :: ms' => m >>= fun x => sequenceM ms' >>= fun xs => pure (x :: xs)
  end.

Fixpoint sequenceM_ {M : Type -> Type} {isMonad : isMonad M} {A : Type} (ms : list (M A)) : M unit :=
  match ms with
  | [] => pure tt
  | m :: ms' => m >>= fun _ => sequenceM_ ms'
  end.

Fixpoint lookup {A : Type} {B : Type} {hasEqDec : hasEqDec A} (x : A) (zs : list (A * B)) : option B :=
  match zs with
  | [] => None
  | (x', y) :: zs' => if Prelude.eqb x x' then Some y else lookup x zs'
  end.

Lemma lt_strong_ind (P : nat -> Prop)
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
Proof. exact (Prelude.lt_strong_ind (@Acc nat Nat.lt) (@Acc_intro nat Nat.lt)). Defined.

Lemma acc_rel {A : Type} {B : Type} (f : A -> B) (R : B -> B -> Prop)
  (R_wf : forall y : B, Acc R y)
  : forall x : A, Acc (fun lhs : A => fun rhs : A => R (f lhs) (f rhs)) x.
Proof.
  intros x. remember (f x) as y eqn: y_eq_f_x.
  revert x y_eq_f_x. induction (R_wf y) as [y' hyp_wf IH].
  intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
  subst y'. eapply IH; [exact (f_x_R_f_x') | reflexivity].
Defined.

Section STRING_OPERATIONS.

Fixpoint mk_string (xs : list char) : string :=
  match xs with
  | [] => []%string
  | ch :: xs' => (ch :: mk_string xs')%string
  end.

Fixpoint mapFromString {A : Type} (f : char -> A) (s : string) : list A :=
  match s with
  | []%string => []
  | (ch :: s')%string => f ch :: mapFromString f s'
  end.

Fixpoint String_take (n : nat) (s : string) : string :=
  match n with
  | O => []%string
  | S n' =>
    match s with
    | []%string => []%string
    | (ch :: s')%string => (ch :: String_take n' s')%string
    end
  end.

Fixpoint String_concat (ss : list string) : string :=
  match ss with
  | [] => ""%string
  | s :: ss' => (s ++ String_concat ss')%string
  end.

Fixpoint String_drop (n : nat) (s : string) : string :=
  match n with
  | O => s
  | S n' =>
    match s with
    | []%string => []%string
    | (ch :: s')%string => String_drop n' s'
    end
  end.

Fixpoint String_rev (s : string) : string :=
  match s with
  | []%string => []%string
  | (ch :: s')%string => (String_rev s' ++ (ch :: []))%string
  end.

Definition showDigit (n : nat) : char :=
  match n with
  | 0 => "0"%char
  | 1 => "1"%char
  | 2 => "2"%char
  | 3 => "3"%char
  | 4 => "4"%char
  | 5 => "5"%char
  | 6 => "6"%char
  | 7 => "7"%char
  | 8 => "8"%char
  | 9 => "9"%char
  | _ => "_"%char
  end.

#[program]
Fixpoint nat_to_string1 (n : nat) (s : string) {measure n} : string :=
  if Prelude.eq_dec n 0 then s else nat_to_string1 (n / 10) (showDigit (n mod 10) :: s)%string.
Next Obligation. change (n / 10 < n). pose proof (Nat.div_mod n 10). pose proof (Nat.mod_bound_pos n 10). lia. Defined.

Lemma nat_to_string1_unfold (n : nat) (s : string) :
  nat_to_string1 n s =
  if Prelude.eq_dec n 0 then s else nat_to_string1 (n / 10) (showDigit (n mod 10) :: s)%string.
Proof.
  unfold nat_to_string1 at 1. unfold nat_to_string1_func.
  rewrite WfExtensionality.fix_sub_eq_ext. simpl.
  destruct (Prelude.eq_dec n 0) as [H_yes | H_no]; reflexivity.
Qed.

Definition nat_to_string (n : nat) : string :=
  if Nat.eqb n 0 then "0"%string else nat_to_string1 n ""%string.

Definition Z_to_string (z : Z) : string :=
  match z with
  | Z0 => "0"%string
  | Zpos pos => nat_to_string (Pos.to_nat pos)
  | Zneg neg => ("-" ++ nat_to_string (Pos.to_nat neg))%string
  end.

Fixpoint nat_from_string1 (n : nat) (s : string) : nat :=
  match s with
  | ("0" :: s')%string => nat_from_string1 (n * 10 + 0) s'
  | ("1" :: s')%string => nat_from_string1 (n * 10 + 1) s'
  | ("2" :: s')%string => nat_from_string1 (n * 10 + 2) s'
  | ("3" :: s')%string => nat_from_string1 (n * 10 + 3) s'
  | ("4" :: s')%string => nat_from_string1 (n * 10 + 4) s'
  | ("5" :: s')%string => nat_from_string1 (n * 10 + 5) s'
  | ("6" :: s')%string => nat_from_string1 (n * 10 + 6) s'
  | ("7" :: s')%string => nat_from_string1 (n * 10 + 7) s'
  | ("8" :: s')%string => nat_from_string1 (n * 10 + 8) s'
  | ("9" :: s')%string => nat_from_string1 (n * 10 + 9) s'
  | _ => n
  end.

Definition nat_from_string (s : string) : nat := nat_from_string1 0 s.

End STRING_OPERATIONS.

Definition isNum (ch : char) : bool := Ascii.leb "0"%char ch && Ascii.leb ch "9"%char.

Definition isLower (ch : char) : bool := Ascii.leb "a"%char ch && Ascii.leb ch "z"%char.

Definition isUpper (ch : char) : bool := Ascii.leb "A"%char ch && Ascii.leb ch "Z"%char.

Definition isAlpha (ch : char) : bool := isLower ch || isUpper ch.

Definition isAlphaNum (ch : char) : bool := isAlpha ch || isNum ch.

End Prelude.

Export Prelude.

Module PreludeTheory.

Import StringNotations ListNotations.

Lemma eqb_eq {A : Type} {hasEqDec : Prelude.hasEqDec A} (lhs : A) (rhs : A)
  : Prelude.eqb lhs rhs = true <-> lhs = rhs.
Proof.
  unfold Prelude.eqb. destruct (Prelude.eq_dec lhs rhs) as [H_yes | H_no].
  - split; [intros _; exact (H_yes) | intros _; reflexivity].
  - split; [intros H_false; inversion H_false | intros H_false; contradiction (H_no H_false)].
Qed.

Lemma eqb_neq {A : Type} {hasEqDec : Prelude.hasEqDec A} (lhs : A) (rhs : A)
  : Prelude.eqb lhs rhs = false <-> lhs <> rhs.
Proof.
  unfold Prelude.eqb. destruct (Prelude.eq_dec lhs rhs) as [H_yes | H_no].
  - split; [intros H_false; inversion H_false | intros H_false; contradiction (H_false H_yes)].
  - split; [intros _; exact (H_no) | intros _; reflexivity].
Qed.

Lemma option_ext_eq {A : Type} (lhs : option A) (rhs : option A)
  : lhs = rhs <-> << EXT_EQ : liftRel_option eq lhs rhs >>.
Proof. unnw. unfold liftRel_option. destruct lhs as [x | ], rhs as [y | ]; split; try (congruence || tauto). Qed.

Lemma list_ext_eq {A : Type} (lhs : list A) (rhs : list A)
  : lhs = rhs <-> << EXT_EQ : forall i : nat, liftRel_option eq (nth_error lhs i) (nth_error rhs i) >>.
Proof.
  unnw. split.
  - intros H_EQ i. rename lhs into xs, rhs into ys. destruct (nth_error xs i) as [xs_i | ] eqn: OBS_xs_i; destruct (nth_error ys i) as [ys_i | ] eqn: OBS_ys_i; cbn in *; try tauto; try congruence.
  - rename lhs into xs, rhs into ys. revert xs ys. induction xs as [ | x xs IH], ys as [ | y ys]; intros H_EQ; simpl.
    + reflexivity.
    + specialize H_EQ with (i := 0). cbn in H_EQ. tauto.
    + specialize H_EQ with (i := 0). cbn in H_EQ. tauto.
    + pose proof (H_EQ 0) as x_eq_y. cbn in x_eq_y. specialize (IH ys (fun i : nat => H_EQ (S i))). congruence.
Qed.

Lemma fold_left_ind {A : Type} {B : Type} (phi : A -> Prop) (f : A -> B -> A) (z0 : A) (xs : list B)
  (phi_z0 : phi z0)
  (phi_f_z_x_if_phi_z : forall z : A, forall x : B, << IH : phi z >> -> phi (f z x))
  : phi (fold_left f xs z0).
Proof.
  unnw. revert xs z0 phi_z0. induction xs as [ | x xs IH]; simpl; intros z phi_z.
  - exact (phi_z).
  - eapply IH with (z0 := f z x). eapply phi_f_z_x_if_phi_z with (z := z) (x := x). exact (phi_z).
Defined.

Lemma String_app_assoc (s1 : string) (s2 : string) (s3 : string)
  : ((s1 ++ s2) ++ s3)%string = (s1 ++ (s2 ++ s3))%string.
Proof.
  revert s2 s3. induction s1 as [ | ch1 s1 IH]; simpl; intros.
  - reflexivity.
  - eapply f_equal. eauto.
Qed.

Lemma String_app_nil_l (s1 : string)
  : ("" ++ s1)%string = s1.
Proof. reflexivity. Qed.

Lemma String_app_nil_r (s1 : string)
  : (s1 ++ "")%string = s1.
Proof. induction s1 as [ | ch1 s1 IH]; simpl; congruence. Qed.

Lemma String_app_length (s1 : string) (s2 : string)
  : length (s1 ++ s2)%string = length s1 + length s2.
Proof. induction s1 as [ | ch1 s1]; simpl; lia. Qed.

Lemma String_take_ge_length (n : nat) (s : string)
  (n_ge_length : n >= length s)
  : String_take n s = s.
Proof.
  revert n s n_ge_length. induction n as [ | n IH], s as [ | ch s]; simpl; intros ?.
  - reflexivity.
  - lia.
  - reflexivity.
  - eapply f_equal. eapply IH. lia.
Qed.

Lemma String_drop_ge_length (n : nat) (s : string)
  (n_ge_length : n >= length s)
  : String_drop n s = []%string.
Proof.
  revert n s n_ge_length. induction n as [ | n IH], s as [ | ch s]; simpl; intros ?.
  - reflexivity.
  - lia.
  - reflexivity.
  - eapply IH. lia.
Qed.

Lemma String_take_app_String_drop (n : nat) (s : string)
  : (String_take n s ++ String_drop n s)%string = s.
Proof.
  assert (n < length s \/ n >= length s) as [n_lt_length_s | n_ge_length] by lia.
  - revert s n_lt_length_s. induction n as [ | n IH].
    + intros s _. reflexivity.
    + intros s n_lt_length_s. destruct s as [ | ch s'].
      * reflexivity.
      * simpl. eapply f_equal. eapply IH. simpl in n_lt_length_s. lia.
  - rewrite String_take_ge_length; trivial.
    rewrite String_drop_ge_length; trivial.
    eapply String_app_nil_r.
Qed.

Lemma String_rev_app (s1 : string) (s2 : string)
  : String_rev (s1 ++ s2)%string = (String_rev s2 ++ String_rev s1)%string.
Proof.
  induction s1 as [ | ch1 s1 IH]; simpl.
  - rewrite String_app_nil_r. reflexivity.
  - rewrite IH. eapply String_app_assoc.
Qed.

Lemma String_rev_involute (s : string)
  : String_rev (String_rev s) = s.
Proof.
  induction s as [ | ch s IH]; simpl.
  - reflexivity.
  - rewrite String_rev_app, IH. reflexivity.
Qed.

Lemma String_rev_ind (phi : string -> Prop)
  (H_EmptyString : phi []%string)
  (H_String : forall ch : ascii, forall s : string, phi s -> phi (s ++ (ch :: [])%string)%string)
  : forall s : string, phi s.
Proof.
  intros s. rewrite <- String_rev_involute with (s := s).
  generalize (String_rev s). clear s. induction s as [ | ch s IH]; simpl.
  - eapply H_EmptyString%string.
  - eapply H_String. exact (IH).
Qed.

Lemma String_rev_dual (phi : string -> Prop)
  (H_rev : forall s : string, phi (String_rev s))
  : forall s : string, phi s.
Proof.
  induction s as [ | ch s _] using String_rev_ind.
  - eapply H_rev with (s := []%string).
  - rewrite <- String_rev_involute with (s := s).
    eapply H_rev with (s := (ch :: String_rev s)%string).
Qed.

Lemma String_rev_inj (s1 : string) (s2 : string)
  (REV_EQ : String_rev s1 = String_rev s2)
  : s1 = s2.
Proof.
  rewrite <- String_rev_involute with (s := s1).
  rewrite <- String_rev_involute with (s := s2).
  eapply f_equal. eassumption.
Qed.

Lemma String_cancel_l (s1 : string) (s2 : string) (s3 : string)
  (s1_app_s2_eq_s1_app_s3 : (s1 ++ s2)%string = (s1 ++ s3)%string)
  : s2 = s3.
Proof.
  revert s2 s3 s1_app_s2_eq_s1_app_s3. induction s1 as [ | ch1 s1 IH]; simpl; intros.
  - eauto.
  - inversion s1_app_s2_eq_s1_app_s3. eauto.
Qed.

Lemma String_cancel_r (s1 : string) (s2 : string) (s3 : string)
  (s1_app_s3_eq_s2_app_s3 : (s1 ++ s3)%string = (s2 ++ s3)%string)
  : s1 = s2.
Proof.
  revert s2 s3 s1_app_s3_eq_s2_app_s3. pattern s1. revert s1. eapply String_rev_dual.
  intros s1 s2. pattern s2. revert s2. eapply String_rev_dual.
  intros s2 s3. pattern s3. revert s3. eapply String_rev_dual.
  intros s3. do 2 rewrite <- String_rev_app.
  intros REV_EQ. apply String_rev_inj, String_cancel_l in REV_EQ. congruence.
Qed.

End PreludeTheory.

Module P.

Import StringNotations ListNotations.

Definition parserT (M : Type -> Type) (A : Type) : Type := string -> M (A * string)%type.

#[global]
Instance parserT_isMonad {M : Type -> Type} (M_isMonad : isMonad M) : isMonad (parserT M) :=
  { pure {A} := curry pure
  ; bind {A} {B} (m : parserT M A) (k : A -> parserT M B) := fun s : string => m s >>= uncurry k
  }.

#[global]
Instance parserT_isAlternative {M : Type -> Type} (M_isAlternative : isAlternative M) : isAlternative (parserT M) :=
  { empty {A} := fun s : string => empty
  ; alt {A} (p1 : parserT M A) (p2 : parserT M A) := fun s : string => p1 s <|> p2 s
  }.

Definition parser : Type -> Type := parserT option.

Definition eqP {A : Type} (lhs : parser A) (rhs : parser A) : Prop := forall s : string, lhs s = rhs s.

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
  { eqProp := @eqP A
  ; eqProp_Equivalence := @eqP_Equivalence A
  }.

#[global]
Add Parametric Morphism {A : Type} {B : Type}
  : (@bind parser (parserT_isMonad option_isMonad) A B) with signature (eqProp (isSetoid := parser_isSetoid) ==> eqProp (isSetoid := arrow_isSetoid parser_isSetoid) ==> eqProp (isSetoid := parser_isSetoid)) as bind_lifts_eqP.
Proof. intros m1 m2 m1_eq_m2 k1 k2 k1_eq_k2 s. simpl. rewrite m1_eq_m2 with (s := s). destruct (m2 s) as [[x s'] | ]; simpl; trivial. eapply k1_eq_k2. Qed.

Lemma bind_assoc {A : Type} {B : Type} {C : Type} (m0 : parser A) (k1 : A -> parser B) (k2 : B -> parser C)
  : ((m0 >>= k1) >>= k2) == (m0 >>= fun x => (k1 x >>= k2)).
Proof. intros s. simpl. destruct (m0 s) as [[x s'] | ]; reflexivity. Qed.

Lemma bind_pure_l {A : Type} {B : Type} (x : A) (k : A -> parser B)
  : (pure x >>= k) == k x.
Proof. intros s. simpl. reflexivity. Qed.

Lemma bind_pure_r {A : Type} (m : parser A)
  : (m >>= pure) == m.
Proof. intros s. simpl. destruct (m s) as [[x s'] | ]; reflexivity. Qed.

#[global]
Add Parametric Morphism {A : Type}
  : (@alt parser (parserT_isAlternative option_isAlternative) A) with signature (eqProp (isSetoid := parser_isSetoid) ==> eqProp (isSetoid := parser_isSetoid) ==> eqProp (isSetoid := parser_isSetoid)) as alt_lifts_eqP.
Proof. intros lhs1 rhs1 lhs1_eq_rhs1 lhs2 rhs2 lhs2_eq_rhs2 s. simpl. rewrite lhs1_eq_rhs1 with (s := s). rewrite lhs2_eq_rhs2 with (s := s). reflexivity. Qed.

Lemma alt_assoc {A : Type} (p1 : parser A) (p2 : parser A) (p3 : parser A)
  : (p1 <|> p2) <|> p3 == p1 <|> (p2 <|> p3).
Proof. intros s. simpl. destruct (p1 s) as [[x1 s'] | ]; reflexivity. Qed.

Lemma alt_empty_l {A : Type} (p : parser A)
  : empty <|> p == p.
Proof. intros s. simpl. reflexivity. Qed.

Lemma alt_empty_r {A : Type} (p : parser A)
  : p <|> empty == p.
Proof. intros s. simpl. destruct (p s) as [[x s'] | ]; reflexivity. Qed.

Definition string_wf : forall s : string, Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s :=
  Prelude.acc_rel String.length Nat.lt Prelude.acc_lt.

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

Lemma isLt_implies_isLe {A : Type} (p : parser A)
  (p_isLt : isLt p)
  : isLe p.
Proof.
  intros s. pose proof (p_isLt s) as H.
  destruct (p s) as [[x s'] | ]; trivial. lia.
Qed.

#[global]
Add Parametric Morphism {A : Type}
  : (@isLt A) with signature (eqProp ==> iff) as isLt_compatWith_eqP.
Proof.
  assert (claim : forall p1 : parser A, forall p2 : parser A, p1 == p2 -> isLt p1 -> isLt p2).
  { intros p1 p2 p1_eq_p2 p1_isLt s. rewrite <- p1_eq_p2 with (s := s). exact (p1_isLt s). }
  intros p1 p2 p1_eq_p2; split; [intros p1_isLt | intros p2_isLt; symmetry in p1_eq_p2]; eauto.
Qed.

#[global]
Add Parametric Morphism {A : Type}
  : (@isLe A) with signature (eqProp ==> iff) as isLe_compatWith_eqP.
Proof.
  assert (claim : forall p1 : parser A, forall p2 : parser A, p1 == p2 -> isLe p1 -> isLe p2).
  { intros p1 p2 p1_eq_p2 p1_isLe s. rewrite <- p1_eq_p2 with (s := s). exact (p1_isLe s). }
  intros p1 p2 p1_eq_p2; split; [intros p1_isLe | intros p2_isLe; symmetry in p1_eq_p2]; eauto.
Qed.

Lemma bind_m_k_isLt_if_m_isLt_and_k_isLe {A : Type} {B : Type} (m : parser A) (k : A -> parser B)
  (m_isLt : isLt m)
  (k_isLe : forall x : A, isLe (k x))
  : isLt (bind (A := A) (B := B) m k).
Proof.
  intros s. pose proof (m_isLt s) as H0.
  simpl. destruct (m s) as [[x' s'] | ]; trivial.
  simpl. pose proof (k_isLe x' s') as H1.
  destruct (k x' s') as [[x'' s''] | ]; trivial. lia.
Qed.

Lemma bind_m_k_isLt_if_m_isLe_and_k_isLt {A : Type} {B : Type} (m : parser A) (k : A -> parser B)
  (m_isLe : isLe m)
  (k_isLt : forall x : A, isLt (k x))
  : isLt (bind (A := A) (B := B) m k).
Proof.
  intros s. pose proof (m_isLe s) as H0.
  simpl. destruct (m s) as [[x' s'] | ]; trivial.
  simpl. pose proof (k_isLt x' s') as H1.
  destruct (k x' s') as [[x'' s''] | ]; trivial. lia.
Qed.

Lemma bind_m_k_isLe_if_m_isLe_and_k_isLe {A : Type} {B : Type} (m : parser A) (k : A -> parser B)
  (m_isLe : isLe m)
  (k_isLe : forall x : A, isLe (k x))
  : isLe (bind (A := A) (B := B) m k).
Proof.
  intros s. pose proof (m_isLe s) as H0.
  simpl. destruct (m s) as [[x' s'] | ]; trivial.
  simpl. pose proof (k_isLe x' s') as H1.
  destruct (k x' s') as [[x'' s''] | ]; trivial. lia.
Qed.

Lemma pure_isLe {A : Type} (x : A)
  : isLe (pure (A := A) x).
Proof. intros s. simpl. reflexivity. Qed.

Lemma alt_p1_p2_isLt_if_p1_isLt_and_p2_isLt {A : Type} (p1 : parser A) (p2 : parser A)
  (p1_isLt : isLt p1)
  (p2_isLt : isLt p2)
  : isLt (alt (A := A) p1 p2).
Proof.
  intros s. simpl. pose proof (p1_isLt s) as H1. destruct (p1 s) as [[x s'] | ].
  - eapply H1.
  - pose proof (p2_isLt s) as H2. destruct (p2 s) as [[x' s'] | ]; trivial.
Qed.

Lemma alt_p1_p2_isLe_if_p1_isLe_and_p2_isLe {A : Type} (p1 : parser A) (p2 : parser A)
  (p1_isLe : isLe p1)
  (p2_isLe : isLe p2)
  : isLe (alt (A := A) p1 p2).
Proof.
  intros s. simpl. pose proof (p1_isLe s) as H1. destruct (p1 s) as [[x s'] | ].
  - eapply H1.
  - pose proof (p2_isLe s) as H2. destruct (p2 s) as [[x' s'] | ]; trivial.
Qed.

Lemma empty_isLt {A : Type}
  : isLt (empty (A := A)).
Proof.
  intros s. simpl. trivial.
Qed.

Section PARSER_COMBINATORS.

Definition satisfyP (cond : char -> bool) : parser char :=
  fun s : string =>
  match s with
  | []%string => None
  | (ch :: s')%string => if cond ch then Some (ch, s') else None
  end.

Lemma satisfyP_isLt (cond : char -> bool)
  : isLt (satisfyP cond).
Proof.
  intros s. unfold satisfyP. destruct s as [ | ch s']; trivial.
  destruct (cond ch); trivial. simpl. red. reflexivity.
Qed.

Definition itemP : parser char :=
  satisfyP (fun ch : char => true).

Lemma itemP_isLt
  : isLt itemP.
Proof. eapply satisfyP_isLt. Qed.

Definition stringP : string -> parser unit := sequenceM_ ∘ mapFromString (satisfyP ∘ Ascii.eqb).

Lemma stringP_isLt (s : string)
  (s_ne_nil : length s > 0)
  : isLt (stringP s).
Proof.
  rename s into str, s_ne_nil into length_str_gt_0.
  enough (to_show : length str = 0 \/ isLt (stringP str)).
  { destruct to_show; [lia | eassumption]. }
  clear length_str_gt_0. induction str as [ | ch str IH_str].
  - left. reflexivity.
  - simpl. right. intros s.
    revert ch str IH_str. induction (string_wf s) as [s _ IH]. intros. simpl.
    red. red. simpl. red. pose proof (satisfyP_isLt (Ascii.eqb ch) s) as length_s_gt_length_s'.
    destruct (satisfyP (Ascii.eqb ch) s) as [[x s'] | ] eqn: H_OBS; trivial.
    simpl. specialize (IH s' length_s_gt_length_s'). destruct str as [ | ch' str'].
    + assert (IH_claim : length "" = 0 \/ isLt (stringP "")).
      { left. reflexivity. }
      specialize (IH ch []%string IH_claim). do 2 red in IH. simpl in IH. red in IH. simpl. eassumption.
    + assert (IH_claim : length (ch' :: str')%string = 0 \/ isLt (stringP (ch' :: str')%string)).
      { right. destruct IH_str as [IH_str | IH_str]; [inversion IH_str | eassumption]. }
      specialize (IH ch (ch' :: str')%string IH_claim). do 2 red in IH. simpl in IH. red in IH.
      destruct IH_str as [IH_str | IH_str].
      * inversion IH_str.
      * specialize (IH_str s'). red in IH_str. red in IH_str.
        destruct (sequenceM_ (mapFromString (satisfyP ∘ Ascii.eqb) (ch' :: str')%string) s') as [[x' s''] | ] eqn: H_OBS'; trivial. lia.
Qed.

Lemma stringP_isLe (s : string)
  : isLe (stringP s).
Proof.
  destruct s as [ | ch s'].
  - intros s. cbn. lia.
  - eapply isLt_implies_isLe. eapply stringP_isLt. cbn. lia.
Qed.

#[program]
Fixpoint someP {A : Type} (p : parser A) (p_isLt : isLt p) (s : string) {measure (length s)} : option (list A * string) :=
  match p s with
  | None => None
  | Some (x, s') =>
    match someP p p_isLt s' with
    | None => Some ([x], s')
    | Some (xs, s'') => Some (x :: xs, s'')
    end
  end.
Next Obligation. pose proof (p_isLt s) as H. rewrite <- Heq_anonymous in H. eassumption. Defined.

Lemma someP_unfold {A : Type} (p : parser A) (p_isLt : isLt p) (s : string) :
  someP p p_isLt s =
  match p s with
  | None => None
  | Some (x, s') =>
    match someP p p_isLt s' with
    | None => Some ([x], s')
    | Some (xs, s'') => Some (x :: xs, s'')
    end
  end.
Proof.
  unfold someP at 1; unfold someP_func; rewrite WfExtensionality.fix_sub_eq_ext; destruct (p s) as [[x s'] | ] eqn: OBS_p_s; simpl.
  - rewrite OBS_p_s; destruct (someP p p_isLt s') as [[xs s''] | ] eqn: OBS_someP_p_s'.
    + unfold someP, someP_func in OBS_someP_p_s'; rewrite OBS_someP_p_s'; reflexivity.
    + unfold someP, someP_func in OBS_someP_p_s'; rewrite OBS_someP_p_s'; reflexivity.
  - rewrite OBS_p_s; reflexivity.
Qed.

Lemma someP_isLt {A : Type} (p : parser A)
  (p_isLt : isLt p)
  : isLt (someP p p_isLt).
Proof.
  intros s. induction (string_wf s) as [s _ IH]. rewrite someP_unfold. pose proof (p_isLt s) as length_s_gt_length_s'. destruct (p s) as [[x s'] | ]; trivial. specialize (IH s' length_s_gt_length_s').
  destruct (someP p p_isLt s') as [[xs s''] | ]; lia.
Qed.

Definition manyP {A : Type} (p : parser A) (p_isLt : isLt p) : parser (list A) := someP p p_isLt <|> pure [].

Lemma manyP_isLe {A : Type} (p : parser A)
  (p_isLt : isLt p)
  : isLe (manyP p p_isLt).
Proof.
  intros s. unfold manyP. simpl.
  pose proof (someP_isLt p p_isLt s) as H1.
  destruct (someP p p_isLt s) as [[x s'] | ].
  - lia.
  - simpl. reflexivity.
Qed.

Theorem someP_defn {A : Type} (p : parser A) (p_isLt : isLt p)
  : someP p p_isLt == (p >>= fun x => manyP p p_isLt >>= fun xs => pure (x :: xs)).
Proof. intros s. rewrite someP_unfold at 1. unfold manyP. simpl. destruct (p s) as [[x s'] | ]; try reflexivity. simpl. destruct (someP p p_isLt s') as [[xs s''] | ]; try reflexivity. Qed.

Theorem manyP_defn {A : Type} (p : parser A) (p_isLt : isLt p)
  : manyP p p_isLt == someP p p_isLt <|> pure [].
Proof. reflexivity. Qed.

Lemma someP_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
  (p1_eq_p2 : p1 == p2)
  : someP p1 p1_isLt == someP p2 p2_isLt.
Proof.
  intros s. induction (string_wf s) as [s _ IH]. do 2 rewrite someP_unfold.
  pose proof (p1_eq_p2 s) as p1_s_eq_p2_s. rewrite p1_s_eq_p2_s. destruct (p2 s) as [[x s'] | ]; trivial.
  rewrite IH; trivial. pose proof (p1_isLt s) as length_s_gt_length_s'. rewrite p1_s_eq_p2_s in length_s_gt_length_s'. eassumption.
Qed.

Lemma manyP_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
  (p1_eq_p2 : p1 == p2)
  : manyP p1 p1_isLt == manyP p2 p2_isLt.
Proof. now unfold manyP; rewrite someP_lifts_eqP with (p1_isLt := p1_isLt) (p2_isLt := p2_isLt) (p1_eq_p2 := p1_eq_p2). Qed.

Definition spaceP : parser unit :=
  (manyP (satisfyP (fun ch : char => Ascii.eqb ch " "%char)) (satisfyP_isLt _)) >>= fun _ => pure tt.

Lemma spaceP_isLe
  : isLe spaceP.
Proof.
  eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
  - eapply manyP_isLe.
  - intros _. eapply pure_isLe.
Qed.

Definition tokenP {A : Type} (p : parser A) : parser A :=
  spaceP >>= fun _ => p >>= fun v => spaceP >>= fun _ => pure v.

Lemma tokenP_isLt {A : Type} (p : parser A)
  (p_isLt : isLt p)
  : isLt (tokenP p).
Proof.
  unfold tokenP. eapply bind_m_k_isLt_if_m_isLe_and_k_isLt.
  - eapply spaceP_isLe.
  - intros _. eapply bind_m_k_isLt_if_m_isLt_and_k_isLe.
    + exact (p_isLt).
    + intros x. eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
      * eapply spaceP_isLe.
      * intros _. eapply pure_isLe.
Qed.

Lemma tokenP_isLe {A : Type} (p : parser A)
  (p_isLe : isLe p)
  : isLe (tokenP p).
Proof.
  unfold tokenP. eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
  - eapply spaceP_isLe.
  - intros _. eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
    + exact (p_isLe).
    + intros x. eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
      * eapply spaceP_isLe.
      * intros _. eapply pure_isLe.
Qed.

Definition symbolP (s : string) : parser unit :=
  tokenP (stringP s).

Lemma symbolP_isLt (s : string)
  (s_ne_nil : length s > 0)
  : isLt (symbolP s).
Proof. eapply tokenP_isLt. eapply stringP_isLt. eassumption. Qed.

Definition digitP : parser char :=
  satisfyP isNum.

Lemma digitP_isLt
  : isLt digitP.
Proof. eapply satisfyP_isLt. Qed.

Definition lowerP : parser char :=
  satisfyP isLower.

Lemma lowerP_isLt
  : isLt lowerP.
Proof. eapply satisfyP_isLt. Qed.

Definition upperP : parser char :=
  satisfyP isUpper.

Lemma upperP_isLt
  : isLt upperP.
Proof. eapply satisfyP_isLt. Qed.

Definition letterP : parser char :=
  satisfyP isAlpha.

Lemma letterP_isLt
  : isLt letterP.
Proof. eapply satisfyP_isLt. Qed.

Definition alphanumP : parser char :=
  satisfyP isAlphaNum.

Lemma alphanumP_isLt
  : isLt alphanumP.
Proof. eapply satisfyP_isLt. Qed.

Definition charP (ch : char) : parser unit :=
  satisfyP (Ascii.eqb ch) >>= fun _ => pure tt.

Lemma charP_isLt (ch : char)
  : isLt (charP ch).
Proof.
  eapply bind_m_k_isLt_if_m_isLt_and_k_isLe.
  - eapply satisfyP_isLt.
  - intros _. eapply pure_isLe.
Qed.

Definition optMinusP : parser bool :=
  (symbolP "-" >>= fun _ => pure true) <|> pure false.

Lemma optMinusP_isLe
  : isLe optMinusP.
Proof.
  eapply alt_p1_p2_isLe_if_p1_isLe_and_p2_isLe.
  - eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
    + eapply isLt_implies_isLe. eapply symbolP_isLt. simpl; eauto.
    + intros _. eapply pure_isLe.
  - eapply pure_isLe. 
Qed.

Definition naturalP : parser nat :=
  (someP digitP (satisfyP_isLt (fun ch : char => ("0" <=? ch)%char && (ch <=? "9")%char))) >>= (fun s => pure (nat_from_string (mk_string s))).

Lemma naturalP_isLt
  : isLt naturalP.
Proof.
  eapply bind_m_k_isLt_if_m_isLt_and_k_isLe.
  - eapply someP_isLt.
  - intros str. eapply pure_isLe.
Qed.

Definition integerP : parser Z :=
  optMinusP >>= fun b => naturalP >>= fun n => if b then pure ((-1) * Z.of_nat n)%Z else pure (Z.of_nat n).

Lemma integerP_isLt
  : isLt integerP.
Proof.
  eapply bind_m_k_isLt_if_m_isLe_and_k_isLt.
  - eapply alt_p1_p2_isLe_if_p1_isLe_and_p2_isLe.
    + eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
      * eapply isLt_implies_isLe. eapply tokenP_isLt. eapply stringP_isLt. eauto.
      * intros _. eapply pure_isLe.
    + eapply pure_isLe.
  - intros b. eapply bind_m_k_isLt_if_m_isLt_and_k_isLe.
    + eapply naturalP_isLt.
    + intros n. destruct b as [ | ].
      * eapply pure_isLe.
      * eapply pure_isLe.
Qed.

Definition identP : parser string :=
  lowerP >>= fun x => manyP alphanumP (satisfyP_isLt _) >>= fun xs => pure (x :: mk_string xs)%string.

Lemma identP_isLt
  : isLt identP.
Proof.
  eapply bind_m_k_isLt_if_m_isLt_and_k_isLe.
  - eapply satisfyP_isLt.
  - intros ch. eapply bind_m_k_isLe_if_m_isLe_and_k_isLe.
    + eapply manyP_isLe.
    + intros chs. eapply pure_isLe.
Qed.

Definition identifierP : parser string :=
  tokenP identP.

Lemma identifierP_isLt
  : isLt identifierP.
Proof.
  eapply tokenP_isLt. eapply identP_isLt.
Qed.

End PARSER_COMBINATORS.

End P.

Module Hs.

Import StringNotations ListNotations.

Inductive strSQLElem : Set :=
| Text : string -> strSQLElem
| Hole : string -> strSQLElem.

Inductive value : Set :=
| ColName : string -> value
| StrVal  : string -> value
| IntVal  : Z      -> value
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

#[global]
Instance cols_hasEqDec
  : hasEqDec cols.
Proof with try ((left; congruence) || (right; congruence)).
  change (forall lhs : cols, forall rhs : cols, {lhs = rhs} + {lhs <> rhs}).
  intros [ | x] [ | y]...
  pose proof (Prelude.eq_dec x y) as [H_EQ | H_NE]...
Defined.

#[global]
Instance value_hasEqDec
  : hasEqDec value.
Proof with try ((left; congruence) || (right; congruence)).
  change (forall lhs : value, forall rhs : value, {lhs = rhs} + {lhs <> rhs}).
  induction lhs as [cn1 | s1 | i1 | v1], rhs as [cn2 | s2 | i2 | v2]...
  - pose proof (Prelude.eq_dec cn1 cn2) as [H_EQ | H_NE]...
  - pose proof (Prelude.eq_dec s1 s2) as [H_EQ | H_NE]...
  - pose proof (Prelude.eq_dec i1 i2) as [H_EQ | H_NE]...
  - pose proof (Prelude.eq_dec v1 v2) as [H_EQ | H_NE]...
Defined.

#[global]
Instance term_hasEqDec
  : hasEqDec term.
Proof with try ((left; congruence) || (right; congruence)).
  change (forall lhs : term, forall rhs : term, {lhs = rhs} + {lhs <> rhs}).
  intros [v1_1 v2_1] [v1_2 v2_2].
  pose proof (Prelude.eq_dec v1_1 v1_2) as [H_EQ1 | H_NE1]...
  pose proof (Prelude.eq_dec v2_1 v2_2) as [H_EQ2 | H_NE2]...
Defined.

#[global]
Instance pred_hasEqDec
  : hasEqDec pred.
Proof with try ((left; congruence) || (right; congruence)).
  change (forall lhs : pred, forall rhs : pred, {lhs = rhs} + {lhs <> rhs}).
  induction lhs as [p1_1 IH1 p2_1 IH2 | t_1], rhs as [p1_2 p2_2 | t_2]...
  - pose proof (IH1 p1_2) as [H_EQ1 | H_NE1]...
    pose proof (IH2 p2_2) as [H_EQ2 | H_NE2]...
  - pose proof (Prelude.eq_dec t_1 t_2) as [H_EQ | H_NE]... 
Defined.

#[global]
Instance sql_hasEqDec
  : hasEqDec sql.
Proof with try ((left; congruence) || (right; congruence)).
  change (forall lhs : sql, forall rhs : sql, {lhs = rhs} + {lhs <> rhs}).
  intros [x1 x2 [x3 | ]] [y1 y2 [y3 | ]]...
  - pose proof (Prelude.eq_dec x1 y1) as [H_EQ1 | H_NE1]...
    pose proof (Prelude.eq_dec x2 y2) as [H_EQ2 | H_NE2]...
    pose proof (Prelude.eq_dec x3 y3) as [H_EQ3 | H_NE3]...
  - pose proof (Prelude.eq_dec x1 y1) as [H_EQ1 | H_NE1]...
    pose proof (Prelude.eq_dec x2 y2) as [H_EQ2 | H_NE2]...
Defined.

Section NORM.

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
Next Obligation.
  simpl. repeat rewrite Nat.add_0_r; red. lia.
Defined.

Example normPred_example1
  (p1 := termPred (equalTerm (ColName "A") (ColName "B")))
  (p2 := termPred (equalTerm (ColName "D") (ColName "E")))
  (p3 := termPred (equalTerm (ColName "G") (ColName "H")))
  (p4 := termPred (equalTerm (ColName "J") (ColName "K")))
  : normPred (orPred (orPred p1 p2) (orPred p3 p4))
  = orPred p1 (orPred p2 (orPred p3 p4)).
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

Definition normMaybePred (maybePred : option pred) : option pred :=
  match maybePred with
  | None => None
  | Some pred => Some (normPred pred)
  end.

Definition norm (sql : Hs.sql) : Hs.sql :=
  match sql with
  | sqlSFW cols tbl maybePred => sqlSFW cols tbl (normMaybePred maybePred)
  end.

End NORM.

Definition env : Set := list (string * value).

Section APPLY.

Definition applyValue (e : env) (v : value) : value :=
  match v with
  | ColName cn => ColName cn
  | StrVal s => StrVal s
  | IntVal i => IntVal i
  | Var x =>
    match lookup x e with
    | None => Var x
    | Some v' => v'
    end
  end.

Definition applyTerm (e : env) (t : term) : term :=
  match t with
  | equalTerm v1 v2 => equalTerm (applyValue e v1) (applyValue e v2)
  end.

Fixpoint applyPred (e : env) (p : pred) : pred :=
  match p with
  | termPred t => termPred (applyTerm e t)
  | orPred p1 p2 => orPred (applyPred e p1) (applyPred e p2)
  end.

Definition applyMaybePred (e : env) (maybePred : option pred) : option pred :=
  match maybePred with
  | None => None
  | Some p => Some (applyPred e p)
  end.

Definition applySQL (e : env) (sql : Hs.sql) : Hs.sql :=
  match sql with
  | sqlSFW cols tbl maybePred => sqlSFW cols tbl (applyMaybePred e maybePred)
  end.

End APPLY.

Definition injection (v : string) (s : string) (sql : Hs.sql) : Hs.sql := applySQL [(v, StrVal s)] sql.

Section INJECTION_FREE.

Definition injFreeValue (lhs : value) (rhs : value) : bool :=
  match lhs, rhs with
  | ColName c1, ColName c2 => Prelude.eqb c1 c2
  | StrVal s1, StrVal s2 => Prelude.eqb s1 s2
  | IntVal i1, IntVal i2 => Prelude.eqb i1 i2
  | Var x, _ => true
  | _, Var x => true
  | _, _ => false
  end.

Definition injFreeTerm (lhs : term) (rhs : term) : bool :=
  match lhs, rhs with
  | equalTerm v11 v12, equalTerm v21 v22 => injFreeValue v11 v21 && injFreeValue v12 v22
  end.

Fixpoint injFreePred (lhs : pred) (rhs : pred) : bool :=
  match lhs, rhs with
  | termPred t1, termPred t2 => injFreeTerm t1 t2
  | orPred pred11 pred12, orPred pred21 pred22 => injFreePred pred11 pred21 && injFreePred pred12 pred22
  | _, _ => false
  end.

Definition injFreeMaybePred (lhs : option pred) (rhs : option pred) : bool :=
  match lhs, rhs with
  | Some p1, Some p2 => injFreePred p1 p2
  | None, None => true
  | _, _ => false
  end.

Definition injFree (s1 : sql) (s2 : sql) : bool :=
  match s1, s2 with
  | sqlSFW cols1 tbl1 maybePred1, sqlSFW cols2 tbl2 maybePred2 => Prelude.eqb cols1 cols2 && Prelude.eqb tbl1 tbl2 && injFreeMaybePred maybePred1 maybePred2
  end.

End INJECTION_FREE.

Section PRINTER.

Fixpoint ppString1 (s : string) : string :=
  match s with
  | []%string => ""%string
  | ("'"%char :: s')%string => ("''" ++ ppString1 s')%string
  | (ch :: s')%string => (ch :: ppString1 s')%string
  end.

Definition ppString (s : string) : string :=
  String_concat ["'"%string; ppString1 s; "'"%string]%list.

Definition ppValue (v : value) : string :=
  match v with
  | ColName s => s
  | StrVal s => ppString s
  | IntVal i => Z_to_string i
  | Var x => ("{" ++ x ++ "}")%string
  end.

Definition ppTerm (t : term) : string :=
  match t with
  | equalTerm v1 v2 => String_concat [ppValue v1; " = "%string; ppValue v2]
  end.

Fixpoint ppPred (p : pred) : string :=
  match p with
  | termPred t => ppTerm t
  | orPred p q => String_concat [ppPred p; " or "%string; ppPred q]
  end.

Definition ppWhere (maybePred : option pred) : string :=
  match maybePred with
  | None => ""%string
  | Some pred => String_concat [" where "%string; ppPred pred]
  end.

Definition ppTbl (tbl : string) : string := tbl.

Fixpoint ppCols_aux (cs : list string) {struct cs} : string :=
  match cs with
  | [] => ""%string
  | [c1] => c1
  | c1 :: cs' => String_concat [c1; ","%string; ppCols_aux cs']
  end.

Definition ppCols (c : cols) : string :=
  match c with
  | star => "*"%string
  | colNames cs => ppCols_aux cs
  end.

Definition printSQL (s : sql) : string :=
  match s with
  | sqlSFW cols tbl maybePred => String_concat ["select "%string; ppCols cols; " from "%string; ppTbl tbl; ppWhere maybePred]
  end.

End PRINTER.

Section PARSER.

#[program]
Fixpoint sqlstringinP (s0 : string) {measure (length s0)} : option (string * string) :=
  match
    match P.charP "'"%char s0 with
    | None => None
    | Some (_, s1) =>
      match P.charP "'"%char s1 with
      | None => None
      | Some (_, s2) =>
        match sqlstringinP s2 with
        | None => None
        | Some (text, s3) => Some (("'"%char :: text)%string, s3)
        end
      end
    end
  with
  | None =>
    match
      match P.charP "'"%char s0 with
      | None => None
      | Some (_, s1) => Some (""%string, s1)
      end
    with
    | None =>
      match P.itemP s0 with
      | None => None
      | Some (c, s1) =>
        match sqlstringinP s1 with
        | None => None
        | Some (text, s2) => Some ((c :: text)%string, s2)
        end
      end
    | Some res => Some res
    end
  | Some res => Some res
  end.
Next Obligation.
  pose proof (P.charP_isLt "'"%char s1) as H1. rewrite <- Heq_anonymous in H1.
  pose proof (P.charP_isLt "'"%char s0) as H2. rewrite <- Heq_anonymous0 in H2.
  etransitivity; eassumption.
Defined.
Next Obligation.
  pose proof (P.itemP_isLt s0) as H1. rewrite <- Heq_anonymous in H1.
  eassumption.
Defined.

Lemma sqlstringinP_unfold (s0 : string) :
  sqlstringinP s0 =
  match
    match P.charP "'"%char s0 with
    | None => None
    | Some (_, s1) =>
      match P.charP "'"%char s1 with
      | None => None
      | Some (_, s2) =>
        match sqlstringinP s2 with
        | None => None
        | Some (text, s3) => Some (("'"%char :: text)%string, s3)
        end
      end
    end
  with
  | None =>
    match
      match P.charP "'"%char s0 with
      | None => None
      | Some (_, s1) => Some (""%string, s1)
      end
    with
    | None =>
      match P.itemP s0 with
      | None => None
      | Some (c, s1) =>
        match sqlstringinP s1 with
        | None => None
        | Some (text, s2) => Some (("'"%char :: text)%string, s2)
        end
      end
    | Some res => Some res
    end
  | Some res => Some res
  end.
Proof.
Admitted.

Theorem sqlstringinP_defn
  : sqlstringinP == (P.charP "'"%char >>= fun _ => P.charP "'"%char >>= fun _ => sqlstringinP >>= fun text => pure (("'"%char :: text)%string)) <|> (P.charP "'"%char >>= fun _ => pure ""%string) <|> (P.itemP >>= fun c => sqlstringinP >>= fun text => pure ("'"%char :: text)%string).
Proof with trivial.
  intros s0. rewrite sqlstringinP_unfold at 1. simpl...
  destruct (P.charP "'" s0) as [[x1 s1] | ] eqn: H_OBS1; simpl...
  destruct (P.charP "'" s1) as [[x2 s2] | ] eqn: H_OBS2; simpl...
  destruct (sqlstringinP s2) as [[x3 s3] | ] eqn: H_OBS3; simpl...
Qed.

Lemma sqlstringinP_isLt
  : P.isLt sqlstringinP.
Proof with trivial.
  intros s. induction (P.string_wf s) as [s0 _ IH]. rewrite sqlstringinP_unfold; simpl.
  pose proof (P.charP_isLt "'" s0) as H1. destruct (P.charP "'" s0) as [[x1 s1] | ] eqn: H_OBS1; simpl...
  - pose proof (P.charP_isLt "'" s1) as H2. destruct (P.charP "'" s1) as [[x2 s2] | ] eqn: H_OBS2; simpl...
    assert (length_gt : length s2 < length s0) by lia.
    specialize (IH s2 length_gt). destruct (sqlstringinP s2) as [[x3 s3] | ] eqn: H_OBS3; simpl... lia.
  - pose proof (P.itemP_isLt s0) as H2. destruct (P.itemP s0) as [[x1 s1] | ] eqn: H_OBS2...
    specialize (IH s1 H2). destruct (sqlstringinP s1) as [[x3 s3] | ] eqn: H_OBS3... lia.
Qed.

Definition sqlstringP : P.parser string :=
  P.charP "'"%char >>= fun _ => sqlstringinP >>= fun text => pure text.

Lemma sqlstringP_isLt
  : P.isLt sqlstringP.
Proof.
  eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
  - eapply P.charP_isLt.
  - intros _. eapply P.bind_m_k_isLe_if_m_isLe_and_k_isLe.
    + eapply P.isLt_implies_isLe. eapply sqlstringinP_isLt.
    + intros x. eapply P.pure_isLe.
Qed.

Definition parsevalueP : P.parser value :=
  (P.identifierP >>= fun colName => pure (ColName colName)) <|> (sqlstringP >>= fun sqlstr => pure (StrVal sqlstr)) <|> (P.integerP >>= fun i => pure (IntVal i)) <|> (P.symbolP "{" >>= fun _ => P.identifierP >>= fun v => P.symbolP "}" >>= fun _ => pure (Var v)).

Lemma parsevalueP_isLt
  : P.isLt parsevalueP.
Proof.
  eapply P.alt_p1_p2_isLt_if_p1_isLt_and_p2_isLt.
  - eapply P.alt_p1_p2_isLt_if_p1_isLt_and_p2_isLt.
    + eapply P.alt_p1_p2_isLt_if_p1_isLt_and_p2_isLt.
      * eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
        { eapply P.tokenP_isLt. eapply P.identP_isLt. }
        { intros s. eapply P.pure_isLe. }
      * eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
        { eapply sqlstringP_isLt. }
        { intros s. eapply P.pure_isLe. }
    + eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
      * eapply P.integerP_isLt.
      * intros i. eapply P.pure_isLe.
  - eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
    + eapply P.tokenP_isLt. eapply P.stringP_isLt. eauto.
    + intros _. eapply P.bind_m_k_isLe_if_m_isLe_and_k_isLe.
      * eapply P.isLt_implies_isLe. eapply P.identifierP_isLt.
      * intros s. eapply P.isLt_implies_isLe. eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
        { eapply P.tokenP_isLt. eapply P.stringP_isLt. eauto. }
        { intros _. eapply P.pure_isLe. }
Qed.

Definition parsetermP : P.parser term :=
  parsevalueP >>= fun v1 => P.symbolP "=" >>= fun _ => parsevalueP >>= fun v2 => pure (equalTerm v1 v2).

Lemma parsetermP_isLt
  : P.isLt parsetermP.
Proof.
  eapply P.bind_m_k_isLt_if_m_isLe_and_k_isLt.
  - eapply P.isLt_implies_isLe. eapply parsevalueP_isLt.
  - intros v. eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
    + eapply P.tokenP_isLt. eapply P.stringP_isLt. eauto.
    + intros _. eapply P.bind_m_k_isLe_if_m_isLe_and_k_isLe.
      * eapply P.isLt_implies_isLe. eapply parsevalueP_isLt.
      * intros v'. eapply P.pure_isLe.
Qed.

#[program]
Fixpoint predicate1P (s0 : string) {measure (length s0)} : option ((pred -> pred) * string) :=
  match
    match P.symbolP "or"%string s0 with
    | None => None
    | Some (_, s1) =>
      match
        match parsetermP s1 with
        | None => None
        | Some (term, s2) =>
          match predicate1P s2 with
          | None => None
          | Some (f, s3) => Some (f (termPred term), s3)
          end
        end
      with
      | None => None
      | Some (pred2, s2) =>
        match predicate1P s2 with
        | None => None
        | Some (f, s3) => Some ((fun pred1 => f (orPred pred1 pred2)), s3)
        end
      end
    end
  with
  | None => Some ((fun x => x), s0)
  | Some res => Some res
  end.
Next Obligation.
  assert (claim : P.isLt (P.symbolP "or"%string)).
  { eapply P.tokenP_isLt. eapply P.stringP_isLt. simpl. eauto. }
  pose proof (claim s0) as H1. rewrite <- Heq_anonymous0 in H1. 
  pose proof (parsetermP_isLt s1) as H2. rewrite <- Heq_anonymous in H2. lia.
Defined.
Next Obligation.
Admitted.

Lemma predicate1P_unfold (s0 : string) :
  predicate1P s0 =
  match
    match P.symbolP "or"%string s0 with
    | None => None
    | Some (_, s1) =>
      match
        match parsetermP s1 with
        | None => None
        | Some (term, s2) =>
          match predicate1P s2 with
          | None => None
          | Some (f, s3) => Some (f (termPred term), s3)
          end
        end
      with
      | None => None
      | Some (pred2, s2) =>
        match predicate1P s2 with
        | None => None
        | Some (f, s3) => Some ((fun pred1 => f (orPred pred1 pred2)), s3)
        end
      end
    end
  with
  | None => Some ((fun x => x), s0)
  | Some res => Some res
  end.
Proof.
Admitted.

Definition predicateP : P.parser pred :=
  parsetermP >>= fun term => predicate1P >>= fun f => pure (f (termPred term)).

Theorem predicateP_defn
  : predicateP == (parsetermP >>= fun term => predicate1P >>= fun f => pure (f (termPred term))).
Proof. reflexivity. Qed.

Theorem predicate1P_defn
  : predicate1P == (P.symbolP "or" >>= fun _ => predicateP >>= fun pred2 => predicate1P >>= fun f => pure (fun pred1 => f (orPred pred1 pred2))) <|> pure (fun x => x).
Proof with reflexivity || trivial.
  transitivity ((P.symbolP "or" >>= (fun _ => (parsetermP >>= fun term => predicate1P >>= fun f => pure (f (termPred term))) >>= (fun pred2 => predicate1P >>= (fun f => pure (fun pred1 => f (orPred pred1 pred2)))))) <|> pure (fun x => x))...
  intros s0. rewrite predicate1P_unfold at 1. simpl...
Qed.

Definition optWhereP : P.parser (option pred) :=
  (P.symbolP "where" >>= fun _ => predicateP >>= fun pred => pure (Some pred)) <|> pure None.

Definition tableP : P.parser string := P.identifierP.

#[program]
Definition columns1P : P.parser (list string) :=
  P.identifierP >>= fun col => P.manyP (P.symbolP "," >>= fun _ => P.identifierP) _ >>= fun cols => pure (col :: cols).
Next Obligation.
  change (P.isLt (P.symbolP "," >>= fun _ => P.identifierP)).
  eapply P.bind_m_k_isLt_if_m_isLt_and_k_isLe.
  - eapply P.symbolP_isLt. simpl; eauto.
  - intros _. eapply P.isLt_implies_isLe. eapply P.identifierP_isLt. 
Defined.

Definition columnsP : P.parser cols :=
  columns1P >>= fun cols => pure (colNames cols).

Definition parseSQL : P.parser sql :=
  P.symbolP "select" >>= fun _ => (P.symbolP "*" >>= fun _ => pure star) <|> columnsP >>= fun cols => P.symbolP "from" >>= fun _ => tableP >>= fun tbl => optWhereP >>= fun maybePred => pure (sqlSFW cols tbl maybePred).

End PARSER.

End Hs.

Module Main.

Import ListNotations.

Definition must_return_true (sql : Hs.sql) (x : string) (v : string) : bool :=
  match Hs.parseSQL ∘ Hs.printSQL ∘ Hs.injection x v $ sql with
  | Some (sql', EmptyString) => Hs.injFree (Hs.norm sql) (Hs.norm sql')
  | _ => false
  end.

Section SQL_EXAMPLES.

Definition sql01 : Hs.sql :=
  Hs.sqlSFW Hs.star "t"%string None.

Example sql01_example1
  (sql := sql01)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql02 : Hs.sql :=
  Hs.sqlSFW (Hs.colNames ["c1"%string]) "t"%string None.

Example sql02_example1
  (sql := sql02)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql03 : Hs.sql :=
  Hs.sqlSFW (Hs.colNames ["c1"%string; "c2"%string; "c3"%string]) "t"%string None.

Example sql03_example1
  (sql := sql03)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql04 : Hs.sql :=
  Hs.sqlSFW Hs.star "t" (Some (Hs.termPred (Hs.equalTerm (Hs.ColName "id") (Hs.IntVal (123)%Z)))).

Example sql04_example1
  (sql := sql04)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql05 : Hs.sql :=
  Hs.sqlSFW Hs.star "t" (Some (Hs.termPred (Hs.equalTerm (Hs.ColName "id") (Hs.Var "z")))).

Example sql05_example1
  (sql := sql05)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql06 : Hs.sql :=
  Hs.sqlSFW Hs.star "t" (Some (Hs.termPred (Hs.equalTerm (Hs.ColName "id") (Hs.StrVal "Hong")))).

Example sql06_example1
  (sql := sql06)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql07 : Hs.sql :=
  Hs.sqlSFW Hs.star "t" (Some (Hs.termPred (Hs.equalTerm (Hs.ColName "name"%string) (Hs.Var "z"%string)))).

Example sql07_example1
  (sql := sql07)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql08 : Hs.sql :=
  Hs.sqlSFW (Hs.colNames ["c1"%string]) "t" None.

Example sql08_example1
  (sql := sql08)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql09 : Hs.sql :=
  Hs.sqlSFW (Hs.colNames ["c1"%string; "c2"%string; "c3"%string]) "t" None.

Example sql09_example1
  (sql := sql09)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

Definition sql10 : Hs.sql :=
  Hs.sqlSFW Hs.star "t" (Some (Hs.orPred (Hs.termPred (Hs.equalTerm (Hs.ColName "name") (Hs.StrVal "'abc'"))) (Hs.termPred (Hs.equalTerm (Hs.IntVal 1) (Hs.IntVal 1))))).

Example sql10_example1
  (sql := sql10)
  (x := "z"%string)
  (v := "' or 1=1"%string)
  : must_return_true sql x v
  = true.
Proof. reflexivity. Qed.

End SQL_EXAMPLES.

Lemma String_values
  : forall str, forall rest, Hs.sqlstringP (Hs.ppString str ++ rest)%string = Some (str, rest).
Proof.
Admitted.

Theorem main_thm (s : Hs.sql) (x : string) (v : string)
  : must_return_true s x v
  = true.
Proof.
Admitted.

End Main.
