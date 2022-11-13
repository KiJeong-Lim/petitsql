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

Module Prelude.

  Import ListNotations.

  #[universes(polymorphic=yes)]
  Definition REFERENCE_HOLDER@{lv} {STATEMENT_Type : Type@{lv}} (REFERENCED_STATEMENT : unit -> STATEMENT_Type) : STATEMENT_Type := REFERENCED_STATEMENT tt.

  #[global]
  Notation " '<<' STATEMENT_REFERENCE ':' STATEMENT '>>' " := (REFERENCE_HOLDER (fun STATEMENT_REFERENCE : unit => match STATEMENT_REFERENCE with tt => STATEMENT end)) (STATEMENT_REFERENCE name, STATEMENT at level 200, at level 70, no associativity) : type_scope.

  Ltac unnw := unfold REFERENCE_HOLDER in *.

  Definition dollar {A : Set} {B : Set} (f : A -> B) (x : A) : B := f x.

  #[global]
  Infix " $ " := dollar (right associativity, at level 100).

  Class isSetoid (A : Type) : Type :=
    { eqProp (lhs : A) (rhs : A) : Prop
    ; eqProp_Equivalence :> Equivalence eqProp
    }.

  #[global]
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

  Lemma option_ext_eq {A : Type} (lhs : option A) (rhs : option A)
    : lhs = rhs <-> << EXT_EQ : liftRel_option eq lhs rhs >>.
  Proof. unnw. unfold liftRel_option. destruct lhs as [x | ], rhs as [y | ]; split; try (congruence || tauto). Qed.

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

  Class isMonad (M : Type -> Type) : Type :=
    { pure {A : Type} : A -> M A
    ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
    }.

  #[global]
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

  #[global]
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

  Fixpoint sequenceM {M : Type -> Type} {M_isMonad : isMonad M} {A : Type} (ms : list (M A)) {struct ms} : M (list A) :=
    match ms with
    | [] => pure []
    | m :: ms' => m >>= fun x => sequenceM ms' >>= fun xs => pure (x :: xs)
    end.

  Fixpoint sequenceM_ {M : Type -> Type} {M_isMonad : isMonad M} {A : Type} (ms : list (M A)) {struct ms} : M unit :=
    match ms with
    | [] => pure tt
    | m :: ms' => m >>= fun _ => sequenceM_ ms'
    end.

  Fixpoint lookup {A : Type} {B : Type} (x : A) (eq_dec : forall y : A, {x = y} + {x <> y}) (zs : list (A * B)) : option B :=
    match zs with
    | [] => None
    | (x', y) :: zs' =>
      if eq_dec x'
      then Some y
      else lookup x eq_dec zs'
    end.

  Definition eq_dec_to_bool {A : Type} (eq_dec : forall lhs : A, forall rhs : A, {lhs = rhs} + {lhs <> rhs}) : A -> A -> bool :=
    fun lhs : A => fun rhs : A => if eq_dec lhs rhs then true else false.

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

  Fixpoint mk_string (xs : list ascii) : string :=
    match xs with
    | [] => EmptyString
    | ch :: xs' => String ch (mk_string xs')
    end.

  Section STRING_OPERATIONS.

  Fixpoint mapFromString {A : Type} (f : ascii -> A) (s : string) {struct s} : list A :=
    match s with
    | EmptyString => []
    | String ch s' => f ch :: mapFromString f s'
    end.

  Fixpoint String_take (n : nat) (s : string) {struct n} : string :=
    match n with
    | O => EmptyString
    | S n' =>
      match s with
      | EmptyString => EmptyString
      | String ch s' => String ch (String_take n' s')
      end
    end.

  Fixpoint String_concat (ss : list string) {struct ss} : string :=
    match ss with
    | [] => ""%string
    | s :: ss' => (s ++ String_concat ss')%string
    end.

  Fixpoint String_drop (n : nat) (s : string) {struct n} : string :=
    match n with
    | O => s
    | S n' =>
      match s with
      | EmptyString => EmptyString
      | String ch s' => String_drop n' s'
      end
    end.

  Fixpoint String_rev (s : string) {struct s} : string :=
    match s with
    | EmptyString => EmptyString
    | String ch s' => (String_rev s' ++ String ch EmptyString)%string
    end.

  Lemma String_app_assoc (s1 : string) (s2 : string) (s3 : string)
    : ((s1 ++ s2) ++ s3)%string = (s1 ++ (s2 ++ s3))%string.
  Proof.
    revert s2 s3. induction s1 as [ | ch1 s1 IH]; simpl; intros.
    - reflexivity.
    - eapply f_equal. eauto.
  Qed.

  Lemma String_app_nil_l (s1 : string)
    : (s1 ++ "")%string = s1.
  Proof. induction s1 as [ | ch1 s1 IH]; simpl; congruence. Qed.

  Lemma String_app_nil_r (s1 : string)
    : ("" ++ s1)%string = s1.
  Proof. reflexivity. Qed.

  Lemma String_app_length (s1 : string) (s2 : string)
    : length (s1 ++ s2)%string = length s1 + length s2.
  Proof. induction s1 as [ | ch1 s1]; simpl; lia. Qed.

  Lemma String_take_app_String_drop (n : nat) (s : string)
    (n_lt_length_s : n < length s)
    : (String_take n s ++ String_drop n s)%string = s.
  Proof.
    revert s n_lt_length_s. induction n as [ | n IH].
    - intros s _. reflexivity.
    - intros s n_lt_length_s. destruct s as [ | ch s'].
      + reflexivity.
      + simpl. eapply f_equal. eapply IH. simpl in n_lt_length_s. lia.
  Qed.

  Lemma String_rev_app (s1 : string) (s2 : string)
    : String_rev (s1 ++ s2)%string = (String_rev s2 ++ String_rev s1)%string.
  Proof.
    induction s1 as [ | ch1 s1 IH]; simpl.
    - rewrite String_app_nil_l. reflexivity.
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
    (H_EmptyString : phi EmptyString)
    (H_String : forall ch : ascii, forall s : string, phi s -> phi (s ++ String ch EmptyString)%string)
    : forall s : string, phi s.
  Proof.
    intros s. rewrite <- String_rev_involute with (s := s).
    generalize (String_rev s). clear s. induction s as [ | ch s IH]; simpl.
    - eapply H_EmptyString.
    - eapply H_String. exact (IH).
  Qed.

  Lemma String_rev_dual (phi : string -> Prop)
    (H_rev : forall s : string, phi (String_rev s))
    : forall s : string, phi s.
  Proof.
    induction s as [ | ch s _] using String_rev_ind.
    - eapply H_rev with (s := ""%string).
    - rewrite <- String_rev_involute with (s := s).
      eapply H_rev with (s := String ch (String_rev s)).
  Qed.

  Lemma String_rev_inj (s1 : string) (s2 : string)
    (REV_EQ : String_rev s1 = String_rev s2)
    : s1 = s2.
  Proof.
    revert s2 REV_EQ. pattern s1. revert s1. eapply String_rev_dual.
    intros s1 s2. pattern s2. revert s2. eapply String_rev_dual.
    intros s2. do 2 rewrite String_rev_involute. congruence.
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

  End STRING_OPERATIONS.

End Prelude.

Export Prelude.

Module P.

  Import ListNotations.

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
    { eqProp := eqP
    ; eqProp_Equivalence := eqP_Equivalence
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

  Lemma alt_assoc {A : Type} (m1 : parser A) (m2 : parser A) (m3 : parser A)
    : (m1 <|> m2) <|> m3 == m1 <|> (m2 <|> m3).
  Proof. intros s. simpl. destruct (m1 s) as [[x1 s'] | ]; reflexivity. Qed.

  Lemma alt_empty_l {A : Type} (m : parser A)
    : empty <|> m == m.
  Proof. intros s. simpl. reflexivity. Qed.

  Lemma alt_empty_r {A : Type} (m : parser A)
    : m <|> empty == m.
  Proof. intros s. simpl. destruct (m s) as [[x s'] | ]; reflexivity. Qed.

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

  Section PARSER_COMBINATORS.

  Definition satisfyP (cond : ascii -> bool) : parser ascii :=
    fun s : string =>
    match s with
    | EmptyString => None
    | String ch s' => if cond ch then Some (ch, s') else None
    end.

  Lemma satisfyP_isLt (cond : ascii -> bool)
    : isLt (satisfyP cond).
  Proof.
    intros s. unfold satisfyP. destruct s as [ | ch s']; trivial.
    destruct (cond ch); trivial. simpl. red. reflexivity.
  Qed.

  Definition stringP : string -> parser unit := sequenceM_ ∘ mapFromString (satisfyP ∘ Ascii.eqb).

  Lemma stringP_isLt (str : string)
    (length_str_gt_0 : length str > 0)
    : isLt (stringP str).
  Proof.
    enough (to_show : length str = 0 \/ isLt (stringP str)).
    { destruct to_show; [lia | assumption]. }
    clear length_str_gt_0. induction str as [ | ch str IH_str].
    - left. reflexivity.
    - simpl. right. intros s.
      assert (H_Acc : Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s) by exact (Prelude.acc_rel String.length lt Prelude.acc_lt s).
      revert ch str IH_str. induction H_Acc as [s _ IH]. intros. simpl.
      red. red. simpl. red. pose proof (satisfyP_isLt (Ascii.eqb ch) s) as length_s_gt_length_s'.
      destruct (satisfyP (Ascii.eqb ch) s) as [[x s'] | ] eqn: H_OBS; trivial.
      simpl. specialize (IH s' length_s_gt_length_s'). destruct str as [ | ch' str'].
      + assert (IH_claim : length "" = 0 \/ isLt (stringP "")) by now left.
        specialize (IH ch EmptyString IH_claim). do 2 red in IH. simpl in IH. red in IH. simpl. assumption.
      + assert (IH_claim : length (String ch' str') = 0 \/ isLt (stringP (String ch' str'))).
        { right. destruct IH_str as [IH_str | IH_str]; [inversion IH_str | assumption]. }
        specialize (IH ch (String ch' str') IH_claim). do 2 red in IH. simpl in IH. red in IH.
        destruct IH_str as [IH_str | IH_str].
        * inversion IH_str.
        * specialize (IH_str s'). red in IH_str. red in IH_str.
          destruct (sequenceM_ (mapFromString (satisfyP ∘ Ascii.eqb) (String ch' str')) s') as [[x' s''] | ] eqn: H_OBS'; trivial. lia.
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
  Next Obligation. pose proof (p_isLt s) as H. rewrite <- Heq_anonymous in H. assumption. Defined.

  Example someP_example1
    : (someP (satisfyP (fun ch : ascii => true)) (satisfyP_isLt _) "abc"%string)
    = Some (["a"%char; "b"%char; "c"%char], ""%string).
  Proof. reflexivity. Qed.

  Example someP_example2
    : (someP (satisfyP (fun ch : ascii => Ascii.eqb ch "a"%char)) (satisfyP_isLt _) "abc"%string)
    = Some (["a"%char], "bc"%string).
  Proof. reflexivity. Qed.

  Example someP_example3
    : (someP (satisfyP (fun ch : ascii => Ascii.eqb ch "b"%char)) (satisfyP_isLt _) "abc"%string)
    = None.
  Proof. reflexivity. Qed.

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
    intros s.
    assert (H_Acc : Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s) by exact (Prelude.acc_rel String.length lt Prelude.acc_lt s).
    induction H_Acc as [s _ IH]. rewrite someP_unfold. pose proof (p_isLt s) as length_s_gt_length_s'. destruct (p s) as [[x s'] | ]; trivial. specialize (IH s' length_s_gt_length_s').
    destruct (someP p p_isLt s') as [[xs s''] | ]; lia.
  Qed.

  Definition manyP {A : Type} (p : parser A) (p_isLt : isLt p) : parser (list A) := someP p p_isLt <|> pure [].

  Theorem someP_spec {A : Type} (p : parser A) (p_isLt : isLt p)
    : someP p p_isLt == (p >>= fun x => manyP p p_isLt >>= fun xs => pure (x :: xs)).
  Proof. intros s. rewrite someP_unfold at 1. unfold manyP. simpl. destruct (p s) as [[x s'] | ]; try reflexivity. simpl. destruct (someP p p_isLt s') as [[xs s''] | ]; try reflexivity. Qed.

  Theorem manyP_spec {A : Type} (p : parser A) (p_isLt : isLt p)
    : manyP p p_isLt == someP p p_isLt <|> pure [].
  Proof. reflexivity. Qed.

  Lemma someP_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
    (p1_eq_p2 : p1 == p2)
    : someP p1 p1_isLt == someP p2 p2_isLt.
  Proof.
    intros s.
    assert (H_Acc : Acc (fun s1 : string => fun s2 : string => length s1 < length s2) s) by exact (Prelude.acc_rel String.length lt Prelude.acc_lt s).
    induction H_Acc as [s _ IH]. do 2 rewrite someP_unfold.
    pose proof (p1_eq_p2 s) as p1_s_eq_p2_s. rewrite p1_s_eq_p2_s. destruct (p2 s) as [[x s'] | ]; trivial.
    rewrite IH; trivial. pose proof (p1_isLt s) as length_s_gt_length_s'. rewrite p1_s_eq_p2_s in length_s_gt_length_s'. assumption.
  Qed.

  Lemma manyP_lifts_eqP {A : Type} (p1 : parser A) (p1_isLt : isLt p1) (p2 : parser A) (p2_isLt : isLt p2)
    (p1_eq_p2 : p1 == p2)
    : manyP p1 p1_isLt == manyP p2 p2_isLt.
  Proof. now unfold manyP; rewrite someP_lifts_eqP with (p1_isLt := p1_isLt) (p2_isLt := p2_isLt) (p1_eq_p2 := p1_eq_p2). Qed.

  Definition spaceP : parser unit :=
    (manyP (satisfyP (fun ch : ascii => Ascii.eqb ch " "%char)) (satisfyP_isLt _)) >>= fun _ => pure (isMonad := parserT_isMonad option_isMonad) tt.

  Definition tokenP {A : Type} (p : parser A) : parser A :=
    spaceP >>= fun _ => p >>= fun v => spaceP >>= fun _ => pure v.

  Definition symbolP (s : string) : parser unit :=
    tokenP (stringP s).

  Let isNum (ch : ascii) : bool := Ascii.leb "0"%char ch && Ascii.leb ch "9"%char.

  Definition digitP : parser ascii := satisfyP isNum.

  Let isLower (ch : ascii) : bool := Ascii.leb "a"%char ch && Ascii.leb ch "z"%char.

  Definition lowerP : parser ascii := satisfyP isLower.

  Let isUpper (ch : ascii) : bool := Ascii.leb "A"%char ch && Ascii.leb ch "Z"%char.

  Definition upperP : parser ascii := satisfyP isUpper.

  Let isAlpha (ch : ascii) : bool := isLower ch || isUpper ch.

  Definition letterP : parser ascii := satisfyP isAlpha.

  Let isAlphaNum (ch : ascii) : bool := isAlpha ch || isNum ch.

  Definition alphanumP : parser ascii := satisfyP isAlphaNum.

  Definition charP (ch : ascii) : parser unit := satisfyP (Ascii.eqb ch) >>= fun _ => pure tt.

  Definition optMinusP : parser bool :=
    (symbolP "-" >>= fun _ => pure true) <|> pure false.

  Definition naturalP : parser nat :=
    (someP digitP (satisfyP_isLt (fun ch : ascii => ("0" <=? ch)%char && (ch <=? "9")%char))) >>= (fun s => pure (BinaryString.to_nat (mk_string s))).

  Definition integerP : parser Z :=
    optMinusP >>= fun b =>
    naturalP >>= fun n =>
    if b then pure ((-1) * Z.of_nat n)%Z else pure (Z.of_nat n).

  Definition identP : parser string :=
    lowerP >>= fun x => manyP alphanumP (satisfyP_isLt _) >>= fun xs => pure (String x (mk_string xs)).

  Definition identifierP : parser string := tokenP identP.

  End PARSER_COMBINATORS.

End P.

Module Hs.

  Import ListNotations.

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

  Definition normMaybePred (maybePred : option pred) : option pred :=
    match maybePred with
    | None => None
    | Some pred => Some (normPred pred)
    end.

  Definition norm (s : sql) : sql :=
    match s with
    | sqlSFW cols tbl maybePred => sqlSFW cols tbl (normMaybePred maybePred)
    end.

  Definition env : Set := list (string * value).

  Definition applyValue (e : env) (v : value) : value :=
    match v with
    | ColName cn => ColName cn
    | StrVal s => StrVal s
    | IntVal i => IntVal i
    | Var x =>
      match lookup x (string_dec x) e with
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

  Definition applySQL (e : env) (s : sql) : sql :=
    match s with
    | sqlSFW cols tbl maybePred => sqlSFW cols tbl (applyMaybePred e maybePred)
    end.

  Definition injection (v : string) (s : string) : sql -> sql := applySQL [(v, StrVal s)].

  Section INJECTION_FREE.

  Lemma cols_eq_dec
    : forall lhs : cols, forall rhs : cols, {lhs = rhs} + {lhs <> rhs}.
    Proof with try ((left; congruence) || (right; congruence)).
    intros [ | x] [ | y]...
    pose proof (list_eq_dec string_dec x y) as [H_EQ | H_NE]...
  Defined.

  Lemma value_eq_dec
    : forall lhs : value, forall rhs : value, {lhs = rhs} + {lhs <> rhs}.
  Proof with try ((left; congruence) || (right; congruence)).
    induction lhs as [cn1 | s1 | i1 | v1], rhs as [cn2 | s2 | i2 | v2]...
    - pose proof (string_dec cn1 cn2) as [H_EQ | H_NE]...
    - pose proof (string_dec s1 s2) as [H_EQ | H_NE]...
    - pose proof (Z.eq_dec i1 i2) as [H_EQ | H_NE]...
    - pose proof (string_dec v1 v2) as [H_EQ | H_NE]...
  Defined.

  Lemma term_eq_dec
    : forall lhs : term, forall rhs : term, {lhs = rhs} + {lhs <> rhs}.
  Proof with try ((left; congruence) || (right; congruence)).
    intros [v1_1 v2_1] [v1_2 v2_2].
    pose proof (value_eq_dec v1_1 v1_2) as [H_EQ1 | H_NE1]; pose proof (value_eq_dec v2_1 v2_2) as [H_EQ2 | H_NE2]...
  Defined.

  Lemma pred_eq_dec
    : forall lhs : pred, forall rhs : pred, {lhs = rhs} + {lhs <> rhs}.
  Proof with try ((left; congruence) || (right; congruence)).
    induction lhs as [p1_1 IH1 p2_1 IH2 | t_1], rhs as [p1_2 p2_2 | t_2]...
    - pose proof (IH1 p1_2) as [H_EQ1 | H_NE1]; pose proof (IH2 p2_2) as [H_EQ2 | H_NE2]...
    - pose proof (term_eq_dec t_1 t_2) as [H_EQ | H_NE]... 
  Defined.

  Lemma sql_eq_dec
    : forall lhs : sql, forall rhs : sql, {lhs = rhs} + {lhs <> rhs}.
    Proof with try ((left; congruence) || (right; congruence)).
    intros [x1 x2 [x3 | ]] [y1 y2 [y3 | ]]...
    - pose proof (cols_eq_dec x1 y1) as [H_EQ1 | H_NE1]...
      pose proof (string_dec x2 y2) as [H_EQ2 | H_NE2]...
      pose proof (pred_eq_dec x3 y3) as [H_EQ3 | H_NE3]...
    - pose proof (cols_eq_dec x1 y1) as [H_EQ1 | H_NE1]...
      pose proof (string_dec x2 y2) as [H_EQ2 | H_NE2]...
  Defined.

  Definition injFreeValue (lhs : value) (rhs : value) : bool :=
    match lhs, rhs with
    | ColName c1, ColName c2 => eq_dec_to_bool string_dec c1 c2
    | StrVal s1, StrVal s2 => eq_dec_to_bool string_dec s1 s2
    | IntVal i1, IntVal i2 => eq_dec_to_bool Z.eq_dec i1 i2
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
    | sqlSFW cols1 tbl1 maybePred1, sqlSFW cols2 tbl2 maybePred2 => eq_dec_to_bool cols_eq_dec cols1 cols2 && eq_dec_to_bool string_dec tbl1 tbl2 && injFreeMaybePred maybePred1 maybePred2
    end.

  End INJECTION_FREE.

  Section PRINTER.

  Fixpoint ppString1 (s : string) : string :=
    match s with
    | EmptyString => ""%string
    | String "'"%char s' => ("''" ++ ppString1 s')%string
    | String ch s' => String ch (ppString1 s')
    end.

  Definition ppString (s : string) : string :=
    String_concat ["'"%string; ppString1 s; "'"%string]%list
  .

  Definition ppValue (v : value) : string :=
    match v with
    | ColName s => s
    | StrVal s => ppString s
    | IntVal i => of_Z i
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

  Definition ppCols (c : cols) : string :=
    let go : list string -> string :=
      fix go_fix (ss : list string) {struct ss} : string :=
      match ss with
      | [] => ""%string
      | [c1] => c1
      | c1 :: cs => String_concat [c1; ","%string; go_fix cs]
      end
    in
    match c with
    | star => "*"%string
    | colNames cs => go cs
    end.

  Definition printSQL (s : sql) : string :=
    match s with
    | sqlSFW cols tbl maybePred => String_concat ["select "%string; ppCols cols; " from "%string; ppTbl tbl; ppWhere maybePred]
    end.

  End PRINTER.

  Section PARSER.

  Definition hacking {A : Type} (p_n : nat -> P.parser A) : P.parser A :=
    fun s : string => p_n (length s) s.

  Fixpoint sqlstringin' (n : nat) {struct n} : P.parser string :=
    match n with
    | O => pure ""%string
    | S n' => (P.charP "'"%char >>= fun _ => P.charP "'"%char >>= fun _ => sqlstringin' n' >>= fun text => pure (String "'"%char text)) <|> (P.charP "'"%char >>= fun _ => pure ""%string) <|> (P.satisfyP (fun ch : ascii => true) >>= fun c : ascii => sqlstringin' n' >>= fun text => pure (String c text)) 
    end.

  Definition sqlstringin : P.parser string := hacking sqlstringin'.

  Definition sqlstring : P.parser string :=
    P.charP "'"%char >>= fun _ => sqlstringin >>= fun text => pure text.

  Definition parsevalue : P.parser value :=
    (P.identifierP >>= fun colName => pure (ColName colName)) <|> (sqlstring >>= fun sqlstr => pure (StrVal sqlstr)) <|> (P.integerP >>= fun i => pure (IntVal i)) <|> (P.symbolP "{" >>= fun _ => P.identifierP >>= fun v => P.symbolP "}" >>= fun _ => pure (Var v)).

  Definition parseterm : P.parser term :=
    parsevalue >>= fun v1 => P.symbolP "=" >>= fun _ => parsevalue >>= fun v2 => pure (equalTerm v1 v2).

  Fixpoint predicate1' (n : nat) : P.parser (pred -> pred) :=
    match n with
    | O => pure (fun x => x)
    | S n' => (P.symbolP "or" >>= fun _ => (parseterm >>= fun term => predicate1' n' >>= fun f => pure (f (termPred term))) >>= fun pred2 => predicate1' n' >>= fun f => pure (fun pred1 => f (orPred pred1 pred2))) <|> pure (fun x => x)
    end.

  Definition predicate1 : P.parser (pred -> pred) := hacking predicate1'.

  Definition predicate : P.parser pred :=
    parseterm >>= fun term => predicate1 >>= fun f => pure (f (termPred term)).

  Definition optWhere : P.parser (option pred) :=
    (P.symbolP "where" >>= fun _ => predicate >>= fun pred => pure (Some pred)) <|> pure None.

  Definition table : P.parser string := P.identifierP.

  Axiom sorry1 : P.isLt (P.symbolP "," >>= (fun _ : () => P.identifierP)).

  Definition columns1 : P.parser (list string) :=
    P.identifierP >>= fun col => P.manyP (P.symbolP "," >>= fun _ => P.identifierP) sorry1 >>= fun cols => pure (col :: cols).

  Definition columns : P.parser cols :=
    columns1 >>= fun cols => pure (colNames cols).

  Definition parseSQL : P.parser sql :=
    P.symbolP "select" >>= fun _ =>
    (P.symbolP "*" >>= fun _ => pure star) <|> columns >>= fun cols =>
    P.symbolP "from" >>= fun _ =>
    table >>= fun tbl =>
    optWhere >>= fun maybePred =>
    pure (sqlSFW cols tbl maybePred).

  End PARSER.

End Hs.

Module Main.

  Import ListNotations Hs.

  Definition defaultSQL : sql :=
    sqlSFW (colNames []) "" None.

  Definition sqlFrom (res : option (sql * string)) : sql :=
    match res with
    | Some (sql, ""%string) => sql
    | _ => defaultSQL
    end.

  Definition spec (sql : sql) (x : string) (v : string) : bool :=
    injFree (norm sql) ∘ norm ∘ sqlFrom ∘ parseSQL ∘ printSQL ∘ injection x v $ sql.

  Definition sql01 : sql := sqlSFW star "t" (Some (termPred (equalTerm (ColName "name"%string) (Var "z"%string)))).

  Example example01
    : (spec sql01 "a"%string "b"%string)
    = true.
  Proof. reflexivity. Qed.

End Main.
