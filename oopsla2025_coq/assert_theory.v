Require Export Arith.
Require Import List.
Require Import Bool.

Require Import common.
Require Import language_def.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module AssertTheory.

  Import LanguageDefinition.

  Parameter entails : module -> asrt -> asrt -> Prop.

  (* assertion satisfaction is assumed, and is disconnected from the semantics defined in the paper. later we make some assumptions to simplify   *)
  Parameter sat : module -> config -> asrt -> Prop.

  Notation "M ⊢ A1 ⊆ A2" := (entails M A1 A2)(at level 40).

  Parameter entails_sound :
    forall M A1 A2, entails M A1 A2 <-> (forall σ, sat M σ A1 -> sat M σ A2).



  Parameter nsat : module -> config -> asrt -> Prop.

  Parameter sat_neg : forall M σ A, nsat M σ A -> sat M σ (¬ A).

  Parameter nsat_neg : forall M σ A, sat M σ A -> nsat M σ (¬ A).

  Parameter nsat_and1 : forall M σ A1 A2, nsat M σ A1 -> nsat M σ (A1 ∧ A2).

  Parameter nsat_and2 : forall M σ A1 A2, nsat M σ A2 -> nsat M σ (A1 ∧ A2).

  Parameter sat_and : forall M σ A1 A2, sat M σ A1 -> sat M σ A2 -> sat M σ (A1 ∧ A2).

  Parameter sat_and_inv : forall M σ A1 A2, sat M σ (A1 ∧ A2) -> sat M σ A1 /\ sat M σ A2.

  Parameter nsat_and_inv : forall M σ A1 A2, sat M σ (A1 ∧ A2) -> sat M σ A1 \/ sat M σ A2.

  Ltac asrt_sat_unfold_neg :=
    match goal with
    | [ H : sat ?M ?σ (¬ ?A)  |- _ ] =>
        inversion H; subst; clear H
    | [ H : nsat ?M ?σ (¬ ?A)  |- _ ] =>
        inversion H; subst; clear H
    | [ |- nsat ?M ?σ (¬ ?A) ] =>
        apply nsat_neg
    | [ |- sat ?M ?σ (¬ ?A) ] =>
        apply sat_neg
    end.

  Ltac asrt_sat_auto_destruct_conj :=
    match goal with
    | [H : sat ?M ?σ (?A1 ∧ ?A2) |- _] =>
        apply sat_and_inv in H; destruct H; subst
    | [H : nsat ?M ?σ (?A1 ∧ ?A2) |- _] =>
        apply nsat_and_inv; destruct H; subst
    | [|- sat ?M ?σ (?A1 ∧ ?A2)] =>
        apply sat_and; auto
    | [H : nsat ?M ?σ ?A1 |- nsat ?M ?σ (?A1 ∧ ?A2)] =>
        apply nsat_and1; auto
    | [H : nsat ?M ?σ ?A2 |- nsat ?M ?σ (?A1 ∧ ?A2)] =>
        apply nsat_and2; auto
    end.

  Lemma destruct_entails :
    forall M A1 A2, (forall σ, sat M σ A1 -> sat M σ A2) ->
                    M ⊢ A1 ⊆ A2.
  Proof.
    apply entails_sound.
  Qed.

  Lemma entails_unfold :
    forall M A1 A2, M ⊢ A1 ⊆ A2 ->
               (forall σ, sat M σ A1 -> sat M σ A2).
  Proof.
    apply entails_sound.
  Qed.

  Ltac intros_entails :=
    intros;
    match goal with
    | [|- _ ⊢ _ ⊆ _ ] =>
        apply destruct_entails;
        intros
    | [H : ?M ⊢ ?A1 ⊆ ?A2 |- _] =>
        assert (forall σ, sat M σ A1 -> sat M σ A2);
        [apply (entails_unfold M A1 A2 H)|clear H]
    end.

  Lemma entails_refl :
    forall M A, M ⊢ A ⊆ A.
  Proof.
    intros_entails;
      auto.
  Qed.

  #[global] Hint Resolve entails_refl : assert_db.

  Parameter apply_entails :
    forall M σ A1 A2, M ⊢ A1 ⊆ A2 ->
                 sat M σ A1 ->
                 sat M σ A2.

   Parameter entails_fld_type :
    forall M C f T, typeOf_f M C f = Some T ->
               forall e, M ⊢ (a_ (e_typ e (t_cls C))) ⊆
                           (a_ (e_typ (e_fld e f) T)).

  Parameter sat_excluded_middle :
    forall M σ A, sat M σ (A ∨ ¬ A).

  Parameter sat_neg_is_not_sat :
    forall M σ A, sat M σ (¬ A) ->
             ~ sat M σ A.

  Parameter entails_excluded_middle :
    forall M A, M ⊢ a_true ⊆ (A ∨ ¬ A).

  Parameter or_and_dist1 :
    forall M A1 A2 A, M ⊢ (A1 ∨ A2) ∧ A ⊆ (A1 ∧ A) ∨ (A2 ∧ A).

  Parameter or_and_dist2 :
    forall M A1 A2 A, M ⊢ (A1 ∧ A) ∨ (A2 ∧ A) ⊆ (A1 ∨ A2) ∧ A.

  Parameter entails_assoc1 :
    forall M A1 A2 A3, M ⊢ ((A1 ∧ A2) ∧ A3) ⊆ (A1 ∧ (A2 ∧ A3)).

  Parameter entails_assoc2 :
    forall M A1 A2 A3, M ⊢ (A1 ∧ (A2 ∧ A3)) ⊆ ((A1 ∧ A2) ∧ A3).

  Parameter entails_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊆ A2 ->
                  M ⊢ A2 ⊆ A3 ->
                  M ⊢ A1 ⊆ A3.

  Ltac simpl_conj_entails :=
    repeat try (eapply entails_trans; [solve [apply entails_assoc1] |]);
    repeat try (eapply entails_trans; [|solve [apply entails_assoc2]]).

  Fixpoint contains {A : Type}`{Eq A}(l : list A)(a : A) :=
    match l with
    | nil => false
    | h :: t => eqb a h || contains t a
    end.

  Lemma conj_entails_left :
    forall M A1 A2, M ⊢ A1 ∧ A2 ⊆ A1.
  Proof.
    intros_entails.
      asrt_sat_auto_destruct_conj;
      auto.
  Qed.

  Lemma conj_entails_right :
    forall M A1 A2, M ⊢ A1 ∧ A2 ⊆ A2.
  Proof.
    intros_entails;
      asrt_sat_auto_destruct_conj;
      auto.
  Qed.

  Lemma entails_conj_split :
    forall M A A1 A2, M ⊢ A ⊆ A1 ->
                 M ⊢ A ⊆ A2 ->
                 M ⊢ A ⊆ A1 ∧ A2.
  Proof.
    repeat intros_entails.
    apply sat_and; eauto.
  Qed.

  Parameter sat_true :
    forall M σ, sat M σ (a_true).

  #[global] Hint Resolve sat_true : assert_db.

  Lemma entails_true :
    forall M A, M ⊢ A ⊆ a_true.
  Proof.
    repeat intros_entails.
    apply sat_true.
  Qed.

  Lemma conj_entails_dup :
    forall M A, M ⊢ A ⊆ (A ∧ A).
  Proof.
    intros; intros_entails;
      repeat asrt_sat_auto_destruct_conj.
  Qed.

End AssertTheory.
