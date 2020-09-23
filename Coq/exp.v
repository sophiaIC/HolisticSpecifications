Require Import common.
Require Import loo_def.
Require Import decoupling.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import function_operations.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma symmetric_equality :
  forall M1 M2 σ0 σ e1 e2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e2) ->
                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (e2 ⩶ e1).
Proof.
  intros.
  inversion H;
    subst.
  match goal with
  | [H : exp_satisfaction _ _ _ _ |- _ ] =>
    inversion H;
      subst;
      clear H
  end.
  match goal with
  | [H : is_exp _ _ |- _] =>
    inversion H;
      subst
  end;
    eauto with chainmail_db.
  apply sat_exp.
  eapply exp_sat with (e':=e2' ⩵ e1');
    eauto with chainmail_db.
  match goal with
  | [ H : _ ∙ _ ⊢ _ ⩵ _ ↪ _ |- _] =>
    inversion H;
      subst
  end.
  eauto with loo_db.
Qed.

Ltac is_exp_destruct :=
  match goal with
  | [H : is_exp (e_ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_val _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_eq _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_plus _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_minus _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_mult _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_div _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_lt _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_if _ _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_acc_f _ _) _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp (ex_acc_g _ _ _) _ |- _] =>
    inversion H;
    subst;
    clear H

  | [H : is_exp _ (e_var _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_val _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_plus _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_minus _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_mult _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_div _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_eq _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_lt _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_if _ _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_acc_f _ _) |- _] =>
    inversion H;
    subst;
    clear H
  | [H : is_exp _ (e_acc_g _ _ _) |- _] =>
    inversion H;
    subst;
    clear H

  end.

Lemma is_exp_unique1 :
  forall e e1, is_exp e e1 ->
          forall e2, is_exp e e2 ->
                e1 = e2.
Proof.
  intros e e1 Hexp;
    induction Hexp;
    intros;
    repeat is_exp_destruct;
    auto;
    try solve [erewrite IHHexp1, IHHexp2; eauto].

  - erewrite IHHexp1, IHHexp2, IHHexp3;
      eauto.

  - erewrite IHHexp;
      eauto.
Qed.

Lemma is_exp_unique2 :
  forall e1 e, is_exp e1 e ->
          forall e2, is_exp e2 e ->
                e1 = e2.
Proof.
  intros e e1 Hexp;
    induction Hexp;
    intros;
    repeat is_exp_destruct;
    auto;
    try solve [erewrite IHHexp1, IHHexp2; eauto].

  - erewrite IHHexp1, IHHexp2, IHHexp3;
      eauto.

  - erewrite IHHexp;
      eauto.
Qed.

Ltac is_exp_auto :=
  repeat is_exp_destruct;
  repeat match goal with
         | [H1 : is_exp ?e ?ea,
                 H2 : is_exp ?e ?eb |- _] =>
           apply is_exp_unique1 with (e1:=ea)(e2:=eb) in H2;
           auto;
           subst
         | [H1 : is_exp ?ea ?e,
                 H2 : is_exp ?eb ?e |- _] =>
           apply is_exp_unique2 with (e1:=ea)(e2:=eb) in H2;
           auto;
           subst
         end.
