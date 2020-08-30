Require Import common.
Require Import loo_def.
Require Import decoupling.
Require Import decoupled_classical_properties.
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
  | [H : is_exp _ _ |- _] =>
    inversion H;
      subst
  end.
  eapply sat_exp with (e':=e2' ⩵ e1');
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

Lemma transitive_equality :
  forall M1 M2 σ0 σ e1 e2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e2) ->
                      forall e3, M1 ⦂ M2 ◎ σ0 … σ ⊨ (e2 ⩶ e3) ->
                            M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e3).
Proof.
  intros.
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ … _ ⊨ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  is_exp_auto.
  repeat match goal with
         | [H : _ ∙ _ ⊢  (_ ⩵ _) ↪ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  link_unique_auto.
  eval_rewrite.
  eapply sat_exp;
    eauto with chainmail_db loo_db.
Qed.

Lemma value_equality_eval :
  forall M σ v1 v2, M ∙ σ ⊢ (e_val v1 ⩵ e_val v2) ↪ v_true ->
               v1 = v2.
Proof.
  intros.
  repeat match goal with
         | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
           inversion H;
             subst;
             clear H
         end;
    auto.
Qed.

Lemma value_equality :
  forall M1 M2 σ0 σ v1 v2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (ex_val v1 ⩶ ex_val v2) ->
                      v1 = v2.
Proof.
  intros M1 M2 σ0 σ v1 v2 Hsat;
    inversion Hsat;
    subst.
  is_exp_auto.
  match goal with
  | [ H : _ ∙ _ ⊢ (e_val _ ⩵ e_val _) ↪ v_true |- _ ] =>
    apply value_equality_eval in H
  end.
  auto.
Qed.

Lemma value_reflexivity_eval :
  forall M σ v, M ∙ σ ⊢ (e_val v ⩵ e_val v) ↪ v_true.
Proof.
  intros.
  apply v_equals with (v:=v);
    eauto with loo_db.
Qed.

Lemma value_reflexivity :
  forall M1 M2 M σ0 σ v, M1 ⋄ M2 ≜ M ->
                    M1 ⦂ M2 ◎ σ0 … σ ⊨ (ex_val v ⩶ ex_val v).
Proof.
  intros.
  eapply sat_exp with (e':=(e_val v ⩵ e_val v));
    eauto with chainmail_db.
  apply value_reflexivity_eval.
Qed.

Lemma neq_is_nsat_eq_1 :
  forall M1 M2 σ0 σ e1 e2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶̸ e2) ->
                      M1 ⦂ M2 ◎ σ0 … σ ⊭ (e1 ⩶ e2).
Proof.
  intros M1 M2 σ0 σ e1 e2 Hneq.
  apply not_sat_implies_nsat;
    intro Hcontra.
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ … _ ⊨ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  is_exp_auto.
  link_unique_auto.
  match goal with
  | [H : _ ∙ _ ⊢ neg _ ↪ _  |- _] =>
    inversion H;
      subst;
      clear H
  end.
  eval_rewrite.
  match goal with
  | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
    inversion H
  end.
Qed.

Ltac exp_sym_auto :=
  match goal with
  | [H : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (?e1 ⩶ ?e2) |- _] =>
    notHyp (M1 ⦂ M2 ◎ σ0 … σ ⊨ (e2 ⩶ e1));
    assert (M1 ⦂ M2 ◎ σ0 … σ ⊨ (e2 ⩶ e1));
    [apply symmetric_equality; auto|]
  end.

Ltac exp_trans_auto :=
  match goal with
  | [H1 : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (?e1 ⩶ ?e2),
          H2 : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (?e2 ⩶ ?e3) |- _] =>
    notHyp (M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e3));
    assert (M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e3));
    [apply transitive_equality with (e2:=e2); auto|]
  end.

Ltac clean :=
  repeat match goal with
         | [H1 : ?P,
                 H2 : ?P|- _] =>
           clear H2
         end.

Ltac exp_auto :=
  repeat link_unique_auto;
  repeat eval_rewrite;
  repeat is_exp_auto;
  repeat exp_sym_auto;
  repeat exp_trans_auto;
  repeat match goal with
         | [H : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (ex_val ?v1 ⩶ ex_val ?v2) |- _] =>
           assert (v1 = v2);
           [eapply value_equality; eauto|subst; clear H]
         end;
  try match goal with
      | [Hlink : _ ⋄ _ ≜ ?M |- ?M ∙ _ ⊢ (e_val ?v ⩵ e_val ?v) ↪ v_true ] =>
        eapply value_reflexivity;
        eauto
      | [Hlink : _ ⋄ _ ≜ ?M |- ?M ∙ _ ⊢ (e_val ?v ⩵ e_val ?v) ↪ v_true ] =>
        eapply value_reflexivity_eval;
        eauto
      end.
