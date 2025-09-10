Require Import common.
Require Import loo_def.
Require Import decoupling.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import function_operations.
Require Import exp.
Require Import decoupled_classical_properties.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Ltac unfold_exp_sat :=
  match goal with
  | [H : exp_satisfaction _ _ _ _ |- _] =>
    inversion H;
    subst;
    clear H;
    repeat link_unique_auto;
    repeat is_exp_auto;
    repeat eval_rewrite
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
  repeat unfold_exp_sat.
  repeat match goal with
         | [H : _ ∙ _ ⊢  (_ ⩵ _) ↪ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  repeat eval_rewrite.
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
  repeat unfold_exp_sat.
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

Lemma exp_satisfaction_refl :
  forall M1 M2 M σ v, M1 ⋄ M2 ≜ M ->
                 exp_satisfaction M1 M2 σ (ex_eq (ex_val v) (ex_val v)).
Proof.
  intros.
  eapply exp_sat with (e':=e_val v ⩵ e_val v);
    eauto with chainmail_db.
  apply value_reflexivity_eval.
Qed.

Lemma value_reflexivity :
  forall M1 M2 M σ0 σ v, M1 ⋄ M2 ≜ M ->
                    M1 ⦂ M2 ◎ σ0 … σ ⊨ (ex_val v ⩶ ex_val v).
Proof.
  intros.
  apply sat_exp.
  eapply exp_satisfaction_refl;
    eauto.
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
  repeat unfold_exp_sat.
  match goal with
  | [H : _ ∙ _ ⊢ neg _ ↪ _  |- _] =>
    inversion H;
      subst;
      clear H
  end.
  repeat eval_rewrite.
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
