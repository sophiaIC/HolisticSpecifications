Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Import chainmail.exp.
Require Import defs.
Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Ltac unfold_eval :=
  match goal with
  | [H : _ ∙ _ ⊢ (e_val _) ↪ _ |- _] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_acc_f _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_acc_g _ _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_if _ _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (_ ⩵ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (_ ⩻ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_plus _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_minus _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_mult _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : _ ∙ _ ⊢ (e_div _ _) ↪ _ |- _ ] =>
    inversion H;
    subst;
    clear H
  end.

Theorem eval_unique :
  forall M σ e v1, M ∙ σ ⊢ e ↪ v1 ->
              forall v2, M ∙ σ ⊢ e ↪ v2 ->
                    v2 = v1.
Proof.
  intros M σ e v1 Heval;
    induction Heval;
    intros;
    try solve [repeat unfold_eval;
               repeat (match goal with
                       | [IH : forall (_ : value), _ ∙ _ ⊢ ?e ↪ _ -> _ = ?v1,
                            H1 : _ ∙ _ ⊢ ?e ↪ ?v1,
                            H2 : _ ∙ _ ⊢ ?e ↪ ?v2 |- _] =>
                         specialize (IH v2);
                         repeat auto_specialize;
                         repeat simpl_crush
                       end);
               crush].
Qed.

Hint Rewrite eval_unique : exp_db.

Ltac eval_rewrite :=
  repeat match goal with
         | [H1 : ?M ∙ ?σ ⊢ ?e ↪ ?v1, H2 : ?M ∙ ?σ ⊢ ?e ↪ ?v2 |- _] =>
           eapply (eval_unique M σ e v1 H1) in H2;
           eauto;
           subst
         end.
