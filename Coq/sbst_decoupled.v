Require Import common.
Require Import loo_def.
Require Import decoupling.

(*Instance raiseAsrt : Raiseable asrt :=
  {
    raise :=
      fix raise' A n :=
        match A with
        | a_expr e => a_expr (e ↑ n)
        | a_class e C => a_class (e ↑ n) C

        | A1 ⟶ A2 => (raise' A1 n) ⟶ (raise' A2 n)
        | A1 ∧ A2 => (raise' A1 n) ∧ (raise' A2 n)
        | A1 ∨ A2 => (raise' A1 n) ∨ (raise' A2 n)
        | ¬ A' => ¬ (raise' A' n)

        | ∀x∙ A' => ∀x∙ (raise' A' (S n))
        | ∃x∙ A' => ∃x∙ (raise' A' (S n))

        | ∀m∙ A' => ∀m∙ (raise' A' n)
        | ∃m∙ A' => ∃m∙ (raise' A' n)

        | x access y => (x ↑ n) access (y ↑ n)
        | x calls y ▸ m ⟨ vMap ⟩ => (x ↑ n) calls (y ↑ n) ▸ m ⟨ vMap ↑ n ⟩

        | a_next A' => a_next (raise' A' n)
        | a_will A' => a_will (raise' A' n)
        | a_prev A' => a_prev (raise' A' n)
        | a_was A' => a_was (raise' A' n)

        | e ∈ Σ => 

        | x external => (x ↑ n) external
        | x internal => (x ↑ n) internal
        end
  }.*)

Lemma sbst_x_neg :
  forall (x : a_var) n A, ([x /s n] ¬A) = (¬ ([x /s n]A)).
Proof.
  intros.
  destruct x;
    auto.
Qed.

Lemma sbst_x_arr :
  forall (x : a_var) n A1 A2, ([x /s n] (A1 ⟶ A2)) = (([x /s n]A1) ⟶ ([x /s n]A2)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_and :
  forall (x : a_var) n A1 A2, ([x /s n] (A1 ∧ A2)) = (([x /s n]A1) ∧ ([x /s n]A2)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_exp :
  forall (x : a_var) n e, ([x /s n] (a_expr e)) = (a_expr ([x /s n] e)).
Proof.
  auto.
Qed.

Lemma sbst_x_class :
  forall (x : a_var) n e C, ([x /s n] (a_class e C)) = (a_class ([x /s n] e) C).
Proof.
  auto.
Qed.

Lemma sbst_x_or :
  forall (x : a_var) n A1 A2, ([x /s n] (A1 ∨ A2)) = (([x /s n]A1) ∨ ([x /s n]A2)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_all :
  forall {x : a_var}{T : a_type} n A, ([x /s n] (∀[x⦂ T ]∙A)) = ((∀[x⦂ T ]∙[x /s S n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_ex :
  forall (x : a_var) T n A, ([x /s n] (∃[x⦂ T]∙A)) = ((∃[x⦂ T]∙[x /s S n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_next :
  forall (x : a_var) n A, ([x /s n] (a_next A)) = (a_next ([x /s n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_will :
  forall (x : a_var) n A, ([x /s n] (a_will A)) = (a_will ([x /s n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_prev :
  forall (x : a_var) n A, ([x /s n] (a_prev A)) = (a_prev ([x /s n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_was :
  forall (x : a_var) n A, ([x /s n] (a_was A)) = (a_was ([x /s n] A)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_acc :
  forall (x : a_var) n y z, ([x /s n] (y access z)) = (([x /s n] y) access ([x /s n] z)).
Proof.
  intros;
    destruct x;
    auto.
Qed.

Lemma sbst_x_call :
  forall (x : a_var) n y z m vMap, ([x /s n] (y calls z ▸ m ⟨ vMap ⟩)) =
                              (([x /s n] y) calls ([x /s n] z) ▸ ([x /s n] m) ⟨ ([x /s n] vMap) ⟩).
Proof.
  auto.
Qed.

Lemma sbst_x_extrn :
  forall (x : a_var) n y, ([x /s n] (y external)) = (([x /s n] y) external).
Proof.
  auto.
Qed.

Lemma sbst_x_intrn :
  forall (x : a_var) n y, ([x /s n] (y internal)) = (([x /s n] y) internal).
Proof.
  auto.
Qed.

Ltac sbst_simpl_actual :=
  match goal with
  | [H : context[[_ /s _] (a_expr _)] |- _] => rewrite sbst_x_exp in H
  | [H : context[[_ /s _] (a_class _ _)] |- _] => rewrite sbst_x_class in H

  | [H : context[[_ /s _] (¬ _)] |- _] => rewrite sbst_x_neg in H
  | [H : context[[_ /s _] (_ ∨ _)] |- _] => rewrite sbst_x_or in H
  | [H : context[[_ /s _] (_ ∧ _)] |- _] => rewrite sbst_x_and in H
  | [H : context[[_ /s _] (_ ⟶ _)] |- _] => rewrite sbst_x_arr in H

  | [H : context[[_ /s _] (a_next _)] |- _] => rewrite sbst_x_next in H
  | [H : context[[_ /s _] (a_will _)] |- _] => rewrite sbst_x_will in H
  | [H : context[[_ /s _] (a_prev _)] |- _] => rewrite sbst_x_prev in H
  | [H : context[[_ /s _] (a_was _)] |- _] => rewrite sbst_x_was in H

  | [H : context[[_ /s _] (∀[x⦂ _]∙_)] |- _] => rewrite sbst_x_all in H
  | [H : context[[_ /s _] (∃[x⦂ _]∙_)] |- _] => rewrite sbst_x_ex in H

  | [H : context[[_ /s _] (_ access _)] |- _] => rewrite sbst_x_acc in H
  | [H : context[[_ /s _] (_ calls _ ▸ _ ⟨ _ ⟩)] |- _] => rewrite sbst_x_call in H

  | [H : context[[_ /s _] (_ external)] |- _] => rewrite sbst_x_extrn in H
  | [H : context[[_ /s _] (_ internal)] |- _] => rewrite sbst_x_intrn in H

  | [|- context[[_ /s _] (a_expr _)]] => rewrite sbst_x_exp
  | [|- context[[_ /s _] (a_class _ _)]] => rewrite sbst_x_class

  | [|- context[[_ /s _] (¬ _)]] => rewrite sbst_x_neg
  | [|- context[[_ /s _] (_ ∨ _)]] => rewrite sbst_x_or
  | [|- context[[_ /s _] (_ ∧ _)]] => rewrite sbst_x_and
  | [|- context[[_ /s _] (_ ⟶ _)]] => rewrite sbst_x_arr

  | [|- context[[_ /s _] (a_next _)]] => rewrite sbst_x_next
  | [|- context[[_ /s _] (a_will _)]] => rewrite sbst_x_will
  | [|- context[[_ /s _] (a_prev _)]] => rewrite sbst_x_prev
  | [|- context[[_ /s _] (a_was _)]] => rewrite sbst_x_was

  | [|- context[[_ /s _] (∀[x⦂ _]∙_)]] => rewrite sbst_x_all
  | [|- context[[_ /s _] (∃[x⦂ _]∙_)]] => rewrite sbst_x_ex

  | [|- context[[_ /s _] (_ access _)]] => rewrite sbst_x_acc
  | [|- context[[_ /s _] (_ calls _ ▸ _ ⟨ _ ⟩)]] => rewrite sbst_x_call

  | [|- context[[_ /s _] (_ external)]] => rewrite sbst_x_extrn
  | [|- context[[_ /s _] (_ internal)]] => rewrite sbst_x_intrn
  end.


Ltac sbst_simpl :=
  repeat sbst_simpl_actual.

(** Rename  *)

Lemma rename_simpl_asgn :
  forall f r1 r2, ❲ f ↦ s_asgn r1 r2 ❳ = (s_asgn (❲ f ↦ r1 ❳) (❲ f ↦ r2 ❳)).
Proof. auto. Qed.

Lemma rename_simpl_meth :
  forall f x y m vMap, ❲ f ↦ s_meth x y m vMap ❳ = (s_meth (❲ f ↦ x ❳) (❲ f ↦ y ❳) m (❲ f ↦ vMap ❳)).
Proof. auto. Qed.

Lemma rename_simpl_new :
  forall f x C fMap, ❲ f ↦ s_new x C fMap ❳ = (s_new (❲ f ↦ x ❳) C (❲ f ↦ fMap ❳)).
Proof. auto. Qed.

Lemma rename_simpl_stmts :
  forall f s1 s2, ❲ f ↦ s_stmts s1 s2 ❳ = (s_stmts (❲ f ↦ s1 ❳) (❲ f ↦ s2 ❳)).
Proof. auto. Qed.

Lemma rename_simpl_rtrn :
  forall f x, ❲ f ↦ s_rtrn x ❳ = (s_rtrn (❲ f ↦ x ❳)).
Proof. auto. Qed.

Ltac rename_simpl_actual :=
  match goal with
  | [H : context[❲ _ ↦ (s_asgn _ _) ❳] |- _] =>
    rewrite rename_simpl_asgn in H
  | [H : context[❲ _ ↦ (s_meth _ _ _ _) ❳] |- _] =>
    rewrite rename_simpl_meth in H
  | [H : context[❲ _ ↦ (s_new _ _ _)❳] |- _] =>
    rewrite rename_simpl_new in H
  | [H : context[❲ _ ↦ (s_stmts _ _)❳] |- _] =>
    rewrite rename_simpl_stmts in H
  | [H : context[❲ _ ↦ (s_rtrn _)❳] |- _] =>
    rewrite rename_simpl_rtrn in H

  | [|- context[❲ _ ↦ (s_asgn _ _)❳]] =>
    rewrite rename_simpl_asgn
  | [|- context[❲ _ ↦ (s_meth _ _ _ _)❳]] =>
    rewrite rename_simpl_meth
  | [|- context[❲ _ ↦ (s_new _ _ _)❳]] =>
    rewrite rename_simpl_new
  | [|- context[❲ _ ↦ (s_stmts _ _)❳]] =>
    rewrite rename_simpl_stmts
  | [|- context[❲ _ ↦ (s_rtrn _)❳]] =>
    rewrite rename_simpl_rtrn
  end.

Ltac rename_simpl :=
  repeat rename_simpl_actual.
