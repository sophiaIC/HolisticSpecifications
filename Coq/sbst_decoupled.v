Require Import common.
Require Import loo_def.
Require Import decoupling.

Class Raiseable (A : Type) :=
  {
    raise : A -> nat -> A
  }.

Notation "a '↑' n" := (raise a n)(at level 40).

Instance raiseNat : Raiseable nat :=
  {
    raise n m := if leb m n
                 then (S n)
                 else n
  }.
Instance raiseAVar : Raiseable a_var :=
  {
    raise x n := match x with
                 | a_hole m => a_hole (m ↑ n)
                 | _ => x
                 end
  }.

Instance raiseExpr : Raiseable expr :=
  {
    raise :=
      fix raise' e n :=
        match e with
        | ex_var x => ex_var (x ↑ n)
        | ex_eq e1 e2 => ex_eq (raise' e1 n) (raise' e2 n)
        | ex_if e1 e2 e3 => ex_if (raise' e1 n) (raise' e2 n) (raise' e3 n)
        | ex_acc_f e' f => ex_acc_f (raise' e' n) f
        | ex_acc_g e1 g e2 => ex_acc_g (raise' e1 n) g (raise' e2 n)
        | _ => e
        end
  }.

Instance raiseFn {A B : Type}`{Eq A}`{Raiseable B} : Raiseable (partial_map A B) :=
  {
    raise f n := fun x => bind (f x) (fun y => Some (y ↑ n))
  }.

Instance raiseAsrt : Raiseable asrt :=
  {
    raise :=
      fix raise' A n :=
        match A with
        | a_exp e => a_exp (e ↑ n)
        | a_class e C => a_class (e ↑ n) C

        | A1 ⇒ A2 => (raise' A1 n) ⇒ (raise' A2 n)
        | A1 ∧ A2 => (raise' A1 n) ∧ (raise' A2 n)
        | A1 ∨ A2 => (raise' A1 n) ∨ (raise' A2 n)
        | ¬ A' => ¬ (raise' A' n)

        | ∀x∙ A' => ∀x∙ (raise' A' (S n))
        | ∃x∙ A' => ∃x∙ (raise' A' (S n))

        | x access y => (x ↑ n) access (y ↑ n)
        | x calls y ▸ m ⟨ vMap ⟩ => (x ↑ n) calls (y ↑ n) ▸ m ⟨ vMap ↑ n ⟩

        | a_next A' => a_next (raise' A' n)
        | a_will A' => a_will (raise' A' n)
        | a_prev A' => a_prev (raise' A' n)
        | a_was A' => a_was (raise' A' n)

        | x external => (x ↑ n) external
        | x internal => (x ↑ n) internal

        | a_name x y => a_name (x ↑ n) y
        end
  }.

Lemma sbst_x_neg :
  forall (α : addr) n A, ([α /s n] ¬A) = (¬ ([α /s n]A)).
Proof.
  auto.
Qed.

Lemma sbst_x_arr :
  forall (α : addr) n A1 A2, ([α /s n] (A1 ⇒ A2)) = (([α /s n]A1) ⇒ ([α /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_and :
  forall (x : addr) n A1 A2, ([x /s n] (A1 ∧ A2)) = (([x /s n]A1) ∧ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_exp :
  forall (x : addr) n e, ([x /s n] (a_exp e)) = (a_exp ([x /s n] e)).
Proof.
  auto.
Qed.

Lemma sbst_x_class :
  forall (x : addr) n e C, ([x /s n] (a_class e C)) = (a_class ([x /s n] e) C).
Proof.
  auto.
Qed.

Lemma sbst_x_or :
  forall (x : addr) n A1 A2, ([x /s n] (A1 ∨ A2)) = (([x /s n]A1) ∨ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_all_x :
  forall (x : addr) n A, ([x /s n] (∀x∙A)) = ((∀x∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_ex_x :
  forall (x : addr) n A, ([x /s n] (∃x∙A)) = ((∃x∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_next :
  forall (x : addr) n A, ([x /s n] (a_next A)) = (a_next ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_will :
  forall (x : addr) n A, ([x /s n] (a_will A)) = (a_will ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_prev :
  forall (x : addr) n A, ([x /s n] (a_prev A)) = (a_prev ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_was :
  forall (x : addr) n A, ([x /s n] (a_was A)) = (a_was ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_acc :
  forall (x : addr) n y z, ([x /s n] (y access z)) = (([x /s n] y) access ([x /s n] z)).
Proof.
  auto.
Qed.

Lemma sbst_x_call :
  forall (x : addr) n y z m vMap, ([x /s n] (y calls z ▸ m ⟨ vMap ⟩)) = (([x /s n] y) calls ([x /s n] z) ▸ m ⟨ ([x /s n] vMap) ⟩).
Proof.
  auto.
Qed.

Lemma sbst_x_extrn :
  forall (x : addr) n y, ([x /s n] (y external)) = (([x /s n] y) external).
Proof.
  auto.
Qed.

Lemma sbst_x_intrn :
  forall (x : addr) n y, ([x /s n] (y internal)) = (([x /s n] y) internal).
Proof.
  auto.
Qed.

Lemma sbst_x_name :
  forall (x : addr) n y z, ([x /s n] (a_name y z)) = (a_name ([x /s n] y) z).
Proof.
  auto.
Qed.

Ltac sbst_simpl_actual :=
  match goal with
  | [H : context[[_ /s _] (a_exp _)] |- _] => rewrite sbst_x_exp in H
  | [H : context[[_ /s _] (a_class _ _)] |- _] => rewrite sbst_x_class in H

  | [H : context[[_ /s _] (¬ _)] |- _] => rewrite sbst_x_neg in H
  | [H : context[[_ /s _] (_ ∨ _)] |- _] => rewrite sbst_x_or in H
  | [H : context[[_ /s _] (_ ∧ _)] |- _] => rewrite sbst_x_and in H
  | [H : context[[_ /s _] (_ ⇒ _)] |- _] => rewrite sbst_x_arr in H

  | [H : context[[_ /s _] (a_next _)] |- _] => rewrite sbst_x_next in H
  | [H : context[[_ /s _] (a_will _)] |- _] => rewrite sbst_x_will in H
  | [H : context[[_ /s _] (a_prev _)] |- _] => rewrite sbst_x_prev in H
  | [H : context[[_ /s _] (a_was _)] |- _] => rewrite sbst_x_was in H

  | [H : context[[_ /s _] (∀x∙_)] |- _] => rewrite sbst_x_all_x in H
  | [H : context[[_ /s _] (∃x∙_)] |- _] => rewrite sbst_x_ex_x in H

  | [H : context[[_ /s _] (_ access _)] |- _] => rewrite sbst_x_acc in H
  | [H : context[[_ /s _] (_ calls _ ▸ _ ⟨ _ ⟩)] |- _] => rewrite sbst_x_call in H

  | [H : context[[_ /s _] (_ external)] |- _] => rewrite sbst_x_extrn in H
  | [H : context[[_ /s _] (_ internal)] |- _] => rewrite sbst_x_intrn in H

  | [H : context[[_ /s _] (a_name _ _)] |- _] => rewrite sbst_x_name in H

  | [|- context[[_ /s _] (a_exp _)]] => rewrite sbst_x_exp
  | [|- context[[_ /s _] (a_class _ _)]] => rewrite sbst_x_class

  | [|- context[[_ /s _] (¬ _)]] => rewrite sbst_x_neg
  | [|- context[[_ /s _] (_ ∨ _)]] => rewrite sbst_x_or
  | [|- context[[_ /s _] (_ ∧ _)]] => rewrite sbst_x_and
  | [|- context[[_ /s _] (_ ⇒ _)]] => rewrite sbst_x_arr

  | [|- context[[_ /s _] (a_next _)]] => rewrite sbst_x_next
  | [|- context[[_ /s _] (a_will _)]] => rewrite sbst_x_will
  | [|- context[[_ /s _] (a_prev _)]] => rewrite sbst_x_prev
  | [|- context[[_ /s _] (a_was _)]] => rewrite sbst_x_was

  | [|- context[[_ /s _] (∀x∙_)]] => rewrite sbst_x_all_x
  | [|- context[[_ /s _] (∃x∙_)]] => rewrite sbst_x_ex_x

  | [|- context[[_ /s _] (_ access _)]] => rewrite sbst_x_acc
  | [|- context[[_ /s _] (_ calls _ ▸ _ ⟨ _ ⟩)]] => rewrite sbst_x_call

  | [|- context[[_ /s _] (_ external)]] => rewrite sbst_x_extrn
  | [|- context[[_ /s _] (_ internal)]] => rewrite sbst_x_intrn

  | [|- context[[_ /s _] (a_name _ _)]] => rewrite sbst_x_name
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
