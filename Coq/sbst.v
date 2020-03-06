Require Import common.
Require Import loo_def.
Require Import chainmail.

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

Instance raiseExp : Raiseable exp :=
  {
    raise :=
      fix raise' e n :=
        match e with
        | e_hole m => e_hole (m ↑ n)
        | e_eq e1 e2 => e_eq (raise' e1 n) (raise' e2 n)
        | e_if e1 e2 e3 => e_if (raise' e1 n) (raise' e2 n) (raise' e3 n)
        | e_acc_f e' f => e_acc_f (raise' e' n) f
        | e_acc_g e1 g e2 => e_acc_g (raise' e1 n) g (raise' e2 n)
        | _ => e
        end
  }.

Instance raiseAVar : Raiseable a_var :=
  {
    raise x n := match x with
                 | a_hole m => a_hole (m ↑ n)
                 | _ => x
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
        | a_eq e1 e2 => a_eq (e1 ↑ n) (e2 ↑ n)
        | a_class e C => a_class (e ↑ n) C
        | a_set e Σ => a_set (e ↑ n) Σ

        | A1 ⇒ A2 => (raise' A1 n) ⇒ (raise' A2 n)
        | A1 ∧ A2 => (raise' A1 n) ∧ (raise' A2 n)
        | A1 ∨ A2 => (raise' A1 n) ∨ (raise' A2 n)
        | ¬ A' => ¬ (raise' A' n)

        | ∀x∙ A' => ∀x∙ (raise' A' (S n))
        | ∃x∙ A' => ∃x∙ (raise' A' (S n))
        | ∀S∙ A' => ∀S∙ (raise' A' (S n))
        | ∃S∙ A' => ∃S∙ (raise' A' (S n))

        | x access y => (x ↑ n) access (y ↑ n)
        | x calls y ∎ m ⟨ vMap ⟩ => (x ↑ n) calls (y ↑ n) ∎ m ⟨ vMap ↑ n ⟩

        | a_next A' => a_next (raise' A' n)
        | a_will A' => a_will (raise' A' n)
        | a_prev A' => a_prev (raise' A' n)
        | a_was A' => a_was (raise' A' n)

        | a_in A' Σ => a_in (raise' A' n) Σ

        | x external => (x ↑ n) external
        | x internal => (x ↑ n) internal
        end
  }.

Lemma sbst_x_neg :
  forall (x : var) n A, ([x /s n] ¬A) = (¬ ([x /s n]A)).
Proof.
  auto.
Qed.

Lemma sbst_x_arr :
  forall (x : var) n A1 A2, ([x /s n] (A1 ⇒ A2)) = (([x /s n]A1) ⇒ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_and :
  forall (x : var) n A1 A2, ([x /s n] (A1 ∧ A2)) = (([x /s n]A1) ∧ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_exp :
  forall (x : var) n e, ([x /s n] (a_exp e)) = (a_exp ([x /s n] e)).
Proof.
  auto.
Qed.

Lemma sbst_x_aeq :
  forall (x : var) n e1 e2, ([x /s n] (a_eq e1 e2)) = (a_eq ([x /s n] e1) ([x /s n] e2)).
Proof.
  auto.
Qed.

Lemma sbst_x_class :
  forall (x : var) n e C, ([x /s n] (a_class e C)) = (a_class ([x /s n] e) C).
Proof.
  auto.
Qed.

Lemma sbst_x_set :
  forall (x : var) n e Σ, ([x /s n] (a_set e Σ)) = (a_set ([x /s n] e) Σ).
Proof.
  auto.
Qed.

Lemma sbst_x_or :
  forall (x : var) n A1 A2, ([x /s n] (A1 ∨ A2)) = (([x /s n]A1) ∨ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_all_x :
  forall (x : var) n A, ([x /s n] (∀x∙A)) = ((∀x∙[x /s S n] A)).
Proof.
  auto.
Qed.
          
Lemma sbst_x_all_Σ :
  forall (x : var) n A, ([x /s n] (∀S∙A)) = ((∀S∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_ex_x :
  forall (x : var) n A, ([x /s n] (∃x∙A)) = ((∃x∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_ex_Σ :
  forall (x : var) n A, ([x /s n] (∃S∙A)) = ((∃S∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_all_x :
  forall (x : varSet) n A, ([x /s n] (∀x∙A)) = ((∀x∙[x /s n] A)).
Proof.
  auto.
Qed.
          
Lemma sbst_Σ_all_Σ :
  forall (x : varSet) n A, ([x /s n] (∀S∙A)) = ((∀S∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_ex_x :
  forall (x : varSet) n A, ([x /s n] (∃x∙A)) = ((∃x∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_ex_Σ :
  forall (x : varSet) n A, ([x /s n] (∃S∙A)) = ((∃S∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_next :
  forall (x : var) n A, ([x /s n] (a_next A)) = (a_next ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_will :
  forall (x : var) n A, ([x /s n] (a_will A)) = (a_will ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_prev :
  forall (x : var) n A, ([x /s n] (a_prev A)) = (a_prev ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_was :
  forall (x : var) n A, ([x /s n] (a_was A)) = (a_was ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_acc :
  forall (x : var) n y z, ([x /s n] (y access z)) = (([x /s n] y) access ([x /s n] z)).
Proof.
  auto.
Qed.

Lemma sbst_x_call :
  forall (x : var) n y z m vMap, ([x /s n] (y calls z ∎ m ⟨ vMap ⟩)) = (([x /s n] y) calls ([x /s n] z) ∎ m ⟨ ([x /s n] vMap) ⟩).
Proof.
  auto.
Qed.

Lemma sbst_x_in :
  forall (x : var) n A Σ, ([x /s n] (a_in A Σ)) = (a_in ([x /s n] A) Σ).
Proof.
  auto.
Qed.

Lemma sbst_Σ_in :
  forall (x : varSet) n A Σ, ([x /s n] (a_in A Σ)) = (a_in ([x /s n] A) ([x /s n] Σ)).
Proof.
  auto.
Qed.

Lemma sbst_x_extrn :
  forall (x : var) n y, ([x /s n] (y external)) = (([x /s n] y) external).
Proof.
  auto.
Qed.

Lemma sbst_x_intrn :
  forall (x : var) n y, ([x /s n] (y internal)) = (([x /s n] y) internal).
Proof.
  auto.
Qed.

Ltac sbst_simpl_actual :=
  match goal with
  | [H : context[[_ /s _] (a_exp _)] |- _] => rewrite sbst_x_exp in H
  | [H : context[[_ /s _] (a_eq _ _)] |- _] => rewrite sbst_x_aeq in H
  | [H : context[[_ /s _] (a_class _ _)] |- _] => rewrite sbst_x_class in H
  | [H : context[[_ /s _] (a_set _ _)] |- _] => rewrite sbst_x_set in H

  | [H : context[[_ /s _] (¬ _)] |- _] => rewrite sbst_x_neg in H
  | [H : context[[_ /s _] (_ ∨ _)] |- _] => rewrite sbst_x_or in H
  | [H : context[[_ /s _] (_ ∧ _)] |- _] => rewrite sbst_x_and in H
  | [H : context[[_ /s _] (_ ⇒ _)] |- _] => rewrite sbst_x_arr in H

  | [H : context[[_ /s _] (a_next _)] |- _] => rewrite sbst_x_next in H
  | [H : context[[_ /s _] (a_will _)] |- _] => rewrite sbst_x_will in H
  | [H : context[[_ /s _] (a_prev _)] |- _] => rewrite sbst_x_prev in H
  | [H : context[[_ /s _] (a_was _)] |- _] => rewrite sbst_x_was in H

  | [H : context[[_ /s _] (∀x∙_)] |- _] => rewrite sbst_x_all_x in H
  | [H : context[[_ /s _] (∀S∙_)] |- _] => rewrite sbst_x_all_Σ in H
  | [H : context[[_ /s _] (∃x∙_)] |- _] => rewrite sbst_x_ex_x in H
  | [H : context[[_ /s _] (∃S∙_)] |- _] => rewrite sbst_x_ex_Σ in H

  | [H : context[[_ /s _] (_ access _)] |- _] => rewrite sbst_x_acc in H
  | [H : context[[_ /s _] (_ calls _ ∎ _ ⟨ _ ⟩)] |- _] => rewrite sbst_x_call in H

  | [H : context[[_ /s _] (a_in _ _)] |- _] => rewrite sbst_x_in in H
  | [H : context[[_ /s _] (_ external)] |- _] => rewrite sbst_x_extrn in H
  | [H : context[[_ /s _] (_ internal)] |- _] => rewrite sbst_x_intrn in H

  | [|- context[[_ /s _] (a_exp _)]] => rewrite sbst_x_exp
  | [|- context[[_ /s _] (a_eq _ _)]] => rewrite sbst_x_aeq
  | [|- context[[_ /s _] (a_class _ _)]] => rewrite sbst_x_class
  | [|- context[[_ /s _] (a_set _ _)]] => rewrite sbst_x_set

  | [|- context[[_ /s _] (¬ _)]] => rewrite sbst_x_neg
  | [|- context[[_ /s _] (_ ∨ _)]] => rewrite sbst_x_or
  | [|- context[[_ /s _] (_ ∧ _)]] => rewrite sbst_x_and
  | [|- context[[_ /s _] (_ ⇒ _)]] => rewrite sbst_x_arr

  | [|- context[[_ /s _] (a_next _)]] => rewrite sbst_x_next
  | [|- context[[_ /s _] (a_will _)]] => rewrite sbst_x_will
  | [|- context[[_ /s _] (a_prev _)]] => rewrite sbst_x_prev
  | [|- context[[_ /s _] (a_was _)]] => rewrite sbst_x_was

  | [|- context[[_ /s _] (∀x∙_)]] => rewrite sbst_x_all_x
  | [|- context[[_ /s _] (∀S∙_)]] => rewrite sbst_x_all_Σ
  | [|- context[[_ /s _] (∃x∙_)]] => rewrite sbst_x_ex_x
  | [|- context[[_ /s _] (∃S∙_)]] => rewrite sbst_x_ex_Σ

  | [|- context[[_ /s _] (_ access _)]] => rewrite sbst_x_acc
  | [|- context[[_ /s _] (_ calls _ ∎ _ ⟨ _ ⟩)]] => rewrite sbst_x_call

  | [|- context[[_ /s _] (a_in _ _)]] => rewrite sbst_x_in
  | [|- context[[_ /s _] (_ external)]] => rewrite sbst_x_extrn
  | [|- context[[_ /s _] (_ internal)]] => rewrite sbst_x_intrn
  end.

Ltac sbst_simpl :=
  repeat sbst_simpl_actual.