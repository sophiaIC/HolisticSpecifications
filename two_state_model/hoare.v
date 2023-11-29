Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import assert.
Require Export external_state_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Hoare.

  Import LanguageDefinition.
  Import Assert.

  Inductive big_step_reduction : module -> config -> config -> Prop :=
  | bsr_single : forall M σ1 σ2, reduction M σ1 σ2 ->
                            big_step_reduction M σ1 σ2

  | bsr_trans : forall M σ1 σ2 σ3, reduction M σ1 σ2 ->
                              big_step_reduction M σ2 σ3 ->
                              big_step_reduction M σ1 σ2.

  Definition hoare_semantics (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    forall χ lcl s' ψ χ' lcl', big_step_reduction M (χ, frm lcl (s_seq s s') ;; nil) (χ', frm lcl' s' ;; nil) ->
                          sat M (χ, frm lcl (s_seq s s') ;; ψ) P ->
                          sat M (χ', frm lcl' s' ;; ψ) Q.

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare_semantics M P s Q)(at level 40).

  Definition asrt_proof (M : module)(A : asrt) : Prop := forall σ, sat M σ A.

  #[global] Instance exp_subst : Subst exp var exp:=
    {
      sbst :=
        fix sbst' e x e' :=
          match e with
          | e_var y => if eqb x y
                        then e'
                        else e_var y
          | e_fld e0 f => e_fld (sbst' e0 x e') f
          | e_class e0 C => e_class (sbst' e0 x e') C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 x e') g (sbst' e1 x e')
          | e_if e0 e1 e2 => e_if (sbst' e0 x e') (sbst' e1 x e') (sbst' e2 x e')
          | _ => e
          end
    }.

  #[global] Instance asrt_subst : Subst asrt var exp:=
    {
      sbst :=
        fix sbst' A x e :=
          match A with
          | a_exp e' => a_exp ([e /s x] e')

          | A1 ∧ A2 => (sbst' A1 x e) ∧ (sbst' A2 x e)
          | A1 ∨ A2 => (sbst' A1 x e) ∨ (sbst' A2 x e)
          | ¬ A' => ¬ (sbst' A' x e)
          | a_all A' => a_all (sbst' A' x e)
          | a_ex A' => a_ex (sbst' A' x e)

          | a_intl e' => a_intl ([e /s x] e')
          | a_extl e' => a_extl ([e /s x] e')

          | a_prt e' => a_prt ([e /s x] e')
          | a_prt_frm e1 e2 => a_prt_frm ([e /s x] e1) ([e /s x] e2)
          end
    }.

  #[global] Instance exp_acc_subst : Subst exp (var * fld) var :=
    {
      sbst :=
        fix sbst' e acc x :=
          match e with
          | e_fld e0 f0 => match e0, acc with
                          | e_ y, (z, f) => if (eqb y z && eqb f0 f)
                                           then e_ x
                                           else e
                          | _, _ => e_fld (sbst' e0 acc x) f0
                         end
          | e_class e0 C => e_class (sbst' e0 acc x) C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 acc x) g (sbst' e1 acc x)
          | e_if e0 e1 e2 => e_if (sbst' e0 acc x) (sbst' e1 acc x) (sbst' e2 acc x)
          | _ => e
          end
    }.

  #[global] Instance asrt_acc_subst : Subst asrt (var * fld) var:=
    {
      sbst :=
        fix sbst' A acc x :=
          match A with
          | a_exp e => a_exp ([x /s acc] e)

          | A1 ∧ A2 => (sbst' A1 acc x) ∧ (sbst' A2 acc x)
          | A1 ∨ A2 => (sbst' A1 acc x) ∨ (sbst' A2 acc x)
          | ¬ A' => ¬ (sbst' A' acc x)
          | a_all A' => a_all (sbst' A' acc x)
          | a_ex A' => a_ex (sbst' A' acc x)

          | a_intl e => a_intl ([x /s acc] e)
          | a_extl e => a_extl ([x /s acc] e)

          | a_prt e => a_prt ([x /s acc] e)
          | a_prt_frm e1 e2 => a_prt_frm ([x /s acc] e1) ([x /s acc] e2)
          end
    }.

  (* Proof Rules *)

  Reserved Notation "M ⊢ ⦃ P ⦄ s ⦃ Q ⦄" (at level 40).

  Inductive hoare : module -> asrt -> stmt -> asrt -> Prop :=
  | h_class : forall M e C s, M ⊢ ⦃ a_ e_class e C ⦄ s ⦃ a_ e_class e C ⦄

  | h_intl : forall M e s, M ⊢ ⦃ a_intl e ⦄ s ⦃ a_intl e ⦄

  | h_extl : forall M e s, hoare M (a_extl e) s (a_extl e)

  | h_read : forall M x y f e, hoare M ([e_ y∙f /s x] (a_exp e)) (s_read x y f) (a_exp e)

  | h_write1 : forall M x f y P, hoare M P (s_write x f y) (a_ e_ x∙f ⩵ e_ y)

  | h_write2 : forall M x f y e, hoare M ([y /s (x, f)] (a_exp e)) (s_write x f y) (a_exp e)

  | h_strengthen : forall M s P1 P2 Q, hoare M P1 s Q ->
                                  asrt_proof M (P2 ⟶ P1) ->
                                  hoare M P2 s Q

  | h_weaken : forall M s P Q1 Q2, hoare M P s Q1 ->
                              asrt_proof M (Q1 ⟶ Q2) ->
                              hoare M P s Q2

  | h_if : forall M e s1 s2 P Q, hoare M (P ∧ a_ e) s1 Q ->
                            hoare M (P ∧ ¬ a_ e) s2 Q ->
                            hoare M P (s_if e s1 s2) Q

  where "M ⊢ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare M P s Q).

  Inductive hoare_seq : module -> asrt -> stmts -> asrt -> Prop :=
  | h_stmt : forall M s P Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                        hoare_seq M P (s_stmt s) Q
  | h_seq : forall M s s' P Q R, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                            hoare_seq M Q s' R ->
                            hoare_seq M P (s_seq s s') R.

End Hoare.
