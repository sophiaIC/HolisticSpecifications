Require Export Arith.
Require Import List.
Require Import Bool.
Require Import String.

Require Import common.
Require Import language_def.
Require Import subst.

Require Import assert_theory.
Require Import hoare.
Require Import spec.
Require Import shop.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

(** 
    The majority of assumptions we make are detailed within this file. 
 *)

Module Assumptions.

  Import LanguageDefinition.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.
  Import SpecSatisfaction.
  Import Shop.

  Open Scope hoare_scope.

  Lemma intro_ex_middle_hoare :
    forall M A A1 A2 s, M ⊢ ⦃ (A ∨ ¬ A) ∧ A1 ⦄ s ⦃ A2 ⦄ ->
                        M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄.
  Proof.
    intros.
    eapply h_strengthen;
      [eassumption|];
      intros_entails;
      asrt_sat_auto_destruct_conj;
      auto;
      apply sat_excluded_middle.
  Qed.

  Lemma split_excluded_middle_hoare :
    forall M A A1 A2 s, M ⊢ ⦃ (A ∧ A1) ∨ (¬ A ∧ A1) ⦄ s ⦃ A2 ⦄ ->
                        M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄.
  Proof.
    intros.
    apply intro_ex_middle_hoare with (A:=A).
    eapply h_strengthen;
      [|apply or_and_dist1];
      auto.
  Qed.

  Ltac hq_conj_post_conseq :=
    match goal with
    | [|- _ ⊢ ⦃ ?A1 ⦄ _ ⦃ ?A2 ∧ ?A3 ⦄ || ⦃ ?A ⦄ ] =>
        apply hq_conseq with (A4:=A1)(A5:=A2)(A6:=A)
    end.

  Parameter hq_conj_assoc1_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.

  Parameter hq_conj_assoc2_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄.

  Parameter hq_conj_assoc2_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.

  Parameter hq_conj_assoc1_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄.


  Parameter rewrite_hoare_quad1 :
    forall M A A1, M ⊢ A1 ⊆ A ->
              forall A2 A3 s, M ⊢ ⦃ A ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.

  Parameter rewrite_hoare_quad2 :
    forall M A A2, M ⊢ A ⊆ A2 ->
              forall A1 A3 s, M ⊢ ⦃ A1 ⦄ s ⦃ A ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.

  Parameter conj_strengthen_entails :
    forall M A1 A2 A, M ⊢ A1 ⊆ A2 ->
                 M ⊢ (A1 ∧ A) ⊆ A2.

  Parameter entails_prt_intl :
    forall M x y C, M ⊢ ((a_ e_typ y (t_cls C)) ∧ ¬ a_extl y) ⊆ a_prt_frm x y.

  Parameter entails_intl :
    forall M e C, C ∈ (snd M) ->
                  M ⊢ (a_ (e_typ e (t_cls C))) ⊆ (¬ a_extl e).

  Parameter entails_extl :
    forall M e, M ⊢ (a_ (e_typ e t_ext)) ⊆ (a_extl e).

  Parameter entails_different_type_neq :
    forall M e1 e2 T1 T2, T1 <> T2 ->
                     M ⊢ ((a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2)) ⊆
                       ¬ (a_ (e_eq e1 e2)).

  Parameter exp_neq_different_type :
    forall M e1 e2 T1 T2,
      T1 <> T2 ->
      M ⊢ (a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2) ⊆
                               (¬ a_ (e_eq e1 e2)).

  Parameter exp_eq_same_type :
    forall M e1 e2 T,
      M ⊢ (a_ e_typ e1 T) ∧ (a_ e_eq e1 e2) ⊆ (a_ e_typ e2 T).

  Parameter entails_eq_trans :
    forall M e1 e2 e3, M ⊢ a_ (e_eq e1 e2) ∧ a_ (e_eq e2 e3) ⊆ a_ (e_eq e1 e3).

  Parameter entails_eq_fld :
    forall M e1 e2 f, M ⊢ a_ (e_eq e1 e2) ⊆ a_ (e_eq (e1 ∙ f) (e2 ∙ f)).

  Parameter entails_eq_not_prt_frm :
    forall M e1 e2, M ⊢ a_ (e1 ⩵ e2) ⊆ ¬ a_prt_frm e1 e2.

  Parameter entails_prt_eq :
    forall M e1 e2, M ⊢ a_ (e_eq e1 e2) ∧ a_prt e1 ⊆ a_prt e2.

  Parameter entails_prt_null :
    forall M, M ⊢ a_prt e_null ⊆ a_false.

  Parameter hoare_false :
    forall M s A, M ⊢ ⦃ a_false ⦄ s ⦃ A ⦄.

  Parameter neg_absurd :
    forall M A, M ⊢ A ∧ ¬ A ⊆ a_false.

  Parameter hoare_UL_write_different_field :
    forall M x f y f' e z,
      f <> f' ->
      hoare_base M (a_ (e_eq (e_fld (e_ x) f) (e_ z)))
                 (s_write y f' e)
                 (a_ (e_eq (e_fld (e_ x) f) (e_ z))).

  Parameter hoare_UL_write_different_field_lt :
    forall M x f y f' e z,
      f <> f' ->
      hoare_base M (a_ (e_lt (e_ z) (e_fld (e_ x) f)))
        (s_write y f' e)
        (a_ (e_lt (e_ z) (e_fld (e_ x) f))).

  Parameter hoare_UL_write_different_object :
    forall M x f y f' e z,
      hoare_base M ((¬ (a_ (e_eq (e_ x) (e_ y)))) ∧
                      (a_ (e_eq (e_fld (e_ x) f) (e_ z))))
                 (s_write y f' e)
                 (a_ (e_eq (e_fld (e_ x) f) (e_ z))).

  Parameter hoare_UL_addition_lt :
    forall M x f y z f' i,
      hoare_base M (a_ (e_lt (e_ y) (e_fld (e_ x) f)))
        (s_write z f' (e_plus ((e_ z) ∙ f') i))
        (a_ (e_lt (e_ y) (e_fld (e_ x) f))).

  Parameter UL_post_true :
    forall M A s, hoare_base M A s (a_true).

  Parameter hoare_ul_write_to_different_object_lt :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄.

  Parameter hoare_ul_write_to_different_object_eq :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄.

  Parameter hoare_ul_return_bool_preserves_fld_lt :
    forall M x y f, hoare_base M
                 ((a_ e_typ (e_ result) t_bool) ∧ a_ (e_lt (e_ x) ((e_ y) ∙ f)))
                 (ret e_false)
                 (a_ (e_lt (e_ x) ((e_ y) ∙ f))).

  Parameter hoare_ul_return_bool_preserves_fld_eq :
    forall M x y f, hoare_base M
                      ((a_ e_typ (e_ result) t_bool) ∧ a_ (e_eq ((e_ x) ∙ f) (e_ y)))
                      (ret e_false)
                      (a_ (e_eq ((e_ x) ∙ f) (e_ y))).

  Fixpoint and A1 A2 :=
    match A1 with
    | A ∧ A' => and A (and A' A2)
    | _ => A1 ∧ A2
    end.

  Fixpoint simplify_conj (A : asrt) : asrt :=
    match A with
    | (a_true) ∧ A' => (simplify_conj A')
    | A' ∧ (a_true) => (simplify_conj A')
    | A1 ∧ A2 => and (simplify_conj A1) (simplify_conj A2)
    | _ => A
    end.

  Fixpoint simplify_neg (A : asrt) : asrt :=
    match A with
    | ¬ ¬ A' => simplify_neg A'
    | A1 ∧ A2 => (simplify_neg A1) ∧ (simplify_neg A2)
    | a_all C A' => a_all C (simplify_neg A')
    | _  => A
    end.

  Parameter simplify_conj_entails1 :
    forall M A, M ⊢ A ⊆ (simplify_conj A).

  Parameter simplify_conj_entails2 :
    forall M A, M ⊢ (simplify_conj A) ⊆ A.

  Parameter entails_prt_int :
    forall M e1 e2 C, M ⊢ (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_int)) ⊆ (a_prt_frm e1 e2).

  Parameter entails_prt_bool :
    forall M e1 e2 C, M ⊢ (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_bool)) ⊆ (a_prt_frm e1 e2).

  Parameter hoare_ul_assgn :
    forall M A x e, hoare_base M ([ e /s x ] A ) (s_read x e) A.

End Assumptions.
