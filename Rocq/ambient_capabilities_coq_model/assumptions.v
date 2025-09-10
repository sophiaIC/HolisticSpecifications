Require Export Arith.
Require Import List.
Require Import Bool.
Require Import String.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert.
Require Export operational_semantics.
Require Import assert_theory.
Require Import hoare.
Require Import spec.
Require Import shop.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Assumptions.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.
  Import SpecSatisfaction.
  Import Shop.

  Open Scope hoare_scope.
  Open Scope assert_scope.

  Lemma apply_entails :
    forall M σ A1 A2, M ⊢ A1 ⊆ A2 ->
                 sat M σ A1 ->
                 sat M σ A2.
  Proof.
  Admitted.

   Lemma entails_fld_type :
    forall M C f T, typeOf_f M C f = Some T ->
               forall e, M ⊢ (a_ (e_typ e (t_cls C))) ⊆
                           (a_ (e_typ (e_fld e f) T)).
  Proof.

  Admitted.

  Lemma sat_excluded_middle :
    forall M σ A, sat M σ (A ∨ ¬ A).
  Proof.
  Admitted.

  Lemma sat_neg_is_not_sat :
    forall M σ A, sat M σ (¬ A) ->
             ~ sat M σ A.
  Proof.
    intros.
  Admitted.

  Lemma entails_excluded_middle :
    forall M A, M ⊢ a_true ⊆ (A ∨ ¬ A).
  Admitted.

  Lemma or_and_dist1 :
    forall M A1 A2 A, M ⊢ (A1 ∨ A2) ∧ A ⊆ (A1 ∧ A) ∨ (A2 ∧ A).
  Admitted.

  Lemma or_and_dist2 :
    forall M A1 A2 A, M ⊢ (A1 ∧ A) ∨ (A2 ∧ A) ⊆ (A1 ∨ A2) ∧ A.
  Admitted.

  Lemma entails_assoc1 :
    forall M A1 A2 A3, M ⊢ ((A1 ∧ A2) ∧ A3) ⊆ (A1 ∧ (A2 ∧ A3)). Admitted.

  Lemma entails_assoc2 :
    forall M A1 A2 A3, M ⊢ (A1 ∧ (A2 ∧ A3)) ⊆ ((A1 ∧ A2) ∧ A3). Admitted.

  Lemma entails_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊆ A2 ->
                  M ⊢ A2 ⊆ A3 ->
                  M ⊢ A1 ⊆ A3.
  Admitted.

  Lemma hq_conj_assoc1_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc2_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc2_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc1_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma rewrite_hoare_quad1 :
    forall M A A1, M ⊢ A1 ⊆ A ->
              forall A2 A3 s, M ⊢ ⦃ A ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.
  Proof.
  Admitted.

  Lemma rewrite_hoare_quad2 :
    forall M A A2, M ⊢ A ⊆ A2 ->
              forall A1 A3 s, M ⊢ ⦃ A1 ⦄ s ⦃ A ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.
  Proof.
  Admitted.

  Lemma conj_strengthen_entails :
    forall M A1 A2 A, M ⊢ A1 ⊆ A2 ->
                 M ⊢ (A1 ∧ A) ⊆ A2.
  Proof.
  Admitted.

  Lemma entails_prt_intl :
    forall M x y C, M ⊢ ((a_ e_typ y (t_cls C)) ∧ ¬ a_extl y) ⊆ a_prt_frm x y.
  Proof.
  Admitted.

  Lemma entails_intl :
    forall M e C, C ∈ (snd M) ->
             M ⊢ (a_ (e_typ e (t_cls C))) ⊆ (¬ a_extl e).
  Admitted.

  Lemma entails_different_type_neq :
    forall M e1 e2 T1 T2, T1 <> T2 ->
                     M ⊢ ((a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2)) ⊆
                       ¬ (a_ (e_eq e1 e2)).
  Proof.
    intros.
  Admitted.

  Lemma exp_neq_different_type :
    forall M e1 e2 T1 T2,
      T1 <> T2 ->
      M ⊢ (a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2) ⊆
                               (¬ a_ (e_eq e1 e2)).
  Proof.
  Admitted.

  Lemma exp_eq_same_type :
    forall M e1 e2 T,
      M ⊢ (a_ e_typ e1 T) ∧ (a_ e_eq e1 e2) ⊆ (a_ e_typ e2 T).
  Proof.
  Admitted.

  Lemma entails_eq_trans :
    forall M e1 e2 e3, M ⊢ a_ (e_eq e1 e2) ∧ a_ (e_eq e2 e3) ⊆ a_ (e_eq e1 e3).
  Admitted.

  Lemma entails_eq_fld :
    forall M e1 e2 f, M ⊢ a_ (e_eq e1 e2) ⊆ a_ (e_eq (e1 ∙ f) (e2 ∙ f)).
  Admitted.

  Lemma entails_eq_not_prt_frm :
    forall M e1 e2, M ⊢ a_ (e1 ⩵ e2) ⊆ ¬ a_prt_frm e1 e2.
  Admitted.

  Lemma entails_prt_eq :
    forall M e1 e2, M ⊢ a_ (e_eq e1 e2) ∧ a_prt e1 ⊆ a_prt e2.
  Admitted.

  Lemma entails_prt_null :
    forall M, M ⊢ a_prt e_null ⊆ a_false.
  Admitted.

  Lemma hoare_false :
    forall M s A, M ⊢ ⦃ a_false ⦄ s ⦃ A ⦄.
  Admitted.

  Lemma neg_absurd :
    forall M A, M ⊢ A ∧ ¬ A ⊆ a_false.
  Admitted.

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

  Lemma hoare_ul_write_to_different_object_lt :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄.
  Admitted.

  Lemma hoare_ul_write_to_different_object_eq :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄.
  Admitted.

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

  Lemma simplify_conj_entails1 :
    forall M A, M ⊢ A ⊆ (simplify_conj A).
  Proof.
  Admitted.

  Lemma simplify_conj_entails2 :
    forall M A, M ⊢ (simplify_conj A) ⊆ A.
  Proof.
  Admitted.

End Assumptions.
