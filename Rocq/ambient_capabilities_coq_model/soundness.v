Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert.
Require Export operational_semantics.
Require Import assert_theory.
Require Import hoare.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Soundness.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.

  Lemma strengthening_sound :
    forall M s P1 P2 Q,
      M ⊨ ⦃ P1 ⦄ s ⦃ Q ⦄ ->
      M ⊢ P2 ⊆ P1 ->
      M ⊨ ⦃ P2 ⦄ s ⦃ Q ⦄.
  Proof.
    unfold hoare_triple_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    apply H.
    apply entails_strengthening with (A1:=P2); auto.
  Qed.

  Lemma weakening_sound :
    forall M s P Q1 Q2,
      M ⊨ ⦃ P ⦄ s ⦃ Q1 ⦄ ->
      M ⊢ Q1 ⊆ Q2 ->
      M ⊨ ⦃ P ⦄ s ⦃ Q2 ⦄.
  Proof.
    unfold hoare_triple_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    apply entails_strengthening with (A1:=Q1); auto.
  Qed.

  Lemma h_and_sound :
    forall M P1 P2 s Q1 Q2,
      M ⊨ ⦃ P1 ⦄ s ⦃ Q1 ⦄ ->
      M ⊨ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
      M ⊨ ⦃ P1 ∧ P2 ⦄ s ⦃ Q1 ∧ Q2 ⦄.
  Proof.
    unfold hoare_triple_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    specialize (H0 χ lcl s' ψ χ' lcl' H1).
    inversion H2; subst; eauto with assert_db.
  Qed.

  Lemma read_sound :
    forall M P x y f,
      M ⊨ ⦃ [e_ y ∙ f /s x] P ⦄ s_read x y f ⦃ P ⦄.
  Proof.
    intros.
    unfold hoare_triple_semantics.
    intros.

    inversion H; subst.

    * 
  Admitted.

  Lemma if_sound :
    forall M e s1 s2 P Q,
      M ⊨ ⦃ P ∧ a_ e ⦄ s1 ⦃ Q ⦄ ->
      M ⊨ ⦃ P ∧ ¬ a_ e ⦄ s2 ⦃ Q ⦄ ->
      M ⊨ ⦃ P ⦄ s_if e s1 s2 ⦃ Q ⦄.
  Proof.
  Admitted.

  Lemma write_prt_frm_sound :
    forall M w x y z f,
      M ⊨ ⦃ a_prt_frm (e_ w) (e_ x) ∧ a_prt_frm (e_ w) (e_ z) ⦄ s_write y f z ⦃ a_prt_frm (e_ w) (e_ x) ⦄.
  Proof.

  Admitted.

  Lemma write_prt_sound :
    forall M x y f z,
      M ⊨ ⦃ a_prt (e_ x) ⦄
        (s_write y f z)
        ⦃ a_prt (e_ x) ⦄.
  Proof.
  Admitted.

  Lemma new_prt_frm1_sound :
    forall M x C e1 e2,
      M ⊨ ⦃ a_prt_frm e1 e2 ⦄
        (s_new x C)
        ⦃ a_prt_frm e1 e2 ⦄.
  Proof.
  Admitted.

  Lemma new_prt_frm2_sound :
    forall M x C e,
      M ⊨ ⦃ a_true ⦄
        (s_new x C)
        ⦃ a_prt_frm (e_ x) e ⦄.
  Proof.
  Admitted.


  Lemma new_prt1_sound :
    forall M x C e,
      M ⊨ ⦃ a_prt e ⦄ (s_new x C) ⦃ a_prt e ⦄.
  Proof.
  Admitted.

  Lemma new_prt2_sound :
    forall M x C,
      M ⊨ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄.
  Proof.
  Admitted.

  #[export]
    Hint Resolve
    strengthening_sound weakening_sound h_and_sound read_sound if_sound write_prt_frm_sound write_prt_sound new_prt1_sound new_prt2_sound new_prt_frm1_sound new_prt_frm2_sound : hoare_db.

  #[export]
    Hint Constructors hoare_extension : hoare_db.

  #[export]
   Hint Constructors hoare_quad : hoare_db.

  Theorem hoare_triple_extension_sound :
    forall M P s Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
               M ⊨ ⦃ P ⦄ s ⦃ Q ⦄.
  Proof.
    induction_hoare; eauto with hoare_db.

    * (* hoare base *)
      apply hoare_base_soundness; auto.
  Qed.

  (* Auxillary Lemmas go here *)

  Definition ordering: 

  Theorem hoare_quadruple_sound :
    forall M P s Q A, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ || ⦃ A ⦄ ->
                 M ⊨ ⦃ P ⦄ s ⦃ Q ⦄ || ⦃ A ⦄.
  Proof.
    induction_hoare; eauto with hoare_db.

    * (* mid *)
      apply hq_mid.

  Admitted.

End Soundness.
