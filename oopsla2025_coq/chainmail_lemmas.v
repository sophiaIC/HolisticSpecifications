Require Export Arith.
Require Import List.
Require Import Bool.
Require Import String.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.

Require Import assert_theory.
Require Import hoare.
Require Import spec.
Require Import shop.
Require Import assumptions.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


(** *
    Suppporting lemmas, tactics, and definitions for constructing chainmail proofs
 *)

Module ChainmailLemmas.

  Import LanguageDefinition.
  Import AssertTheory.
  Import SubstDefn.
  Import Hoare.
  Import SpecSatisfaction.
  Import Shop.
  Import Assumptions.

  Open Scope hoare_scope.

  Ltac apply_hq_sequ_with_mid_eq_fst :=
    match goal with
    | [ H : typeOf_f ?M ?C ?f = Some ?T  |- ?M ⊢ ⦃ ?A ⦄ (s_read ?x (e_fld _ ?f)) ;; _ ⦃ _ ⦄ || ⦃ _ ⦄] => apply hq_sequ with (A2:=(a_ (e_typ (e_ x) T)) ∧ A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ ] => apply h_seq with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    end.

  Ltac simpl_types :=
    unfold a_typs;
    unfold asrt_frm_list;
    simpl in *.

  Open Scope string_scope.

  Ltac split_post_condition_by_conjunction :=
    match goal with
    | [|- ?M ⊢ ⦃ ?A1 ⦄ ?s ⦃ ?A2 ∧ ?A3 ⦄ || ⦃ ?Ainv ⦄ ] =>
        apply hq_conseq with (A4:=A1 ∧ A1)(A5:=A2 ∧ A3)(A6:=Ainv);
        [apply hq_combine| apply conj_entails_dup with (A:=A1) | | ];
        try solve [apply entails_refl]
    end.

  Ltac by_hq_types2 :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ a_ (e_typ (e_ ?x) ?T) ⦄ || ⦃ ?A ⦄ ] =>
        apply hq_conseq with (A4:=a_ (e_typ (e_ x) T))(A5:=a_ (e_typ (e_ x) T))(A6:=A);
        [apply hq_types2| | |];
        try solve [apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ a_ (e_typ ?e ?T) ⦄ || ⦃ ?A ⦄ ] =>
        apply hq_conseq with (A4:=a_ (e_typ e T))(A5:=a_ (e_typ e T))(A6:=A);
        [apply hq_types2| | |];
        try solve [apply entails_refl]
    end.

  Ltac by_assumption :=
    match goal with
    |[|- _ ⊢ ?A ∧ _ ⊆ _ ] =>
       intros_entails; repeat asrt_sat_auto_destruct_conj; auto with assert_db
    end.

  Ltac has_spec S :=
    match S with
    | S2 => apply lspec_and1, lspec_base
    | S3 => apply lspec_and2, lspec_base
    end.

  Ltac by_call_ext_adapt_strong_using S :=
    try (eapply hq_conseq; [apply hq_call_ext_adapt_strong;
                           has_spec S| | | ];
         simpl;
         try solve [auto with assert_db; by_assumption]).

  Ltac conseq_pre A :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A4:=A);
        [
        |
        |apply entails_refl
        |apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen with (P1:=A)
    end.

  Ltac econseq_pre :=
    match goal with
      | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |
        |apply entails_refl
        |apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄] =>
        eapply h_strengthen
    end.

  Ltac conseq_post A :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A5:=A);
        [
        |apply entails_refl
        |
        |apply entails_refl]
    end.

  Ltac econseq_post :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |apply entails_refl
        |
        |apply entails_refl]
    end.

  Ltac conseq_inv A :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A6:=A);
        [
        |apply entails_refl
        |apply entails_refl
        |]
    end.

  Ltac econseq_inv :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |apply entails_refl
        |apply entails_refl
        |]
    end.

  Ltac hq_conj_assoc_left_rewrite :=
    match goal with
    | [ |- _ ⊢ ⦃ ?A1 ∧ (?A2 ∧ ?A3) ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc2_pre
    end.

  Ltac hq_conj_assoc_right_rewrite :=
    match goal with
    | [ |- _ ⊢ ⦃ (?A1 ∧ ?A2) ∧ ?A3 ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc1_pre
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ (_ ∧ _) ∧ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc2_post
    end.

  Ltac drop_right_of_conj :=
    repeat hq_conj_assoc_left_rewrite;
    econseq_pre;
    [|apply conj_entails_left];
    repeat hq_conj_assoc_right_rewrite.

  Lemma hoare_triple_post_true :
    forall M A s, M ⊢ ⦃ A ⦄ s ⦃ a_true ⦄.
  Proof.
    intros;
      apply h_embed_UL, UL_post_true.
  Qed.

  Lemma hoare_quad_post_true :
    forall M A1 A2 s, M ⊢ ⦃ A1 ⦄ s ⦃ a_true ⦄ || ⦃ A2 ⦄.
  Proof.
    intros; apply hq_mid, hoare_triple_post_true.
  Qed.

  Ltac hoare_post_true :=
    try solve [apply UL_post_true];
    try solve [apply hoare_triple_post_true];
    try solve [apply hoare_quad_post_true].

  Ltac apply_hq_sequ_preserving_left_of_pre :=
    repeat hq_conj_assoc_left_rewrite;
    match goal with
    | [ H : typeOf_f ?M ?C ?f = Some ?T  |- ?M ⊢ ⦃ ?A ⦄ (s_read ?x (e_fld _ ?f)) ;; _ ⦃ _ ⦄ || ⦃ _ ⦄] => apply hq_sequ with (A2:=(a_ (e_typ (e_ x) T)) ∧ A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ ] => apply h_seq with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    end;
    repeat hq_conj_assoc_right_rewrite.

  Definition rewrite_hq_conj_simpl1 M A :=
    rewrite_hoare_quad1 M (simplify_conj A) A
      (simplify_conj_entails1 M A).

  Definition rewrite_hq_conj_simpl2 M A :=
    rewrite_hoare_quad2 M (simplify_conj A) A
      (simplify_conj_entails2 M A).

  Ltac simpl_conj_hq :=
    repeat apply hq_conj_assoc1_pre;
    repeat apply hq_conj_assoc2_post;
    apply rewrite_hq_conj_simpl1;
    apply rewrite_hq_conj_simpl2.

  Ltac extract_classDef :=
    match goal with
    |[def : classDef |- _ ] =>
       match goal with
       |[H : ⟦ _ ↦ def ⟧_∈ _ |- _] =>
          unfold update, t_update in H;
          simpl in H;
          inversion H;
          subst;
          clear H
       end
    end.

  Ltac setup_class :=
    simpl;
    intros;
    extract_classDef.

  Ltac setup_methods :=
  match goal with
  | [m : mth, mDef : methDef |- _] =>
      match goal with
      | [H : (m = _ ) /\ (mDef = _) \/ _ |- _ ] =>
          destruct H as [l |];
          [destruct l; subst|try setup_methods]
      | [H : (m = _ ) /\ (mDef = _) |- _ ] =>
          destruct H; subst
      end
  end.

  Ltac fetch_methods :=
    match goal with
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths ShopDef |- _ ] =>
        apply destruct_shopMths in H
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths AccountDef |- _ ] =>
        apply destruct_accountMths in H
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths KeyDef |- _ ] =>
        idtac
    end.

  Definition class_satisfies_invariant (M : module) C S : Prop :=
    match S with
    | S_inv Quantifications A => forall CDef m mDef,
        ⟦ C ↦ CDef ⟧_∈ snd M ->
        ⟦ m ↦ mDef ⟧_∈ c_meths CDef ->
        vis mDef = public ->
        Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                              (this, t_cls C) ::
                              params mDef) ∧
                      a_typs (Quantifications)) ∧
                     A ∧ adapt A (this :: map fst (params mDef))) ⦄
          body mDef
          ⦃ A ∧ adapt A (result :: nil) ⦄
        || ⦃ A ⦄
    | _ => False
    end.

End ChainmailLemmas.
