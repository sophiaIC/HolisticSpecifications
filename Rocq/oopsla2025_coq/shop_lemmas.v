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
Require Import chainmail_lemmas.
Require Import shop.
Require Import assumptions.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


(** * Shop Lemmas *)
(** * Suppporting lemmas for the main Shop Proof in shop_proof.v *)

Module ShopLemmas.

  Import LanguageDefinition.
  Import AssertTheory.
  Import SubstDefn.
  Import Hoare.
  Import SpecSatisfaction.
  Import ChainmailLemmas.
  Import Shop.
  Import Assumptions.

  Open Scope hoare_scope.

  Lemma return_false_prt_akey :
    Mgood
      ⊢ ⦃ (a_ e_typ (e_ result) t_bool
           ∧ (a_ e_typ (e_ a) (t_cls Account)
              ∧ a_prt ((e_ a) ∙ key))) ⦄
      ret e_false ⦃ a_prt ((e_ a) ∙ key) ∧
                      a_prt_frm (e_fld (e_ a) key) (e_ result) ⦄
    || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    split_post_condition_by_conjunction.

    *
      repeat hq_conj_assoc_left_rewrite.
      apply hq_mid.
      eapply h_prot1;
        simpl;
        auto;
        intros.

      match goal with
      | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄] =>
          apply h_strengthen
          with (P1:=[e_false /s result] A);
          [|try solve [intros_entails;
                       repeat asrt_sat_auto_destruct_conj;
                       auto]]
      end.
      apply h_embed_UL.
      apply hoare_ul_assgn.

    *
      match goal with
      | [|- ?M ⊢ ⦃ ?A1 ⦄ _ ⦃ a_prt_frm ?e ?x ⦄ || ⦃ ?A3 ⦄ ] =>
          eapply hq_conseq with
          (A4:=A1)
          (A5:=a_ (e_typ x t_bool) ∧ (a_ (e_typ e (t_cls Key))))
          (A6:=A3)
      end.

      **
        split_post_condition_by_conjunction.
        by_hq_types2;
          intros_entails;
          repeat asrt_sat_auto_destruct_conj;
          eauto.
        by_hq_types2;
          intros_entails;
          repeat asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply keyHasTypeKey|eauto].

      **
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.

      **
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [apply entails_prt_bool|asrt_sat_auto_destruct_conj; eauto].

      **
        apply entails_refl.
  Qed.

  Ltac return_false_protects_key :=
    eapply hq_conseq;
    [apply return_false_prt_akey| | | ];
    try solve [intros_entails;
               repeat asrt_sat_auto_destruct_conj;
               auto].

  Ltac solve_entails :=
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  Ltac unrelated_var_assgn_preserves_prt x e :=
          try (
              match goal with
              | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
                  apply hq_mid
              end);
          eapply h_strengthen;
          [apply h_prot1 with (A:=a_true);
           crush;
           match goal with
           | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄ ] =>
               apply h_strengthen with (P1:=A);
               [|]
           end;
           try solve [solve_entails];
           match goal with
           | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
               apply h_strengthen
               with (P1:=[e /s x] A);
               [|simpl; auto with assert_db]
           end;
           apply h_embed_UL;
           apply hoare_ul_assgn;
           intros_entails;
           repeat asrt_sat_auto_destruct_conj;
           auto with assert_db
          |try solve [solve_entails]].

  Ltac by_UL_hoare_unrelated_var_assgn x e :=
    try (
        match goal with
        | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
            apply hq_mid
        end);
    match goal with
    | [|- context [e_lt ?e1 ?e2] ] =>
        apply h_strengthen with (P1:=a_ e_lt e1 e2)
    end;
    try solve [solve_entails];
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen
        with (P1:=[e /s x] A);
        [|simpl; auto with assert_db]
    end;
    apply h_embed_UL;
    apply hoare_ul_assgn;
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  Lemma buyCallPreserves_akey_prot:
    Mgood
      ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int
          ∧ (a_ e_typ (e_ thisAcc) (t_cls Account)
             ∧ (a_ e_typ (e_ itemPrice) t_int
                ∧ (a_ e_typ (e_ result) t_bool
                   ∧ (a_ e_typ (e_ this) (t_cls Shop)
                      ∧ (a_ e_typ (e_ buyer) t_ext
                         ∧ (a_ e_typ (e_ item) (t_cls Item)
                            ∧ (a_ e_typ (e_ a) (t_cls Account)
                               ∧ (a_prt ((e_ a) ∙ key) ∧ a_prt_frm ((e_ a) ∙ key) (e_ buyer)))))))))
      ⦄ s_call tmp buyer pay (thisAcc :: itemPrice :: nil) ⦃ a_prt ((e_ a) ∙ key)
      ⦄ || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.

    (* tmp = buyer.pay(thisAcc, itemPrice) *)
    by_call_ext_adapt_strong_using S2.
    simpl_types;
    repeat apply entails_conj_split;
      try solve [by_assumption].

    ****
      by_assumption.
      eapply apply_entails;
        [apply entails_extl|].
      repeat asrt_sat_auto_destruct_conj;
        eauto with assert_db.

    ****
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_intl|].
      repeat asrt_sat_auto_destruct_conj;
        eauto with assert_db.
      eapply apply_entails;
        [eapply entails_intl|];
        eauto.
      unfold Mgood;
        simpl;
        auto.
      eexists; crush.

    **** (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

  Qed.

  Ltac by_h_prot1_normal :=
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄ ] =>
        apply h_strengthen with (P1:=a_true ∧ A);
        [|solve_entails]
    end;
    apply h_prot1 with (A:=a_true);
    crush;
    match goal with
    | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄ ] =>
        apply h_strengthen with (P1:=A);
        [|]
    end;
    try solve [solve_entails].

  Ltac by_UL_hoare_write_unrelated_field :=
    match goal with
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ || ⦃ _ ⦄ ] =>
        apply hq_mid;
        apply h_strengthen with (P1:=A);
        try solve [intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto]
    |[ |- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ ] =>
       apply h_strengthen with (P1:=A);
       try solve [intros_entails;
                  repeat asrt_sat_auto_destruct_conj;
                  auto]
    end;
    by_h_prot1_normal;

    apply h_embed_UL;
    apply hoare_UL_write_different_field;
    intro Hcontra; inversion Hcontra.

  Ltac by_prt_frm_preserved_by_unrelated_var_assigment y z f :=
    apply hq_mid;
    eapply h_strengthen;
    [apply h_prot2 with (x:=y); intros|];
    try solve [solve_entails];
    try solve [left; auto];
    try solve [right; eexists; auto];
    try (
        match goal with
        | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
            apply hq_mid
        end);
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen
        with (P1:=[(e_ z) ∙ f /s y] A);
        [|simpl; auto with assert_db]
    end;
    apply h_embed_UL;
    apply hoare_ul_assgn;
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  Ltac by_prt_frm_preserved_by_unrelated_var_assgn :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ s_read ?x (e_fld (e_ ?y) ?f) ⦃ _ ⦄ || ⦃ _ ⦄] =>
        by_prt_frm_preserved_by_unrelated_var_assigment x y f
    end.

End ShopLemmas.
