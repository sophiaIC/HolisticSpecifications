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
Require Import assumptions.
Require Import shop.
Require Import shop_lemmas.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

(** *
    Chainmail proof for the Shop example - Appendix H in the related paper.
 *)

Module ShopProof.

  Import LanguageDefinition.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.
  Import SpecSatisfaction.
  Import ChainmailLemmas.
  Import Assumptions.
  Import Shop.
  Import ShopLemmas.

  Open Scope hoare_scope.

  Lemma Shop_sat_I2 :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths ShopDef ->
                   vis mDef = public ->
                   Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                                         (this, t_cls Shop) ::
                                         params mDef) ∧
                                 a_typs ((a, t_cls Account) :: nil)) ∧
                                a_prt ((e_ a) ∙ key)) ∧
                               adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
                     body mDef
                     ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
                   || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    setup_shop.
    intros.
    (* Shop *)
    apply destruct_shopMths in H;
      destruct H.
    * (* buy *)
      destruct H;
        subst.
      simpl.
      unfold buyBody.

      simpl_types.
      simpl_conj_hq.
      unfold simplify_conj;
        simpl.
      eapply hq_conseq with (A4:=a_ e_typ (e_ result) t_bool
                                 ∧ (a_ e_typ (e_ this) (t_cls Shop)
                                    ∧ (a_ e_typ (e_ buyer) t_ext
                                       ∧ (a_ e_typ (e_ item) (t_cls Item)
                                          ∧ (a_ e_typ (e_ a) (t_cls Account)
                                             ∧ (a_prt ((e_ a) ∙ key)
                                                ∧ (a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))));
        [| |apply entails_refl|apply entails_refl];
        try solve [solve_entails].
      repeat try apply_hq_sequ_with_mid_eq_fst;
        repeat split_post_condition_by_conjunction;
        try solve [by_hq_types2; by_assumption];

        try solve [apply hq_mid;
                   eapply h_strengthen;
                   [apply h_read_type|];
                   solve_entails;
                   eapply apply_entails;
                   [apply entails_fld_type; eauto|eauto]];

        (* <a.key> <-\- x is preserved by var assgn that is unrelated to the preservation *)
        try solve [by_prt_frm_preserved_by_unrelated_var_assgn].

      ** (* itemPrice = item.price *)

        unrelated_var_assgn_preserves_prt itemPrice (e_fld (e_ item) price).

      **
        unrelated_var_assgn_preserves_prt thisAcc (e_fld (e_ this) acc).

      ** (* oldBalance = thisAcc.balance *)
        unrelated_var_assgn_preserves_prt
          oldBalance
            (e_fld (e_ thisAcc) balance).

      ** (* tmp = buyer.pay(thisAcc, itemPrice) *)
        apply buyCallPreserves_akey_prot.

      **
        by_call_ext_adapt_strong_using S2;
          unfold prt_frms, asrt_frm_list; simpl;
          [|solve_entails].
        simpl_types.
        solve_entails.

        eapply apply_entails;
          [apply entails_extl|]; auto.

        eapply apply_entails;
          [apply entails_prt_intl|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_intl; unfold update, t_update, Mgood; simpl; eexists|eauto].
        crush.

        eapply apply_entails;
          [apply entails_prt_int|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_fld_type|eauto].
        unfold typeOf_f, Mgood;
          simpl.
        eexists; eauto.

      **
        apply hq_if.

        *** (* internal call to this.send *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
              eapply hq_conseq with (A6:=A3);
              [| | |apply entails_refl]
          end;
          [eapply hq_call_int with
            (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                   a_prt ((e_ a) ∙ key))
            (A2:=a_prt ((e_ a) ∙ key))
            (A3:=a_prt ((e_ a) ∙ key))
            (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
          | |];

          [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
           try solve [apply in_eq];
           try solve [simpl; eauto];
           simpl
          | | | | | ];

          try solve [simpl; eauto];

          try solve [simpl_types; solve_entails].

        *** (* external call to buyer.tell *)
          by_call_ext_adapt_strong_using S2;
            try solve [by_assumption].
          simpl_types.
          repeat apply entails_conj_split;
            try solve [by_assumption].

          by_assumption; eapply apply_entails; [apply entails_extl|auto].

      **
        apply hq_if.

        *** (* internal call to this.send *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
              eapply hq_conseq with (A6:=A3);
              [| | |apply entails_refl]
          end;
          [eapply hq_call_int with
            (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                   a_prt_frm ((e_ a) ∙ key) (e_ buyer))
            (A2:=a_prt_frm ((e_ a) ∙ key) (e_ buyer))
            (A3:=a_prt ((e_ a) ∙ key))
            (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
          | |];

          [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
           try solve [apply in_cons, in_eq];
           try solve [auto];
           try solve [simpl; eauto]
          | | | | | ];

          try solve [simpl; eauto];
          try solve [simpl_types; solve_entails].

        *** (* external call to buyer.tell *)
          by_call_ext_adapt_strong_using S2;
            try solve [by_assumption];
            simpl.
          simpl_types.
          repeat apply entails_conj_split;
            try solve [by_assumption].
          by_assumption; eapply apply_entails; [apply entails_extl|auto].
          unfold prt_frms, asrt_frm_list; simpl.
          try solve [solve_entails].

      **
        unrelated_var_assgn_preserves_prt result e_false.

      **
        return_false_protects_key.

    * (* send method: private method not considered *)
      destruct H;
        subst.
      simpl_types.
      crush.
  Qed.

  Ltac by_prt_frm_bool :=
    match goal with
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ a_prt_frm (?o ∙ key) ?b ⦄ ] =>
        match goal with
        | |- context [e_typ b t_bool] =>
            conseq_post ((a_ (e_typ (o ∙ key) (t_cls Key))) ∧ (a_ (e_typ b t_bool)));
            [|solve [apply entails_prt_bool]];
            repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption];
            conseq_post (a_ (e_typ o (t_cls Account)));
            [|apply keyHasTypeKey];
            by_hq_types2; by_assumption
        end
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ a_prt_frm (?o ∙ key) ?b ⦄ || ⦃ _ ⦄ ] =>
        match goal with
        | |- context [e_typ b t_bool] =>
            conseq_post ((a_ (e_typ (o ∙ key) (t_cls Key))) ∧ (a_ (e_typ b t_bool)));
            [|solve [apply entails_prt_bool]];
            repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption];
            conseq_post (a_ (e_typ o (t_cls Account)));
            [|apply keyHasTypeKey];
            by_hq_types2; by_assumption
        end
    end.

  Lemma Account_sat_I2 :
    forall m mDef,
      ⟦ m ↦ mDef ⟧_∈ c_meths AccountDef ->
      vis mDef = public ->
      Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                            (this, t_cls Account) ::
                            params mDef) ∧
                    a_typs ((a, t_cls Account) :: nil)) ∧
                   a_prt ((e_ a) ∙ key)) ∧
                  adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
        body mDef
        ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
      || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    intros.
    setup_shop.

    simpl_types.
    apply destruct_accountMths in H;
      repeat destruct H;
      subst;
      simpl;
      simpl_types;
      simpl_conj_hq.

    *
      (* Account::transfer *)
      unfold simplify_conj;
        simpl.
      unfold transferBody.
      repeat split_post_condition_by_conjunction.

      **
        conseq_pre (a_prt ((e_ a) ∙ key));

          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     eauto;
                     try solve [apply sat_true]].
        apply_hq_sequ_with_mid_eq_fst.

        ***
          apply hq_mid.
          by_h_prot1_normal.

          apply h_if.

          ****
            eapply h_strengthen;
              [|apply conj_entails_left].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [
                  apply h_embed_UL;
                  apply hoare_UL_write_different_field;
                  unfold key, balance;
                  crush].

          ****
            match goal with
            | [|- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ⦃ _ ⦄] =>
                apply h_strengthen
                with (P1:=[e_false /s result] A);
                [|try solve [intros_entails;
                             repeat asrt_sat_auto_destruct_conj;
                             auto]]
            end.
            apply h_embed_UL.
            apply hoare_ul_assgn.


        ***
          apply hq_mid.

          match goal with
          | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
              apply h_strengthen
              with (P1:=[e_false /s result] A);
              [|try solve [intros_entails;
                           repeat asrt_sat_auto_destruct_conj;
                           auto]]
          end.
          apply h_embed_UL.
          apply hoare_ul_assgn.

      **
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.

        apply_hq_sequ_with_mid_eq_fst.

        ***
          repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption].

        ***
          by_prt_frm_bool.

    * (* setKey *)
      unfold simplify_conj;
        simpl.
      unfold setKeyBody.

      apply hq_if.

      ** (* true branch, i.e. this.key == null: this.key = k *)
        drop_right_of_conj.
        drop_right_of_conj.
        match goal with
        | [ |- _ ⊢ ⦃ ?A ∧ ?A1 ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
            apply hq_sequ with (A2:=A1)
        end;
        [|return_false_protects_key].
        repeat split_post_condition_by_conjunction;
          try solve [by_hq_types2; by_assumption].

        apply hq_mid.
        eapply h_strengthen with
          (P1:=(a_ (e_eq (e_fld (e_ this) key) e_null)) ∧
                 (a_prt (e_fld (e_ a) key)));
          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     auto].

        apply split_excluded_middle_hoare with
          (A:=a_ e_eq (e_ a) (e_ this)).
        apply h_or.

        *** (* a == this *)
          apply h_strengthen with (P1:=a_false);
            [apply hoare_false|].
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [eapply entails_prt_null|].
        eapply apply_entails;
          [eapply entails_prt_eq|].
        asrt_sat_auto_destruct_conj; [|eassumption].
        eapply apply_entails;
          [eapply entails_eq_trans|].
        asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply entails_eq_fld|auto].

        *** (* a <> this  *)
          eapply h_strengthen with
            (P1:=(e_ a) ≠ (e_ this) ∧ (a_prt ((e_ a) ∙ key)));
            try solve [solve_entails].
        apply h_prot1;
          try solve [crush].
        intros.
        apply h_embed_UL.
        apply hoare_UL_write_different_object.

      **
      (* false branch, i.e. this.key != null: return false *)
      return_false_protects_key.
  Qed.

  Lemma Key_sat_I2 :
    forall m mDef,
      ⟦ m ↦ mDef ⟧_∈ c_meths KeyDef ->
      vis mDef = public ->
      Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                            (this, t_cls Key) ::
                            params mDef) ∧
                    a_typs ((a, t_cls Account) :: nil)) ∧
                   a_prt ((e_ a) ∙ key)) ∧
                  adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
        body mDef
        ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
      || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    intros;
      setup_shop.
    unfold KeyDef in *; simpl in *.
    match goal with
    | [ H : ⟦ _ ↦ _ ⟧_∈ (∅) |-_] =>
        inversion H
    end.
  Qed.

  Lemma I2 :
    spec_sat Mgood S2.
  Proof.
    setup_shop.
    apply spec_invariant.
    intros.
    apply destruct_Mgood in H;
      destruct H.

    *
      (* Shop *)
      destruct H; subst.
      eapply Shop_sat_I2;
        eauto.

    *
      (* Account \/ Key*)
      destruct H;
        destruct H;
        subst;
        simpl.

      **
        (* Account *)
        eapply Account_sat_I2;
          eauto.

      **
        (* Key *)
        eapply Key_sat_I2;
          eauto.
  Qed.

  Ltac split_post_condition_by_conjunction_and_solve :=
    repeat split_post_condition_by_conjunction;
    try solve [by_hq_types2; by_assumption];
    try solve [apply hq_mid;
               eapply h_strengthen;
               [apply h_read_type|];
               solve_entails;
               eapply apply_entails;
               [apply entails_fld_type; eauto|eauto]];
    try solve [by_prt_frm_preserved_by_unrelated_var_assgn].

  Ltac by_hoare_ul_assgn :=
    match goal with
    | [|- ?M ⊢ ⦃ ?A ⦄ s_read ?x ?e ⦃ ?A ⦄ ] =>
        assert (Hrewrite: A = [e /s x] A);
        [|assert ( M ⊢ ⦃ [e /s x] A ⦄ s_read x e ⦃ A ⦄);
          [auto|simpl; auto]];
        [|apply h_embed_UL, hoare_ul_assgn]
    | [|- _ ] => apply hq_mid; by_hoare_ul_assgn
    end.

  Ltac S3_by_unrelated_var_assgn_prt_and_lt x y f:=
    split_post_condition_by_conjunction_and_solve;
    [(* prt *)
      unrelated_var_assgn_preserves_prt x (e_fld (e_ y) f)
    |(* b <= a.balance *)
      drop_right_of_conj;
      repeat hq_conj_assoc_left_rewrite;
      econseq_pre;
      [
      |apply conj_entails_right]; (*;
      apply hq_mid, h_embed_UL;*)
      by_hoare_ul_assgn
    ];
    auto.

  Lemma buyCallPreserves_akey_prot_and_balance:
    Mgood
      ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int
          ∧ (a_ e_typ (e_ thisAcc) (t_cls Account)
             ∧ (a_ e_typ (e_ itemPrice) t_int
                ∧ (a_ e_typ (e_ result) t_bool
                   ∧ (a_ e_typ (e_ this) (t_cls Shop)
                      ∧ (a_ e_typ (e_ buyer) t_ext
                         ∧ (a_ e_typ (e_ item) (t_cls Item)
                            ∧ (a_ e_typ (e_ a) (t_cls Account) ∧
                                 (a_ e_typ (e_ b) t_int ∧
                                    (a_prt ((e_ a) ∙ key) ∧ (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧ a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))))))) ⦄
      s_call tmp buyer pay (thisAcc :: itemPrice :: nil)
      ⦃ a_prt ((e_ a) ∙ key) ∧ (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)) ⦄
    || ⦃ a_prt ((e_ a) ∙ key) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)⦄.
  Proof.

    (* tmp = buyer.pay(thisAcc, itemPrice) *)
    by_call_ext_adapt_strong_using S3;
      simpl_types;
      repeat apply entails_conj_split;
      try solve [by_assumption].

    *
      by_assumption;
        eapply apply_entails;
        [apply entails_extl|auto].

    *
      by_assumption;
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

    * (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

  Qed.

  Lemma Shop_sat_I3 :
    class_satisfies_invariant Mgood Shop S3.
  Proof.
    setup_shop.
    setup_class.
    (* Shop *)
    fetch_methods.
    setup_methods.
    * (* buy *)
      simpl.
      unfold buyBody.

      simpl_types.
      simpl_conj_hq.
      unfold simplify_conj;
        simpl.
      eapply hq_conseq with (A4:=a_ e_typ (e_ result) t_bool
                                 ∧ (a_ e_typ (e_ this) (t_cls Shop)
                                    ∧ (a_ e_typ (e_ buyer) t_ext
                                       ∧ (a_ e_typ (e_ item) (t_cls Item)
                                          ∧ (a_ e_typ (e_ a) (t_cls Account)
                                             ∧ (a_ e_typ (e_ b) t_int
                                                ∧ (a_prt ((e_ a) ∙ key) ∧
                                                     (a_ e_lt (e_ b) ((e_ a) ∙ balance)
                                                      ∧ (a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))))));
        [| |apply entails_refl|apply entails_refl];
        try solve [solve_entails].

      (* Itemprice = item.price *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt itemPrice item price
        |].

      (* thisAcc = this.acc *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt thisAcc this acc
        |].

      (* oldBalance = thisAcc.balance *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt oldBalance thisAcc balance
        |].

      (* tmp = buyer.pay(thisAcc, itemPrice) *)
      apply_hq_sequ_with_mid_eq_fst;
        [split_post_condition_by_conjunction_and_solve;
         try solve [econseq_post;
                    [apply buyCallPreserves_akey_prot_and_balance
                     |by_assumption]]
        |].

      **
        (* prt_frm a.key buyer is preserved across external pay call  *)
        by_call_ext_adapt_strong_using S3;
          unfold prt_frms, asrt_frm_list; simpl;
          [|solve_entails].
        simpl_types.
        solve_entails.

        eapply apply_entails;
          [apply entails_extl|auto].

        eapply apply_entails;
          [apply entails_prt_intl|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_intl; unfold update, t_update, Mgood; simpl; eexists|eauto].
        crush.

        eapply apply_entails;
          [apply entails_prt_int|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_fld_type|eauto].
        unfold typeOf_f, Mgood;
          simpl.
        eexists; eauto.

        **
          apply_hq_sequ_preserving_left_of_pre.

          ***
            repeat split_post_condition_by_conjunction;
              try solve [by_hq_types2; by_assumption].

            **** (* prt a.key *)

              apply hq_if.

              ***** (* internal call to this.send *)
                econseq_inv;
                  [|apply conj_entails_left].
              match goal with
              | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
                  eapply hq_conseq with (A6:=A3);
                  [| | |apply entails_refl]
              end;
              [eapply hq_call_int with
                (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                       a_prt ((e_ a) ∙ key))
                (A2:=a_prt ((e_ a) ∙ key))
                (A3:=a_prt ((e_ a) ∙ key))
                (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
              | |];

              [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
               try solve [apply in_eq];
               try solve [simpl; eauto];
               simpl
              | | | | | ];

              try solve [simpl; eauto];

              try solve [simpl_types; solve_entails].

              ***** (* external call to buyer.tell *)
                by_call_ext_adapt_strong_using S3;
                  try solve [by_assumption];
                  simpl.
              simpl_types.
              repeat apply entails_conj_split;
                try solve [by_assumption].
              by_assumption; eapply apply_entails; [apply entails_extl|auto].

            **** (* b < a.balance *)

              apply hq_if.

              *****(* internal call to this.send *)
                match goal with
                | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
                    eapply hq_conseq with (A6:=A3);
                    [| | |apply entails_refl]
                end;
              [eapply hq_call_int with
                (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                       (a_ e_typ (e_ b) t_int ∧
                          (a_prt ((e_ a) ∙ key) ∧
                             (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))))
                (A2:=a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))
                (A3:=a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))
                (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
              | |];

              [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
               try solve [simpl; auto];
               simpl
              | | | | | ];

              try solve [simpl; eauto];

              try solve [simpl_types; solve_entails].

              ***** (* external call to buyer.tell *)
                by_call_ext_adapt_strong_using S3;
                  try solve [by_assumption];
                  simpl.
              simpl_types.
              repeat apply entails_conj_split;
                try solve [by_assumption].
              by_assumption; eapply apply_entails; [apply entails_extl|auto].

          ***
            repeat split_post_condition_by_conjunction;
              try solve [return_false_protects_key];
              try solve [by_UL_hoare_unrelated_var_assgn result (e_false)].

    * (* send *)
      crush. (* send is not a public method *)
  Qed.

  Lemma Account_sat_I3 :
    class_satisfies_invariant Mgood Account S3.
  Proof.
    setup_shop.
    setup_class.
    fetch_methods.
    setup_methods.

    *
      (* Account::transfer *)
      simpl.
      unfold transferBody.
      simpl_types.
      conseq_post
        (a_prt ((e_ a) ∙ key) ∧
           (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧
              a_prt_frm ((e_ a) ∙ key) (e_ result)));
        try solve [unfold prt_frms, asrt_frm_list;
                   simpl;
                   intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto with assert_db].
      repeat split_post_condition_by_conjunction.

      **
        conseq_pre (a_prt ((e_ a) ∙ key));

          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     eauto;
                     try solve [apply sat_true]].
        apply_hq_sequ_with_mid_eq_fst.

        ***
          apply hq_mid.
          by_h_prot1_normal.

          apply h_if.

          ****
            eapply h_strengthen;
              [|apply conj_entails_left].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [
                  apply h_embed_UL;
                  apply hoare_UL_write_different_field;
                  unfold key, balance;
                  crush].

          ****
            match goal with
            | [|- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ⦃ _ ⦄] =>
                apply h_strengthen
                with (P1:=[e_false /s result] A);
                [|try solve [intros_entails;
                             repeat asrt_sat_auto_destruct_conj;
                             auto]]
            end.
            apply h_embed_UL.
            apply hoare_ul_assgn.


        ***
          apply hq_mid.

          match goal with
          | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
              apply h_strengthen
              with (P1:=[e_false /s result] A);
              [|try solve [intros_entails;
                           repeat asrt_sat_auto_destruct_conj;
                           auto]]
          end.
          apply h_embed_UL.
          apply hoare_ul_assgn.

      **
        unfold prt_frms, asrt_frm_list;
          simpl.

        apply hq_sequ
          with (A2:=a_ e_typ (e_ result) t_bool ∧ a_ e_typ (e_ a) (t_cls Account) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)).

        ***
          repeat split_post_condition_by_conjunction_and_solve.
          apply hq_if.

          ****
            apply hq_mid.
            apply split_excluded_middle_hoare
              with (A:=a_ ((e_ a) ⩵ (e_ this))).
            apply h_or.

            ***** (* a == this *)
              apply h_strengthen with (P1:=a_false);
                [apply hoare_false|].
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.
            apply apply_entails with (A1:=a_prt_frm ((e_ a) ∙ key) (e_ k) ∧ ¬ (a_prt_frm ((e_ a) ∙ key) (e_ k)));
              [eapply neg_absurd|].
            asrt_sat_auto_destruct_conj.

            eapply apply_entails;
              [apply entails_eq_not_prt_frm|].

            eapply apply_entails;
              [eapply entails_eq_trans|].

            asrt_sat_auto_destruct_conj;
              eauto.

            eapply apply_entails;
              [apply entails_eq_fld|].

            auto.

            *****
              econseq_pre.
            eapply h_seq with (A2:=a_ e_lt (e_ b) ((e_ a) ∙ balance)).
            apply hoare_ul_write_to_different_object_lt.
            apply h_embed_UL.
            apply hoare_UL_addition_lt.
            intros_entails.
            repeat asrt_sat_auto_destruct_conj.

          ****
            econseq_pre.
            apply hq_mid, h_embed_UL.
            apply hoare_ul_return_bool_preserves_fld_lt.
            intros_entails.
            repeat asrt_sat_auto_destruct_conj.

        ***
          econseq_pre.
          apply hq_mid, h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_lt.
          intros_entails.
          repeat asrt_sat_auto_destruct_conj.

      **
        simpl_types.
        repeat hq_conj_assoc_right_rewrite.
        unfold prt_frms, asrt_frm_list;
          simpl.
        econseq_pre;
          [|apply conj_entails_right].
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.

        repeat split_post_condition_by_conjunction_and_solve;
          try solve [hoare_post_true].

        apply_hq_sequ_with_mid_eq_fst.

        repeat split_post_condition_by_conjunction_and_solve.

        ***
          hoare_post_true.

        ***
          repeat hq_conj_assoc_left_rewrite.
          apply hq_mid.
          apply h_prot1;
            try solve[simpl; auto];
            intros.

          apply h_if.

          ****
            apply h_strengthen with (P1:=a_ (((e_ a) ∙ key) ⩵ (e_ z)));
              try solve [intros_entails;
                         repeat asrt_sat_auto_destruct_conj;
                         auto].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [apply h_embed_UL;
                         apply hoare_UL_write_different_field;
                         intro Hcontra; inversion Hcontra].

          ****
            eapply h_strengthen.
            apply h_embed_UL.
            apply hoare_ul_return_bool_preserves_fld_eq.
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.

        ***
          by_prt_frm_bool.

    * (* setKey *)
      simpl_types.
      conseq_post
        (a_prt ((e_ a) ∙ key) ∧
           (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧
              a_prt_frm ((e_ a) ∙ key) (e_ result)));
        try solve [unfold prt_frms, asrt_frm_list;
                   simpl;
                   intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto with assert_db].
      unfold setKeyBody.

      apply hq_if.

      ** (* true branch, i.e. this.key == null: this.key = k *)

        drop_right_of_conj.
        drop_right_of_conj.

        repeat split_post_condition_by_conjunction;
          try solve [by_prt_frm_bool].

        apply hq_mid.
        eapply h_strengthen with
          (P1:=(a_ e_typ (e_ result) t_bool) ∧ (a_ (e_eq (e_fld (e_ this) key) e_null)) ∧
                 (a_prt (e_fld (e_ a) key)));
          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     auto].

        apply split_excluded_middle_hoare with
          (A:=a_ e_eq (e_ a) (e_ this)).
        apply h_or.

        *** (* a == this *)
          apply h_strengthen with (P1:=a_false);
            [apply hoare_false|].
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [eapply entails_prt_null|].
        eapply apply_entails;
          [eapply entails_prt_eq|].
        asrt_sat_auto_destruct_conj; [|eassumption].
        eapply apply_entails;
          [eapply entails_eq_trans|].
        asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply entails_eq_fld|auto].

        *** (* a <> this  *)
          eapply h_strengthen with
            (P1:= (a_ e_typ (e_ result) t_bool) ∧ (e_ a) ≠ (e_ this) ∧ (a_prt ((e_ a) ∙ key)));
            try solve [solve_entails].
        apply h_prot1;
          try solve [crush].
        intros.
        apply h_seq with (A2:=(a_ e_typ (e_ result) t_bool) ∧ a_ (((e_ a) ∙ key) ⩵ (e_ z))).

          ****
          match goal with
          | [ |- _ ⊢ ⦃ ?A1 ⦄ _ ⦃ ?A2 ∧ ?A3 ⦄] =>
              conseq_pre (A1 ∧ A1)
          end;
          [|intros_entails; repeat asrt_sat_auto_destruct_conj].
          apply h_and.

          *****
            econseq_pre.
          apply h_types1.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj;
            auto.

          *****
            econseq_pre.
          apply h_embed_UL.
          apply hoare_UL_write_different_object.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj.

        ****
          apply h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_eq.

        *** (* this.key == null -> contradiction on prt null *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ || ⦃ _ ⦄] =>
              apply hq_sequ with (A2:=(a_ e_typ (e_ result) t_bool) ∧ A)
          end.
          split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption].
          econseq_pre.
          apply hq_mid, h_embed_UL.
          apply hoare_UL_write_different_field_lt.
          intro Hcontra; inversion Hcontra.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj;
            auto.

          apply hq_mid, h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_lt.

      **
      (* false branch, i.e. this.key != null: return false *)
        repeat split_post_condition_by_conjunction;
          try solve [return_false_protects_key].
        econseq_pre.
        apply hq_mid, h_embed_UL.
        apply hoare_ul_return_bool_preserves_fld_lt.
        intros_entails.
        repeat asrt_sat_auto_destruct_conj.

  Qed.

  Lemma Key_sat_I3 :
    class_satisfies_invariant Mgood Key S3.
  Proof.
    setup_class.
    unfold KeyDef in *; simpl in *.
    match goal with
    | [ H : ⟦ _ ↦ _ ⟧_∈ (∅) |-_] =>
        inversion H
    end.
  Qed.

  Lemma I3 :
    spec_sat Mgood S3.
  Proof.
    setup_shop.
    apply spec_invariant.
    intros.
    apply destruct_Mgood in H;
      destruct H.

    *
      (* Shop *)
      destruct H; subst.
      eapply Shop_sat_I3;
        eauto; auto.

    *
      (* Account \/ Key*)
      destruct H;
        destruct H;
        subst;
        simpl.

      **
        (* Account *)
        eapply Account_sat_I3;
          eauto.
        auto.

      **
        (* Key *)
        eapply Key_sat_I3;
          eauto.
        auto.
  Qed.

End ShopProof.
