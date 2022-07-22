Require Import List.
Require Import String.
Open Scope string_scope.
Require Import L_def.
Require Import defs.
Require Import common.
Require Import exp.
Require Import necessity_tactics.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module SimpleBankAccount(L : LanguageDef).

  Export L.
  Module L_NecessityTactics := NecessityTactics(L).
  Import L_NecessityTactics.

  Open Scope assert_scope.
  Open Scope reduce_scope.

  (** #<h2># Password Class #</h2># *)

  Definition Password := classID 101.

  Definition PasswordDef := clazz Password
                                 boundary
                                 empty
                                 empty
                                 empty.

  (** #<h2>#Account Class#</h2># *)

  Definition Account := classID 100.

  Definition password := fieldID 101.

  Definition balance := fieldID 102.

  Definition transfer := methID 101.

  Parameter transferBody : block.

  Definition setPassword := methID 102.

  Parameter setPwdBody : block.

  Definition AccountDef := clazz Account
                                 boundary
                                 (⟦ balance ↦ (t_int) ⟧ ⟦ password ↦ (t_cls Password) ⟧ empty)
                                 (⟦ setPassword ↦ setPwdBody ⟧
                                    ⟦ transfer ↦ transferBody ⟧
                                    empty)
                                 empty.

  Definition destAcc := (n_ 101).

  Definition pwd := (n_ 102).

  Definition pwd' := (n_ 103).

  (** #<h2>#Bank Module#</h2># *)

  Definition BankMdl := (⟦ Account ↦ AccountDef ⟧
                           ⟦ Password  ↦ PasswordDef ⟧ empty).


  (*simple type extraction: the type of the password of any account is Password*)
  Axiom password_class_is_Password :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧ (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)))) ⊇
                   (a_class (e_ p) Password).

  Lemma BankMdlMethods :
    forall C CDef m, ⟦ C ↦ CDef ⟧_∈ BankMdl ->
                m ∈ c_meths CDef ->
                (C = Account /\ CDef = AccountDef /\ (m = transfer \/ m = setPassword)).
  Proof.
    intros.
    unfold BankMdl in *.

    destruct (eq_dec C Account) ;
      subst.

    * repeat right.
      repeat map_rewrite.
      inversion H;
        subst.
      unfold AccountDef in H0.
      simpl in H0.
      destruct (eq_dec m transfer);
        subst.

      ** repeat map_rewrite.

      ** destruct (eq_dec m setPassword);
           subst.

         *** repeat map_rewrite.

         *** repeat map_rewrite.
             destruct_exists_loo.
             inversion H0.

    *  repeat map_rewrite.
       destruct (eqb C Password);
         inversion H;
         subst.
       unfold PasswordDef in *;
         simpl in *.
       match goal with
       | [H : ?m ∈ empty |- _] =>
         let mDef := fresh "mDef" in
         let H' := fresh in
         destruct H as [mDef H'];
           inversion H'
       end.
  Qed.

  (** Type System Guarantees **)

  Parameter transferParameters :
    forall a β, BankMdl ⊢ ((a_class (e_ a) Account) ∧
                      ∃x.[(a♢ 0) calls (a_ a) ◌ transfer ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ a) ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                    ⟦ destAcc ↦ a♢ 2 ⟧
                                                                    empty⟩ ]]]).

  Parameter setPasswordParameters :
    forall a β, BankMdl ⊢ ((a_class (e_ a) Account) ∧
                      ∃x.[(a♢ 0) calls (a_ a) ◌ setPassword ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ a) ◌ setPassword ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                       ⟦ pwd' ↦ a♢ 2 ⟧empty⟩ ]]]).

  (** #<h2># Reduce Balance #</h2># *)

(*)  Parameter transferBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                    (¬ a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal))) ∧
                                    (a_class (e_ a) Account)}
                            m_call a transfer β
                            {post: ¬ a_exp ((e_acc_f (e_ b) balance) ⩻ (e_int bal))}.*)

  Parameter transferBalanceChangeSpecification :
    forall a a' a'' p p' bal β,
      BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                      (¬ a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal))) ∧
                      (a_class (e_ a') Account) ∧
                      (¬ ((a_exp ((e_acc_f (e_ a) password) ⩵ (e_val p))) ∧
                          (a_exp (e_ a' ⩵ e_ a))))}
              m_call a' transfer (⟦ pwd ↦ p'⟧ ⟦ destAcc ↦ a'' ⟧ β)
              {post: ¬ a_exp (e_acc_f (e_ a) balance ⩻ (e_int bal))}.

  Parameter setPasswordBalanceChangeSpecification :
    forall a a' β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                  (¬ a_exp ((e_acc_f (e_ a') balance) ⩻ (e_int bal))) ∧
                                  (a_class (e_ a) Account)}
                          m_call a setPassword β
                          {post: ¬ a_exp ((e_acc_f (e_ a') balance) ⩻ (e_int bal))}.

  Lemma setPasswordBalChange :
    forall a a' bal p p',
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (¬ a_exp ((e_acc_f (e_ a') balance) ⩻ (e_int bal))) ∧
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ setPassword ⟨ ⟦ pwd ↦ av_ p ⟧
                                                             ⟦ pwd' ↦ av_ p' ⟧ empty ⟩]))
              to1 (a_exp ((e_acc_f (e_ a') balance) ⩻ (e_int bal)))
              onlyIf (a_exp (e_false)).
  Proof.
    intros.
    eapply if1_classical with (β := ⟦ pwd ↦ p ⟧ ⟦ pwd' ↦ p' ⟧ empty);
      [|repeat compose_simpl; auto|].
    eapply hoare_consequence1.
    * apply setPasswordBalanceChangeSpecification.
    * specX_cnf_r.
      repeat spec_auto.
    * unfold no_free;
        intros;
        subst_simpl;
        auto.
  Qed.

  Lemma transferBalChange :
    forall a bal a' a'' p,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (¬ a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal))) ∧
                 (a_class (e_ a') Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a') ◌ transfer ⟨ ⟦ pwd ↦ av_ p ⟧
                                                           ⟦ destAcc ↦ av_ a'' ⟧
                                                           empty  ⟩]))
              to1 (a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                        ⟦ destAcc ↦ a♢ 2 ⟧
                                                                        empty  ⟩ ∧
                                     (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 1)))]]]).
  Proof.
    intros.

    specX_cnf_r.

    apply if1_ex1;
      intro o.
    subst_simpl.

    eapply if1_conseq3;
      [
      | apply if1_andI
          with (A':= (a_exp (e_acc_f (e_ a) password ⩵ e_val p)) ∧
                     (a_exp (e_ a' ⩵ e_ a)));
      [apply if1_start|]].

    * apply and_comm.
      commutativity.
      commutativity.
      commutativity.
      commutativity.
      commutativity.
      commutativity.
      substitute_equality (v_ a').
      there_exists_on_right a''.
      there_exists_on_right p.
      there_exists_on_right o.
      repeat spec_auto.

    * match goal with
      | [|- _ ⊢ (?A ∧ _ calls ?x ◌ ?m ⟨ ?β ⟩) to1 _ onlyIf _] =>
      eapply if1_conseq1
        with (A1:=A ∧ ∃x.[ a♢ 0 calls x ◌ m ⟨ β ⟩]);
        [repeat spec_auto
        |]
      end.

      ** repeat apply conseq_and2.
         apply conseq_ex2.
         exists o.
         subst_simpl.
         spec_auto.

      ** apply if1_classical with (β:=⟦ pwd ↦ p ⟧
                                        ⟦ destAcc ↦ a'' ⟧
                                        empty);
           [|repeat compose_simpl; auto|unfold no_free; intros; subst_simpl; auto].

(*      match goal with
      | [|- _ ⊢ {pre: _ } _ {post: ¬ a_exp (?e1 ⩻ ?e2)}] =>
        eapply hoare_consequence2 with (A2':=a_exp (e1 ⩵ e2))
      end.*)

      *** eapply hoare_consequence1.
          apply transferBalanceChangeSpecification.
          repeat spec_auto.
          repeat specX_cnf_r.
          repeat apply conseq_and2.
          repeat spec_auto.
          **** eapply conseq_trans; [|apply neg_distr_and_2];
                 apply or_l, conseq_refl.
          **** eapply conseq_trans; [|apply neg_distr_and_2];
                 spec_auto.

  Qed.

  Ltac BankMdlMethodsCases :=
    match goal with
    | [ Hclass : ⟦ ?C' ↦ ?CDef' ⟧_∈ BankMdl,
                 Hmeth : ?m' ∈ c_meths ?CDef' |- _ ] =>
      destruct (BankMdlMethods C' CDef' m' Hclass Hmeth);
      andDestruct;
      subst
    end.

  Lemma balanceChange :
    forall a bal,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (¬ (a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal)))))
              to1 (a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                         ⟦ destAcc ↦ a♢ 2 ⟧
                                                                         empty  ⟩ ∧
                                     (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 1)))]]]).
  Proof.
    intros.
    apply if1_internal;
      [| |repeat spec_auto].

    * intros.
      (* Case Analysis of all possible method calls to BankMdl objects *)
      BankMdlMethodsCases.
      disj_split;
        subst.

      (* transfer *)
      ** eapply if1_conseq1.

         *** apply conseq_and.

             **** apply conseq_and1, conseq_refl.

             **** eapply conseq_trans;
                    [ apply conseq_and
                        with (A1:=a_class (e_ α) Account);
                      [spec_auto
                      |repeat apply conseq_and2; apply conseq_refl]
                     |].
                  apply transferParameters.

         *** specX_cnf_r.
             apply if1_ex1;
               intro a'';
               subst_simpl.
             specX_cnf_r.
             apply if1_ex1;
               intro p;
               subst_simpl.
             apply transferBalChange.

      (* setPassword *)
      ** eapply if1_conseq1.

         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply setPasswordParameters.

         *** specX_cnf_r.
             apply if1_ex1;
               intro p1;
               subst_simpl.
             specX_cnf_r.
             apply if1_ex1;
               intro p2;
               subst_simpl.

             apply if1_conseq3
               with (A3:= a_false);
               [apply conseq_absurd
               |].
             apply setPasswordBalChange.

    (* encapsulation *)
    * eapply enc_conseq1;
        [apply not_lt_eq_gt_conseq2 |apply not_lt_eq_gt_conseq1|].
      apply enc_or.
      ** apply enc_eq; [apply enc_fld|apply enc_value].
         apply i_obj with (C:=Account).
         spec_auto.
         exists AccountDef.
         auto.

      ** apply enc_lt;
           [apply enc_value|apply enc_fld].
         apply i_obj with (C:=Account).
         spec_auto.
         exists AccountDef.
         auto.
  Qed.

  (* wrapped contains an existential, so the index (i.e. a♢ 1) is incremented *)
  Lemma balanceChange' :
    forall a bal,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (¬ a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal))))
              to (a_exp ((e_acc_f (e_ a) balance) ⩻ (e_int bal)))
              onlyThrough (∃x.[ ¬ wrapped (a♢ 1) ∧
                                (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 0)))]).
  Proof.
    intros.

    apply by_changes_and_conseq.

    * eapply conseq_trans;
        [
        |apply neg_distr_and_2].
      apply or_r.
      apply conseq_not_not2.

    * eapply if1_conseq2;
        [apply neg_distr_and_1|].
      apply if1_orI2.

      ** apply if1_conseq3 with (A3:=a_false);
           [apply conseq_absurd|].

         eapply if1_conseq1;
           [|apply change_class_absurd].
         spec_auto.

      ** eapply if1_conseq2;
           [apply conseq_not_not1|].
         eapply if1_conseq3;
           [|apply balanceChange].
         introduce_existential_on_left a'.
         introduce_existential_on_left p.
         introduce_existential_on_left o.
         there_exists_on_right p.
         repeat spec_auto.

         apply conseq_and1.
         apply param_not_wrapped with (x:=pwd).
         auto.

  Qed.

  (** #<h2># Change Password #</h2>#  *)

  Parameter transfer_PasswordChangeSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                (a_class (e_ a) Account)}
                        m_call a' transfer β
                        {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma transfer_PasswordChange :
    forall a a' a'' p p', BankMdl ⊢ (a_class (e_ a) Account ∧
                                (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                                (a_class (e_ a') Account) ∧
                                (∃x.[ (a♢ 0) calls (a_ a') ◌ transfer ⟨ ⟦ pwd ↦ av_ p' ⟧
                                                                          ⟦ destAcc ↦ av_ a'' ⟧ empty ⟩ ]))
                             to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                             onlyIf a_false.
  Proof.
    intros.

    apply if1_classical with (β:=⟦ pwd ↦ p' ⟧ ⟦ destAcc ↦ a'' ⟧ empty);
      [|repeat compose_simpl; auto|unfold no_free; intros; subst_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply transfer_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Parameter setPassword_PasswordChangeSpecification :
    forall a a' p p' β, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                                   (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                   (a_class (e_ a') Account) ∧
                                   (¬ (a_exp ((e_ a') ⩵ (e_ a)) ∧
                                       a_exp ((e_val p') ⩵ (e_ p))))}
                           m_call a' setPassword (⟦ pwd ↦ p' ⟧ β)
                           {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma setPassword_PasswordChange :
    forall a a' p p' p'', BankMdl ⊢ (a_class (e_ a) Account ∧
                                (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                                (a_class (e_ a') Account) ∧
                                (∃x.[ (a♢ 0) calls (a_ a') ◌ setPassword ⟨ ⟦ pwd ↦ av_ p' ⟧
                                                                             ⟦ pwd' ↦ av_ p'' ⟧ empty ⟩ ]))
                             to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                             onlyIf (a_exp ((e_ a') ⩵ (e_ a)) ∧
                                     a_exp ((e_val p') ⩵ (e_ p))).
  Proof.
    intros.

    apply if1_classical with (β:=⟦ pwd ↦ p' ⟧ ⟦ pwd' ↦ p'' ⟧ empty);
      [|repeat compose_simpl; auto|unfold no_free; intros; subst_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply setPassword_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Lemma passwordChange :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧
                      (a_exp (e_acc_f (e_ a) password ⩵ e_ p)))
                   to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                   onlyIf (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ setPassword ⟨ ⟦ pwd ↦ a_ p ⟧
                                                                           ⟦ pwd' ↦ a♢ 1 ⟧ empty  ⟩ ] ]).
  Proof.
    intros.
    apply if1_internal.

    * intros.
      BankMdlMethodsCases.
      disj_split;
        subst.

      (* transfer *)
      ** apply if1_conseq3
           with (A3:=a_false);
           [apply conseq_absurd|].
         eapply if1_conseq1;
           [|].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply transferParameters.

         *** do 2 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).
             apply transfer_PasswordChange.

      (*set password*)
      ** eapply if1_conseq1;
           [|].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply setPasswordParameters.

         *** do 2 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).
             eapply if1_conseq3;
               [|apply if1_andI;
                 [apply if1_start|apply setPassword_PasswordChange]].
             commutativity.
             introduce_existential_on_left x.
             there_exists_on_right y.
             there_exists_on_right x.
             specX_cnf_r.
             substitute_equality (v_ α).
             substitute_equality y0.
             spec_auto.

    (* encapsulation *)
    * eapply enc_conseq1;
        [apply conseq_not_not2
        |apply conseq_not_not1
        |apply enc_eq].

      ** apply enc_fld.
         apply i_obj with (C:=Account).
         spec_auto.
         exists AccountDef.
         auto.

      ** apply enc_value.

    *  eapply conseq_trans;
         [|apply conseq_not_not2].
       spec_auto.
  Qed.

  (** #<h2># Leak Password #</h2># *)
  (** TODO: add to paper: Sematic protection not syntactic protection **)

  Parameter passwordLeakChangePasswordSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                                (a_class (e_ a')  Account) ∧
                                (a_class (e_ a) Account)}
                        m_call a setPassword β
                        {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.


  Lemma changePasswordLeak :
    forall a a' p p1 p2, BankMdl ⊢ ((a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                               (a_class (e_ a') Account) ∧
                               (wrapped (a_ p)) ∧
                               (a_class (e_ a) Account) ∧
                               (∃x.[ (a♢ 0) calls (a_ a) ◌ setPassword ⟨ ⟦ pwd ↦ (av_ p1) ⟧
                                                                           ⟦ pwd' ↦ (av_ p2) ⟧ empty⟩]))
                            to1 ¬ wrapped (a_ p)
                            onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ pwd ↦ p1 ⟧ ⟦ pwd' ↦ p2 ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakChangePasswordSpecification with (a':=a')|].
      repeat spec_auto.

    * repeat compose_simpl;
        auto.
  Qed.

  Parameter passwordLeakTransferSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                (a_class (e_ a)  Account) ∧
                                (a_class (e_ a') Account) ∧
                                ¬ (a_false)}
                        m_call a' transfer β
                        {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.


  Lemma transferLeak :
    forall a a' p p' a'', BankMdl ⊢ ((a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                (a_class (e_ a) Account) ∧
                                (wrapped (a_ p)) ∧
                                (a_class (e_ a') Account) ∧
                                (∃x.[ (a♢ 0) calls (a_ a') ◌ transfer ⟨ ⟦ pwd ↦ (av_ p') ⟧
                                                                          ⟦ destAcc ↦ (av_ a'') ⟧
                                                                          empty⟩]))
                             to1 ¬ wrapped (a_ p)
                             onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ pwd ↦ p' ⟧ ⟦ destAcc ↦ a'' ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakTransferSpecification with (a:=a)|].
      repeat spec_auto.

    * repeat compose_simpl;
        auto.
  Qed.

  Lemma passwordLeak :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧
                      (a_exp (e_acc_f (e_ a) password ⩵ e_ p) ∧
                       (wrapped (a_ p))))
                   to1 (¬ (wrapped (a_ p)))
                   onlyIf (a_exp (e_false)).
  Proof.
    intros.
    apply if1_internal.

    * intros.
      (* Case Analysis of all possible method calls to BankMdl objects *)
      BankMdlMethodsCases.
      disj_split;
        subst.

      (* transfer *)
      ** eapply if1_conseq1;
           [
           |].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply transferParameters.

         *** do 2 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).

           eapply if1_conseq1;
               [|apply transferLeak with (p:=p)(a:=a)(a':=α)].
             repeat spec_auto.
             repeat apply conseq_and2.
             apply conseq_refl.

      (* changePassword *)
      ** eapply if1_conseq1;
           [|].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply setPasswordParameters.

         *** specX_cnf_r;
               apply if1_ex1;
               intros;
               subst_simpl.
             specX_cnf_r;
               apply if1_ex1;
               intros;
               subst_simpl.

             apply if1_conseq3
               with (A3:= a_false);
               [apply conseq_absurd
               |].
             eapply if1_conseq1;
               [
                  |apply changePasswordLeak with (a':=a)(a:=α)].
             repeat spec_auto.
             repeat apply conseq_and2;
               apply conseq_refl.

    (* encapsulation *)
    * eapply enc_conseq1;
        [apply conseq_not_not2
        |apply conseq_not_not1
        |].

      apply enc_conseq3 with (A1:=a_class (e_addr a) Account
                                  ∧ (a_exp (e_acc_f (e_addr a) password ⩵ (e_addr p))));
        [repeat spec_auto|].
      apply enc_conseq3 with (A1:=a_class (e_ p) Password);
        [apply password_class_is_Password|].
      apply enc_wrapped2.

    * eapply conseq_trans;
        [|apply conseq_not_not2].
      spec_auto.
  Qed.

  (** BankSpec **)

  Lemma necessityBankSpec :
    forall a bal p, BankMdl ⊢ (a_class (e_ a) Account ∧
                          (¬ a_exp (e_acc_f (e_ a) balance ⩻ (e_int bal))) ∧
                          (a_exp (e_acc_f (e_ a) password ⩵ (e_ p))))
                       to (a_exp (e_acc_f (e_ a) balance ⩻ (e_int bal)))
                       onlyIf ¬ wrapped (a_ p).
  Proof.
    intros.
    apply if_trans with (A':= ¬ wrapped (a_ p) ∨ ¬ (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)))).

    - apply ot_conseq3 with (A3:=∃x.[ ¬ wrapped (a♢ 1) ∧
                                      (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 0)))]). (*  *)
      + apply conseq_ex1;
          intros;
          subst_simpl.
        match goal with
        | [|- _ ⊢ ¬ wrapped (av_ ?v1) ∧ _ ⊇ ¬ wrapped (av_ ?v2) ∨ _ ] =>
          match goal with
          |[|- _ ⊢ ?A ⊇ _] =>
           apply conseq_trans with (A2:=A ∧ ((a_exp (e_val v1 ⩵ e_val v2)) ∨ ¬ (a_exp (e_val v1 ⩵ e_val v2))));
             [apply conseq_and;
              [apply conseq_refl
              |apply conseq_trans with (A2:=(a_true));
               [apply conseq_true
               |apply conseq_excluded_middle]]
             |]
          end
        end.
        apply and_comm.
        apply and_distr_trans1.
        apply or_lr.

        * apply or_l.
          repeat match goal with
                 | [|- context[wrapped (av_ ?v)]] =>
                   let Hrewrite := fresh in
                   assert (Hrewrite : wrapped (av_ v) = wrapped ([v /s 1] (a♢ 1)));
                     [subst_simpl; auto|rewrite Hrewrite; clear Hrewrite]
                 end.
          remember (a♢ 1) as a0.
          repeat extract_vals x 0.
          repeat extract_from_exp x.
          repeat extract_from_wrapped x.
          extract_from_asrt x.
          extract_from_asrt x.
          extract_from_asrt x.
          extract_from_asrt x.
          extract_from_asrt x.
          match goal with
          | [|- _ ⊢ [_ /s _] a_exp (_ ⩵ ?e') ∧ _ ⊇ _] =>
            subst e'
          end.
          apply subst_eq.
          subst; subst_simpl.
          apply conseq_and1, conseq_refl.

        * apply or_r.
          match goal with
          | [|- _ ⊢ ?Aa ∧ (_ ∧ ?Ab) ⊇ _] =>
            apply conseq_trans with (A2:=Aa ∧ Ab);
              [repeat spec_auto;
               apply conseq_and2;
               repeat spec_auto
              |]
          end.
          apply and_comm.
          apply conseq_exp_eq_neq.

      + eapply ot_conseq1;
          [apply conseq_and1, conseq_refl|].
        apply balanceChange'.

    - apply if_orI2.

      * (* Case A *)
        apply if_orE with (A':= wrapped (a_ p)).

        ** apply if_conseq3 with (A3:= a_true).
           *** match goal with
               | [|- _ ⊢ _ ⊇ ?Aa ∨ ?Ab] =>
                 apply conseq_trans with (A2:=Ab ∨ Aa);
                   [|apply conseq_or_comm]
               end.
               apply conseq_excluded_middle.
           *** match goal with
               | [|- _ ⊢ ?A1 to _ onlyIf ?A2 ] =>
                 apply if_conseq3 with (A3:=A1);
                   [|apply if_start]
               end.
               apply conseq_true.

        ** apply ot_conseq1 with (A1:=a_class (e_ a) Account ∧
                                      (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)) ∧
                                       wrapped (a_ p))).
           *** repeat spec_auto.

           *** apply by_changes_and_conseq.

               **** eapply conseq_trans;
                      [|apply neg_distr_and_2].
                    apply or_r.
                    eapply conseq_trans;
                      [|apply neg_distr_and_2].
                    spec_auto.

               **** eapply if1_conseq2;
                      [apply neg_distr_and_1|].
                    apply if1_orI2.

                    *****
                      eapply if1_conseq1; [|apply change_class_absurd]; spec_auto.
                    *****
                      eapply if1_conseq2; [apply neg_distr_and_1|].
                    apply if1_orI2.

                    ******
                      apply if1_conseq3 with (A3:=wrapped (a_ p) ∧ ¬ wrapped (a_ p));
                      [apply neg_false|].
                    apply if1_andI.

                    *******
                      eapply if1_conseq1; [|apply if1_start]; spec_auto.

                    *******
                      specX_cnf_l;
                      repeat spec_auto.
                    eapply if1_conseq1; [apply conseq_and1, conseq_refl|].
                    eapply if1_conseq3; [|apply passwordChange].
                    introduce_existential_on_left p''.
                    introduce_existential_on_left x.
                    apply param_not_wrapped with (x:=pwd);
                      auto.

                    ******
                      apply passwordLeak.

      * (* Case B *)
        apply if_trans
          with (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ setPassword ⟨ ⟦ pwd ↦ a_ p ⟧
                                                                ⟦ pwd' ↦ a♢ 1 ⟧ empty  ⟩ ] ]).

        ** apply ot_conseq1 with (A1:=(a_class (e_ a) Account ∧
                                       (a_exp (e_acc_f (e_ a) password ⩵ (e_ p))))).
           *** apply conseq_and.
               **** repeat apply conseq_and1.
                    apply conseq_refl.

               **** apply conseq_and2, conseq_refl.

           *** apply ot_conseq2 with (A2:=¬ ((a_class (e_ a) Account) ∧
                                             (a_exp ((e_acc_f (e_ a) password ⩵ (e_ p)))))).

               **** apply conseq_trans with (A2:=¬ a_class (e_ a) Account ∨
                                                 ¬ a_exp (e_acc_f (e_ a) password ⩵ (e_ p))).
                    *****
                      apply or_r, conseq_refl.

                    *****
                      apply neg_distr_and_2.

               **** apply ot_changes.

                    match goal with
                    | [|- _ ⊢ _ to1 ¬ (?Aa ∧ ?Ab) onlyIf _] =>
                      apply if1_conseq2 with (A2:=¬ Ab ∨ ¬ Aa);
                        [apply conseq_trans with (A2:=¬ Aa ∨ ¬ Ab);
                         [apply neg_distr_and_1|apply conseq_or_comm]|]
                    end.
                    match goal with
                    | [|- _ ⊢ _ to1 _ onlyIf ?A] =>
                      apply if1_conseq3 with (A3:=A ∨ (a_false));
                        [apply or_lr;
                         [apply conseq_refl
                         |apply conseq_absurd]|]
                    end.
                    apply if1_orI2.

                    *****
                      eapply if1_conseq3;
                      [apply or_l, conseq_refl|].
                    apply passwordChange.
                    *****
                      eapply if1_conseq1;
                      [apply conseq_and1, conseq_refl|].
                    apply if1_conseq3 with (A3:=a_false);
                      [apply conseq_absurd|apply change_class_absurd].

        ** apply if_conseq2 with (A2:=¬ wrapped (a_ p)).

           *** apply conseq_ex1;
                 intros;
                 subst_simpl.
               apply conseq_ex1;
                 intros;
                 subst_simpl.
               apply conseq_trans with (A2:=av_ x0 external ∧ av_ x0 access (a_ p));
                 [
                 | apply conseq_not_wrapped].
               spec_auto.

               **** apply caller_ext.
               **** apply calls_param1.

           *** apply if_orE with (A':= wrapped (a_ p)).

               **** match goal with
                    | [|- _ ⊢ _ to _ onlyIf ?Aa ∨ ?Ab] =>
                      apply if_conseq3 with (A3:= a_true);
                        [ apply conseq_trans with (A2:=Ab ∨ Aa);
                          [ apply conseq_excluded_middle
                          | apply conseq_or_comm]
                        |]
                    end.
                    apply if_start_conseq.
                    apply conseq_true.

               **** apply ot_conseq1 with (A1:= a_class (e_ a) Account ∧
                                                (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)) ∧
                                                 wrapped (a_ p))).

                    ***** repeat spec_auto.

                    *****
                       apply by_changes_and_conseq.

                    ******
                      eapply conseq_trans;
                      [|apply neg_distr_and_2].
                    apply or_r.
                    eapply conseq_trans;
                      [|apply neg_distr_and_2].
                    spec_auto.

                    ******
                      eapply if1_conseq2;
                      [apply neg_distr_and_1|].
                    apply if1_orI2.

                    ******* eapply if1_conseq1; [|apply change_class_absurd]; spec_auto.
                    *******
                      eapply if1_conseq2; [apply neg_distr_and_1|].
                    apply if1_orI2.

                    ********
                      apply if1_conseq3 with (A3:=wrapped (a_ p) ∧ ¬ wrapped (a_ p));
                      [apply neg_false|].
                    apply if1_andI.

                    *********
                      eapply if1_conseq1; [|apply if1_start]; spec_auto.

                    *********
                      specX_cnf_l;
                      repeat spec_auto.
                    eapply if1_conseq1; [apply conseq_and1, conseq_refl|].
                    eapply if1_conseq3; [|apply passwordChange].
                    introduce_existential_on_left p''.
                    introduce_existential_on_left x.
                    apply param_not_wrapped with (x:=pwd);
                      auto.

                    ********
                      apply passwordLeak.

  Qed.

  Close Scope assert_scope.
  Close Scope reduce_scope.
End SimpleBankAccount.
