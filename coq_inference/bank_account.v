Require Import List.
Require Import String.
Open Scope string_scope.
Require Import L_def.
Require Import defs.
Require Import common.
Require Import exp.
Require Import inference_tactics.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module BankAccount(L : LanguageDef).

  Export L.
  Module L_InferenceTactics := InferenceTactics(L).
  Import L_InferenceTactics.

  Open Scope specw_scope.
  Open Scope reduce_scope.

  (** #<h2>#Variables#</h2>#*)

  (** #<h2>#Account Class#</h2># *)

  Definition Account := classID 100.

  Definition password := fieldID 101.

  Definition authenticate := methID 101.

  Parameter authenticateBody : block.

  Definition changePassword := methID 102.

  Parameter changePasswordBody : block.

  Definition AccountDef := clazz Account
                                 boundary
                                 (⟦ password ↦ (t_cls Object) ⟧ empty)
                                 (⟦ changePassword ↦ changePasswordBody ⟧
                                    ⟦ authenticate ↦ authenticateBody ⟧
                                    empty)
                                 empty.

  Definition pwd := (n_ 101).

  Definition newPwd := (n_ 205).

  (** #<h2>#Ledger Class#</h2># *)

  Definition Ledger := classID 200.

  Definition acc1 := fieldID 201.

  Definition acc2 := fieldID 202.

  Definition bal1 := fieldID 203.

  Definition bal2 := fieldID 204.

  Definition ledgerTransfer := methID 201.

  Parameter ledgerTransferBody : block.

  Definition ledgerGetBalance := gFieldID 201.

  Definition acc := x_ (n_ 201).

  Definition ledgerGetBalBody := e_if (e_eq (e_var acc) (e_acc_f (e_this) acc1))
                                      (e_acc_f (e_this) acc1)
                                      (e_if (e_eq (e_var acc) (e_acc_f (e_this) acc2))
                                            (e_acc_f (e_this) bal2)
                                            (e_int -1)).

  Definition LedgerDef := clazz Ledger
                                inside
                                (⟦ bal2 ↦ t_int ⟧
                                   ⟦ bal1 ↦ t_int ⟧
                                   ⟦ acc2 ↦ (t_cls Account) ⟧
                                   ⟦ acc1 ↦ (t_cls Account) ⟧
                                   empty)
                                (⟦ ledgerTransfer ↦ ledgerTransferBody ⟧ empty)
                                (⟦ ledgerGetBalance ↦ (int, ledgerGetBalBody) ⟧empty).

  Definition fromAcc := (n_ 202).

  Definition toAcc := (n_ 203).

  Definition amt := (n_ 204).

  (** #<h2>#Bank Class#</h2># *)

  Definition Bank := classID 300.

  Definition book := fieldID 301.

  Definition getBalance := gFieldID 302.

  Definition getBalanceBody := (e_acc_g (e_acc_f (e_this) book) ledgerGetBalance (e_var acc)).

  Definition transfer := methID 303.

  Parameter transfer_body : block.

  Definition BankDef := clazz Bank
                              boundary
                              (⟦ book ↦ (t_cls Ledger) ⟧ empty)
                              (⟦ transfer ↦ transfer_body ⟧ empty)
                              (⟦ getBalance ↦ (int, getBalanceBody) ⟧ empty).

  (** #<h2>#Bank Module#</h2># *)

  Definition BankMdl := (⟦ Account ↦ AccountDef ⟧
                           ⟦ Ledger ↦ LedgerDef ⟧
                           ⟦ Bank ↦ BankDef ⟧ empty).

  Lemma BankMdlMethods :
    forall C CDef m, ⟦ C ↦ CDef ⟧_∈ BankMdl ->
                m ∈ c_meths CDef ->
                (C = Bank /\ CDef = BankDef /\ m = transfer) \/
                (C = Ledger /\ CDef = LedgerDef /\ m = ledgerTransfer) \/
                (C = Account /\ CDef = AccountDef /\ (m = authenticate \/ m = changePassword)).
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
      destruct (eq_dec m authenticate);
        subst.

      ** repeat map_rewrite.

      ** destruct (eq_dec m changePassword);
           subst.

         *** repeat map_rewrite.

         *** repeat map_rewrite.
             destruct_exists_loo.
             inversion H0.

    * destruct (eq_dec C Ledger);
        subst.

      ** right; left;
           split;
           auto.
        repeat map_rewrite.
         inversion H;
           subst.
         destruct (eq_dec m ledgerTransfer);
           subst;
           auto.

         simpl in *.
         repeat map_rewrite.
         destruct_exists_loo.
         inversion H0.

      ** destruct (eq_dec C Bank);
           subst.

         *** left;
               split;
               auto.

             repeat map_rewrite.
             inversion H;
               subst.
             simpl in *.
             destruct (eq_dec m transfer);
               subst;
               auto.

             repeat map_rewrite.
             destruct_exists_loo.
             inversion H0.

         *** repeat map_rewrite.
             inversion H.
  Qed.

  (** Type System Guarantees **)

  Parameter bankTransferParameters :
    forall b β, BankMdl ⊢ ((a_class (e_ b) Bank) ∧
                      ∃x.[(a♢ 0) calls (a_ b) ◌ transfer ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦  a♢ 1⟧
                                                                            ⟦ fromAcc ↦ a♢ 2 ⟧
                                                                            ⟦ toAcc ↦ a♢ 3⟧
                                                                            ⟦ amt ↦ a♢ 4 ⟧ empty⟩ ]]]]]).

  Parameter ledgerTransferParameters :
    forall l β, BankMdl ⊢ ((a_class (e_ l) Ledger) ∧
                      ∃x.[(a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ⟦ fromAcc ↦ a♢ 1 ⟧
                                                                              ⟦ toAcc ↦ a♢ 2⟧
                                                                              ⟦ amt ↦ a♢ 3 ⟧ empty⟩ ]]]]).

  Parameter authenticateParameters :
    forall a β, BankMdl ⊢ ((a_class (e_ a) Account) ∧
                      ∃x.[(a♢ 0) calls (a_ a) ◌ authenticate ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[ (a♢ 0) calls (a_ a) ◌ authenticate ⟨ ⟦ pwd ↦ a♢ 1 ⟧ empty⟩ ]]).

  Parameter changePasswordParameters :
    forall a β, BankMdl ⊢ ((a_class (e_ a) Account) ∧
                      ∃x.[(a♢ 0) calls (a_ a) ◌ changePassword ⟨ β ⟩ ])
                   ⊇
                   (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                          ⟦ newPwd ↦ a♢ 2 ⟧empty⟩ ]]]).

  (** #<h2># Reduce Balance #</h2># *)

  Parameter authenticateBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal))) ∧
                                    (*                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧*)
                                    (a_class (e_ a) Account)}
                            m_call a authenticate β
                            {post: ¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal))}.

  Lemma authBalChange :
    forall a a' b bal p,
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal))) ∧
(*                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧*)
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ authenticate ⟨ ⟦ pwd ↦ av_ p ⟧ empty ⟩]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal)))
              onlyIf (a_exp (e_false)).
  Proof.
    intros.
    eapply if1_classical with (β := ⟦ pwd ↦ p ⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence1.
    * apply authenticateBalanceChangeSpecification.
    * specX_cnf_r.
      repeat spec_auto.
  Qed.

  Parameter changePasswordBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal))) ∧
                                    (a_class (e_ a) Account)}
                            m_call a changePassword β
                            {post: a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))}.

  Lemma changePasswordBalChange :
    forall a a' b bal p p',
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal))) ∧
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ av_ p ⟧ ⟦ newPwd ↦ av_ p' ⟧ empty ⟩]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal)))
              onlyIf (a_exp (e_false)).
  Proof.
    intros.
    apply if1_classical with (β := ⟦ pwd ↦ p ⟧ ⟦ newPwd ↦ p'⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence2; [|apply eq_implies_not_lt].
    repeat hoare_simpl.
    apply changePasswordBalanceChangeSpecification.
  Qed.

  Parameter ledgerTransferBalanceChangeSpecification :
    forall a a' b l bal β,
      BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                      (a_class (e_ b)  Bank) ∧
                      (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal))) ∧
                      (a_class (e_ l) Ledger) ∧
                      (¬ (a_exp (e_val a' ⩵ e_ a)))}
              m_call l ledgerTransfer (⟦ fromAcc ↦ a' ⟧ β)
              {post: (a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩵ (e_int bal)))}.

  Lemma ledgerTransferBalChange :
    forall l a a' a'' m b bal,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal))) ∧
                 (a_class (e_ l) Ledger) ∧
                 (∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ⟦ fromAcc ↦ av_ a' ⟧
                                                                ⟦ toAcc ↦ av_ a'' ⟧
                                                                ⟦ amt ↦ av_ m ⟧ empty ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf a_false.
  Proof.
    intros.

    eapply if1_conseq3;
      [
      |apply if1_start].

    specX_cnf_r.

    introduce_existential_on_left x.

    eapply conseq_trans;
      [eapply conseq_and
         with (A1:= wrapped (a_ l))
              (A2:= ¬ wrapped (a_ l))
      |apply neg_false].

    * specX_cnf_r.
      apply conseq_and2, conseq_and2, conseq_and2, conseq_and1.
      apply inside_wrapped with (Def:=LedgerDef);
        auto.

    *  specX_cnf_r.
       repeat apply conseq_and2.
       apply recv_not_wrapped.
  Qed.

  Parameter transferBalanceChangeSpecification :
    forall a a' b b' p p' bal β,
      BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                      (a_class (e_ b)  Bank) ∧
                      (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal))) ∧
                      (a_class (e_ b') Bank) ∧
                      (¬ ((a_exp ((e_acc_f (e_ a) password) ⩵ (e_val p))) ∧
                          (a_exp (e_val a' ⩵ e_ a)) ∧
                          (a_exp (e_ b' ⩵ e_ b))))}
              m_call b' transfer (⟦ pwd ↦ p'⟧ ⟦ fromAcc ↦ a' ⟧ β)
              {post: (a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩵ (e_int bal)))}.

  Lemma bankTransferBalChange :
    forall a b b' bal a' m a'',
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal))) ∧
                 (a_class (e_ b') Bank) ∧
                 (∃x.[∃x.[ (a♢ 0) calls (a_ b') ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1  ⟧
                                                               ⟦ fromAcc ↦ av_ a' ⟧
                                                               ⟦ toAcc ↦ av_ a'' ⟧
                                                               ⟦ amt ↦ av_ m ⟧
                                                               empty  ⟩]]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                             ⟦ fromAcc ↦ a_ a ⟧
                                                                             ⟦ toAcc ↦ a♢ 2 ⟧
                                                                             ⟦ amt ↦ a♢ 3 ⟧
                                                                             empty  ⟩ ∧
                                          (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 1)))]]]]).
  Proof.
    intros.

    specX_cnf_r.

    apply if1_ex1;
      intro p.
    subst_simpl.

    eapply if1_conseq3;
      [
      | apply if1_andI
          with (A':= (a_exp (e_acc_f (e_ a) password ⩵ e_val p)) ∧
                     (a_exp (e_val a' ⩵ e_ a)) ∧
                     (a_exp (e_ b' ⩵ e_ b)));
        [ apply if1_start
        | ]].

    * commutativity.
      introduce_existential_on_left x.
      specX_cnf_r.
      commutativity.
      substitute_equality a'.
      substitute_equality (v_ b').
      there_exists_on_right m.
      there_exists_on_right a''.
      there_exists_on_right p.
      there_exists_on_right x.
      repeat spec_auto.

    * apply if1_classical with (β:=⟦ pwd ↦ p ⟧
                                     ⟦ fromAcc ↦ a' ⟧
                                     ⟦ toAcc ↦ a'' ⟧
                                     ⟦ amt ↦ m ⟧
                                     empty);
        [|repeat compose_simpl; auto].

      match goal with
      | [|- _ ⊢ {pre: _ } _ {post: ¬ a_exp (?e1 ⩻ ?e2)}] =>
        eapply hoare_consequence2 with (A2':=a_exp (e1 ⩵ e2))
      end.

      ** eapply hoare_consequence1.
         apply transferBalanceChangeSpecification with (p:=p).
         repeat spec_auto.

      ** apply eq_implies_not_lt.

  Qed.

  Ltac BankMdlMethodsCases :=
    match goal with
    | [ Hclass : ⟦ ?C' ↦ ?CDef' ⟧_∈ BankMdl,
                 Hmeth : ?m' ∈ c_meths ?CDef' |- _ ] =>
      destruct (BankMdlMethods C' CDef' m' Hclass Hmeth);
      [|disj_split];
      andDestruct;
      subst
    end.

  Lemma balanceChange :
    forall a b bal,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                             ⟦ fromAcc ↦ a_ a ⟧
                                                                             ⟦ toAcc ↦ a♢ 2 ⟧
                                                                             ⟦ amt ↦ a♢ 3 ⟧
                                                                             empty  ⟩ ∧
                                          (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 1)))]]]]).
  Proof.
    intros.
    apply if1_internal.

    * intros.
      (* Case Analysis of all possible method calls to BankMdl objects *)
      BankMdlMethodsCases.

      (* Bank Methods*)
      ** eapply if1_conseq1;
           [
           |].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Bank);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply bankTransferParameters.

         *** specX_cnf_r.
             apply if1_ex1;
               intro m;
               subst_simpl.
             specX_cnf_r.
             apply if1_ex1;
               intro a'';
               subst_simpl.
             specX_cnf_r.
             apply if1_ex1;
               intro a';
               subst_simpl.

             apply bankTransferBalChange.

      (* Ledger methods*)
      ** eapply if1_conseq1;
           [
           |].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Ledger);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply ledgerTransferParameters.

         *** specX_cnf_r;
               apply if1_ex1;
               intros;
               subst_simpl.
             specX_cnf_r;
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
               |apply ledgerTransferBalChange].
             repeat spec_auto.
             **** specX_cnf_r.
                  introduce_existential_on_left x.
                  specX_cnf_r.
                  apply conseq_and2, conseq_and2, conseq_and2, conseq_and1, conseq_refl.
             **** repeat apply conseq_and2;
                    apply conseq_refl.

      (* Account methods*)
      ** (* case analysis of Account methods*)
        disj_split;
          subst.

        (* authenticate *)
         *** eapply if1_conseq1;
               [
               |].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  *****
                    apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply authenticateParameters.

             **** specX_cnf_r;
                    apply if1_ex1;
                    intros;
                    subst_simpl.

                  apply if1_conseq3
                    with (A3:= a_false);
                    [apply conseq_absurd
                    |].
                  eapply if1_conseq1;
                    [
                    |apply authBalChange].
                  repeat spec_auto.
                  ***** specX_cnf_r.
                  introduce_existential_on_left x.
                  specX_cnf_r.
                  apply conseq_and2, conseq_and2, conseq_and2, conseq_and1, conseq_refl.
                  *****
                    repeat apply conseq_and2;
                    apply conseq_refl.

         (* changePassword *)
         *** eapply if1_conseq1;
               [
               |].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  *****
                    apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply changePasswordParameters.

             **** specX_cnf_r;
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
                    |apply changePasswordBalChange].
                  repeat spec_auto.
                  *****
                    apply conseq_and1, conseq_and2, conseq_refl.

                  *****
                    repeat apply conseq_and2;
                    apply conseq_refl.

    (* encapsulation *)
    * eapply enc_conseq2;
        [apply eq_implies_not_lt
        |apply enc_eq].

      **  apply enc_eintrnl.
          apply i_ghost with (C:=Bank)(CDef:=BankDef)(e:=getBalanceBody);
            auto;
            repeat spec_auto.
          *** apply i_obj with (C:=Bank).
              spec_auto.
              exists BankDef.
              auto.

          *** apply i_obj with (C:=Account).
              spec_auto.
              exists AccountDef.
              auto.

      **  apply enc_eintrnl;
            apply i_int.

    * spec_auto.
  Qed.

  Lemma balanceChange' :
    forall a b bal,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (¬ a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal))))
              to (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
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
         eapply if1_conseq2;
           [apply neg_distr_and_1|].
         apply if1_orI2.

         *** eapply if1_conseq1;
               [|apply change_class_absurd].
             spec_auto.

         *** eapply if1_conseq1;
               [|apply change_class_absurd].
             spec_auto.

      ** eapply if1_conseq2;
           [apply conseq_not_not1|].
         eapply if1_conseq3;
           [|apply balanceChange].
         introduce_existential_on_left m.
         introduce_existential_on_left a''.
         introduce_existential_on_left p.
         introduce_existential_on_left x.
         there_exists_on_right p.
         repeat spec_auto.

         apply conseq_and1.
         apply param_not_wrapped with (x:=pwd).
         auto.

  Qed.

  (** #<h2># Change Password #</h2>#  *)

  Parameter authenticate_PasswordChangeSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                (a_class (e_ a) Account)}
                        m_call a' authenticate β
                        {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma authenticate_PasswordChange :
    forall a a' p p', BankMdl ⊢ (a_class (e_ a) Account ∧
                            (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                            (a_class (e_ a') Account) ∧
                            (∃x.[ (a♢ 0) calls (a_ a') ◌ authenticate ⟨ ⟦ pwd ↦ av_ p' ⟧ empty ⟩ ]))
                         to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                         onlyIf a_false.
  Proof.
    intros.

    apply if1_classical with (β:=⟦ pwd ↦ p' ⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply authenticate_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Parameter changePassword_PasswordChangeSpecification :
    forall a a' p p' β, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                                   (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                   (a_class (e_ a') Account) ∧
                                   (¬ (a_exp ((e_ a') ⩵ (e_ a)) ∧
                                       a_exp ((e_val p') ⩵ (e_ p))))}
                           m_call a' changePassword (⟦ pwd ↦ p' ⟧  β)
                           {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma changePassword_PasswordChange :
    forall a a' p p' p'', BankMdl ⊢ (a_class (e_ a) Account ∧
                                (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                                (a_class (e_ a') Account) ∧
                                (∃x.[ (a♢ 0) calls (a_ a') ◌ changePassword ⟨ ⟦ pwd ↦ av_ p' ⟧
                                                                                ⟦ newPwd ↦ av_ p'' ⟧ empty ⟩ ]))
                             to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                             onlyIf (a_exp ((e_ a') ⩵ (e_ a)) ∧
                                     a_exp ((e_val p') ⩵ (e_ p))).
  Proof.
    intros.

    apply if1_classical with (β:=⟦ pwd ↦ p' ⟧ ⟦ newPwd ↦ p'' ⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply changePassword_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Parameter ledgerTransfer_PasswordChangeSpecification :
    forall a l p β, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                                (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                (a_class (e_ l) Ledger)}
                        m_call l ledgerTransfer β
                        {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma ledgerTransfer_PasswordChange :
    forall a p l a' a'' m, BankMdl ⊢ (a_class (e_ a) Account ∧
                                 (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                                 (a_class (e_ l) Ledger) ∧
                                 (∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ⟦ fromAcc ↦ av_ a' ⟧
                                                                                ⟦ toAcc ↦ av_ a'' ⟧
                                                                                ⟦ amt ↦ av_ m ⟧ empty ⟩ ]))
                              to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                              onlyIf a_false.
  Proof.
    intros.

    apply if1_classical with (β:=⟦ fromAcc ↦ a' ⟧ ⟦ toAcc ↦ a'' ⟧ ⟦ amt ↦ m ⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply ledgerTransfer_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Parameter transfer_PasswordChangeSpecification :
    forall a p b β, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                               (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                               (a_class (e_ b) Bank)}
                       m_call b transfer β
                       {post: a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))}.

  Lemma transfer_PasswordChange :
    forall a p b p' a' a'' m, BankMdl ⊢ (a_class (e_ a) Account ∧
                                    (a_exp (e_acc_f (e_ a) password ⩵ e_ p)) ∧
                                    (a_class (e_ b) Bank) ∧
                                    (∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ av_ p' ⟧
                                                                             ⟦ fromAcc ↦ av_ a' ⟧
                                                                             ⟦ toAcc ↦ av_ a'' ⟧
                                                                             ⟦ amt ↦ av_ m ⟧ empty ⟩ ]))
                                 to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                                 onlyIf a_false.
  Proof.
    intros.

    apply if1_classical with (β:= ⟦ pwd ↦ p' ⟧ ⟦ fromAcc ↦ a' ⟧ ⟦ toAcc ↦ a'' ⟧ ⟦ amt ↦ m ⟧ empty);
      [|repeat compose_simpl; auto].
    eapply hoare_consequence2;
      [|apply conseq_not_not2].
    eapply hoare_consequence1;
      [apply transfer_PasswordChangeSpecification|].
    repeat spec_auto.
  Qed.

  Lemma passwordChange :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧
                      (a_exp (e_acc_f (e_ a) password ⩵ e_ p)))
                   to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                   onlyIf (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ a_ p ⟧ ⟦ newPwd ↦ a♢ 1 ⟧ empty  ⟩ ] ]).
  Proof.
    intros.
    apply if1_internal.

    * intros.
      BankMdlMethodsCases.

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
                       with (A1:= a_class (e_ α) Bank);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply bankTransferParameters.

         *** do 4 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).
             apply transfer_PasswordChange.

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
                       with (A1:= a_class (e_ α) Ledger);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply ledgerTransferParameters.

         *** do 3 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).
             apply ledgerTransfer_PasswordChange.

      ** disj_split;
         subst.
         *** apply if1_conseq3
               with (A3:=a_false);
               [apply conseq_absurd|].
             eapply if1_conseq1;
               [|].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  ***** apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply authenticateParameters.

             **** do 1 (specX_cnf_r;
                        apply if1_ex1;
                        intros;
                        subst_simpl).
                  apply authenticate_PasswordChange.

         *** eapply if1_conseq1;
               [|].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  ***** apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply changePasswordParameters.

             **** do 2 (specX_cnf_r;
                        apply if1_ex1;
                        intros;
                        subst_simpl).
                  eapply if1_conseq3;
                    [|apply if1_andI;
                      [apply if1_start|apply changePassword_PasswordChange]].
                  commutativity.
                  introduce_existential_on_left x.
                  there_exists_on_right y.
                  there_exists_on_right x.
                  specX_cnf_r.
                  substitute_equality (v_ α).
                  substitute_equality y0.
                  spec_auto.

    (* encapsulation *)
    * eapply enc_conseq2;
        [apply conseq_not_not2
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

  Parameter passwordLeakAuthenticateSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                                (a_class (e_ a')  Account) ∧
                                (a_class (e_ a) Account)}
                        m_call a authenticate β
                        {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.


  Lemma authenticatePasswordLeak :
    forall a a' p p', BankMdl ⊢ ((a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                            (a_class (e_ a') Account) ∧
                            (wrapped (a_ p)) ∧
                            (a_class (e_ a) Account) ∧
                            (∃x.[ (a♢ 0) calls (a_ a) ◌ authenticate ⟨ ⟦ pwd ↦ (av_ p') ⟧ empty⟩]))
                         to1 ¬ wrapped (a_ p)
                         onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ pwd ↦ p' ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakAuthenticateSpecification with (a':=a')|].
      repeat spec_auto.

    * repeat compose_simpl;
        auto.
  Qed.

  Parameter passwordLeakChangePasswordSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                                (a_class (e_ a')  Account) ∧
                                (a_class (e_ a) Account)}
                        m_call a changePassword β
                        {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.


  Lemma changePasswordLeak :
    forall a a' p p1 p2, BankMdl ⊢ ((a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                               (a_class (e_ a') Account) ∧
                               (wrapped (a_ p)) ∧
                               (a_class (e_ a) Account) ∧
                               (∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ (av_ p1) ⟧
                                                                              ⟦ newPwd ↦ (av_ p2) ⟧ empty⟩]))
                            to1 ¬ wrapped (a_ p)
                            onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ pwd ↦ p1 ⟧ ⟦ newPwd ↦ p2 ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakChangePasswordSpecification with (a':=a')|].
      repeat spec_auto.

    * repeat compose_simpl;
        auto.
  Qed.

  Parameter passwordLeakLedgerTransferSpecification :
    forall a l p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                               (a_class (e_ a)  Account) ∧
                               (a_class (e_ l) Ledger) ∧
                               ¬ (a_false)}
                       m_call l ledgerTransfer β
                       {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.


  Lemma ledgerTransferLeak :
    forall a l p m f t, BankMdl ⊢ ((a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                              (a_class (e_ a) Account) ∧
                              (wrapped (a_ p)) ∧
                              (a_class (e_ l) Ledger) ∧
                              (∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ⟦ fromAcc ↦ (av_ f) ⟧
                                                                             ⟦ toAcc ↦ (av_ t) ⟧
                                                                             ⟦ amt ↦ (av_ m) ⟧ empty⟩]))
                           to1 ¬ wrapped (a_ p)
                           onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ fromAcc ↦ f ⟧ ⟦ toAcc ↦ t ⟧ ⟦ amt ↦ m ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakLedgerTransferSpecification with (a:=a)|].
      repeat spec_auto.

    * repeat compose_simpl;
        auto.
  Qed.

  Parameter passwordLeakBankTransferSpecification :
    forall a b p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                               (a_class (e_ a)  Account) ∧
                               (a_class (e_ b) Bank) ∧
                               ¬ (a_false)}
                       m_call b transfer β
                       {post: ¬ a_exp ((e♢ 0) ⩵ (e_ p))}.

  Lemma bankTransferLeak :
    forall a b p p' m f t, BankMdl ⊢ ((a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                                 (a_class (e_ a) Account) ∧
                                 (wrapped (a_ p)) ∧
                                 (a_class (e_ b) Bank) ∧
                                 (∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ (av_ p') ⟧
                                                                          ⟦ fromAcc ↦ (av_ f) ⟧
                                                                          ⟦ toAcc ↦ (av_ t) ⟧
                                                                          ⟦ amt ↦ (av_ m) ⟧ empty⟩]))
                              to1 ¬ wrapped (a_ p)
                              onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:= ⟦ pwd ↦ p' ⟧ ⟦ fromAcc ↦ f ⟧ ⟦ toAcc ↦ t ⟧ ⟦ amt ↦ m ⟧ empty).

    * eapply hoare_consequence1;
        [apply passwordLeakBankTransferSpecification with (a:=a)|].
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

      (* Bank Methods*)
      ** eapply if1_conseq1;
           [
           |].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Bank);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply bankTransferParameters.

         *** do 4 (specX_cnf_r;
                   apply if1_ex1;
                   intros;
                   subst_simpl).

           eapply if1_conseq1;
               [|apply bankTransferLeak with (p:=p)(a:=a)(b:=α)].
             repeat spec_auto.
             repeat apply conseq_and2.
             apply conseq_refl.

      (* Ledger methods*)
      ** eapply if1_conseq1;
           [
           |].

         (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
         *** apply conseq_and.
             **** apply conseq_and1, conseq_refl.
             **** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Ledger);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply ledgerTransferParameters.

         *** specX_cnf_r;
               apply if1_ex1;
               intros;
               subst_simpl.
             specX_cnf_r;
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
               |apply ledgerTransferLeak with (a:=a)(l:=α)].
             repeat spec_auto.
             specX_cnf_r.
             introduce_existential_on_left x.
             specX_cnf_r.
             there_exists_on_right x.
             repeat apply conseq_and2.
             apply conseq_refl.

      (* Account methods*)
      ** (* case analysis of Account methods*)
        disj_split;
          subst.

        (* authenticate *)
         *** eapply if1_conseq1;
               [
               |].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  *****
                    apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply authenticateParameters.

             **** specX_cnf_r;
                    apply if1_ex1;
                    intros;
                    subst_simpl.

                  apply if1_conseq3
                    with (A3:= a_false);
                    [apply conseq_absurd
                    |].
                  eapply if1_conseq1;
                    [
                    |apply authenticatePasswordLeak with (a':=a)(a:=α)].
                  repeat spec_auto.
                  repeat apply conseq_and2;
                    apply conseq_refl.

         (* changePassword *)
         *** eapply if1_conseq1;
               [
               |].

             (** Using the type system to get actual paramters.
             TODO: Need to make into a tactic **)
             **** apply conseq_and.
                  *****
                    apply conseq_and1, conseq_refl.
                  ***** eapply conseq_trans;
                    [apply conseq_and
                       with (A1:= a_class (e_ α) Account);
                     [ spec_auto
                     | repeat apply conseq_and2; apply conseq_refl]
                    |].
                  apply changePasswordParameters.

             **** specX_cnf_r;
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
    * eapply enc_conseq2;
        [apply conseq_not_not2
        |].

      apply enc_wrapped1.

    * eapply conseq_trans;
        [|apply conseq_not_not2].
      spec_auto.


  Qed.

  (** BankSpec **)

  Lemma necessityBankSpec :
    forall a b bal p, BankMdl ⊢ (a_class (e_ a) Account ∧ 
                            a_class (e_ b) Bank ∧
                            (¬ a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩻ (e_int bal))) ∧
                            (a_exp (e_acc_f (e_ a) password ⩵ (e_ p))))
                         to (a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩻ (e_int bal)))
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
          with (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ a_ p ⟧
                                                                   ⟦ newPwd ↦ a♢ 1 ⟧ empty  ⟩ ] ]).

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

  Close Scope specw_scope.
  Close Scope reduce_scope.
End BankAccount. 
