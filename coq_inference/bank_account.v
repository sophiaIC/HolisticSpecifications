Require Import List.
Require Import String.
Open Scope string_scope.
Require Import L_def.
Require Import defs.
Require Import common.
Require Import exp.
Require Import chainmail_tactics.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module BankAccount(L : LanguageDef).

  Module L_ChainmailTactics := ChainmailTactics(L).
  Import L_ChainmailTactics.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.
  Open Scope hoare_scope.
  Open Scope inference_scope.
  Open Scope chainmail_tactics_scope.

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

  (** #<h2>#Account Specifications#</h2># *)

  Parameter authenticateBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                                    (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal)))}
                            m_call a authenticate β
                            {post: a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))}.

  Parameter changePasswordBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                                    (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal)))}
                            m_call a changePassword β
                            {post: a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))}.

  Parameter transferBalanceChangeSpecification :
    forall a a' b b' p bal β,
      BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                      (a_class (e_ b)  Bank) ∧
                      (a_class (e_ b') Bank) ∧
                      (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal)))}
              m_call b' transfer (⟦ pwd ↦ p⟧ ⟦ fromAcc ↦ a' ⟧ β)
              {post: a_exp (e_val p ⩵ e_acc_f (e_ a) password) ∧
                     (a_exp (e_val a' ⩵ (e_ a))) ∧
                     (a_exp (e_ b' ⩵ (e_ b)))}.

  Lemma eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).
  Admitted.

  Lemma not_false_is_true :
    forall M, M ⊢ (¬ a_exp (e_false)) ⊇ (a_exp (e_true)).
  Admitted.

  Lemma true_is_not_false :
    forall M, M ⊢ (a_exp (e_true)) ⊇ (¬ a_exp (e_false)).
  Admitted.

  Lemma and_true1 :
    forall M A, M ⊢ (A ∧ (a_exp (e_true))) ⊇ A.
  Admitted.

  Lemma and_true2 :
    forall M A, M ⊢ A ⊇ (A ∧ (a_exp (e_true))).
  Admitted.

  Lemma and_comm :
    forall M A1 A2, M ⊢ (A1 ∧ A2) ⊇ (A2 ∧ A1).
  Admitted.

  Lemma and_assoc1 :
    forall M A1 A2 A3, M ⊢ (A1 ∧ A2 ∧ A3) ⊇ (A1 ∧ (A2 ∧ A3)).
  Admitted.

  Lemma and_assoc2 :
    forall M A1 A2 A3, M ⊢ A1 ∧ (A2 ∧ A3) ⊇ A1 ∧ A2 ∧ A3.
  Admitted.

  Lemma and_consequence1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                   M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2.
  Admitted.

  Lemma and_consequence2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                   M ⊢ A1 ∧ A2 ⊇ A1 ∧ A2'.
  Admitted.

  Lemma conseq_and1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                   M ⊢ A1 ∧ A2 ⊇ A1'.
  Admitted.

  Lemma conseq_and2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                   M ⊢ A1 ∧ A2 ⊇ A2'.
  Admitted.

  Lemma conseq_ex :
    forall M A1 A2, (forall x, M ⊢ [x /s 0] A1 ⊇ A2) ->
               M ⊢ (∃x.[A1]) ⊇ A2.
  Admitted.

  Lemma subst_eq :
    forall M x y z A, M ⊢ (a_exp (e_val x ⩵ e_val y)) ∧ [y /s z] A ⊇ [x /s z] A.
  Admitted.

  Ltac hoare_simpl :=
    match goal with
    | [|- _ ⊢ {pre: ?A1 ∧ (?A2 ∧ ?A3)} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_assoc2]
    | [|- _ ⊢ {pre: (_ ∧ (_ ∧ _)) ∧ _} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence1, and_assoc2]
    | [|- _ ⊢ {pre: _ ∧ ((_ ∧ _) ∧ _)} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence1, and_assoc2]
    | [|- _ ⊢ {pre: _ ∧ (a_exp (e_true))} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_true1]
    | [|- _ ⊢ {pre: _ ∧ (¬ (a_exp (e_false)))} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence2, not_false_is_true]
    end.

  Ltac spec_auto :=
    match goal with
    |[|- _ ⊢ ?A ⊇ ?A] =>
     apply conseq_refl
    |[|- _ ⊢ ∃x.[_] ⊇ _] =>
     apply conseq_ex; intros; simpl
    |[|- _ ⊢ ?A ∧ _ ⊇ ?A] =>
     apply conseq_and1
    |[|- _ ⊢ _ ∧ ?A ⊇ ?A] =>
     apply conseq_and2
    |[|- _ ⊢ _ ∧ ?A ∧ _ ⊇ ?A] =>
     apply conseq_and2, conseq_and1
    |[|- _ ⊢ _ ∧ _ ∧ ?A ∧ _ ⊇ ?A] =>
     apply conseq_and2, conseq_and2, conseq_and1
    end.

  Lemma authBalChange :
    forall a a' b bal ps,
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ (am_ authenticate) ⟨ (fun v => Some (av_ v)) ∘ ps ⟩]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal)))
              onlyIf (a_exp (e_false)).
  Proof.
    intros.
    eapply if1_classical with (β := ps);
      [|auto].
    eapply hoare_consequence2; [|apply eq_implies_not_lt].
    repeat hoare_simpl.
    apply authenticateBalanceChangeSpecification.
  Qed.

  Lemma changePassowrdBalChange :
    forall a a' b bal ps,
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ (am_ changePassword) ⟨ (fun v => Some (av_ v)) ∘ ps ⟩]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩻ (e_int bal)))
              onlyIf (a_exp (e_false)).
  Proof.
    intros.
    apply if1_classical with (β := ps);
      [|auto].
    eapply hoare_consequence2; [|apply eq_implies_not_lt].
    repeat hoare_simpl.
    apply changePasswordBalanceChangeSpecification.
  Qed.

  Lemma ledgerTransferBalChange :
    forall l a b bal ps v,
      BankMdl ⊢ ((a_class (e_ l) Ledger) ∧
                 (a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_val v))) ∧
                (∃x.[ (a♢ 0) calls (a_ l) ◌ (am_ ledgerTransfer) ⟨ ps ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ b) ◌ (am_ transfer) ⟨ ⟦ pwd ↦ (av_ v)⟧
                                                                                ⟦ amt ↦ (a♢ 1)⟧
                                                                                ⟦ fromAcc ↦ (a_ a) ⟧
                                                                                ⟦ toAcc ↦ (a♢ 2) ⟧
                                                                                empty ⟩]]]).
  Proof.
    intros.
    eapply (if1_conseq);
      [|apply conseq_refl
       |apply conseq_refl
       |apply absurd].
    eapply (if1_conseq);
      [|apply conseq_refl
       |apply conseq_refl
       |apply neg_false with (A:=wrapped(a_ l))].
    apply if1_andI.

    - apply if1_if.
      apply if_start.
      apply consequence_transitivity with (A2 := a_class (e_ l) Ledger);
        [apply conseq_and1|apply inside_wrapped with (Def:=LedgerDef); auto].
      repeat apply conseq_and1; spec_auto.

    - apply if1_if, if_start.
      repeat apply conseq_and2.
      spec_auto.
      apply recv_not_wrapped.
  Qed.

  Lemma bankTransferBalChange :
    forall a b b' bal p p' ps,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_class (e_ b') Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                (∃x.[ (a♢ 0) calls (a_ b') ◌ (am_ transfer) ⟨ ⟦ pwd ↦ a_ p' ⟧ ps  ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[∃x.[∃x.[ (a♢ 0) calls (a♢ 1) ◌ (am_ transfer) ⟨ ⟦ pwd ↦ (a_ p)⟧
                                                                                ⟦ amt ↦ (a♢ 2)⟧
                                                                                ⟦ fromAcc ↦ (a♢ 3) ⟧
                                                                                ⟦ toAcc ↦ (a♢ 4) ⟧
                                                                                empty ⟩]]]).
  Proof.
    intros.

    extract3 (v_ p) 100;
      eapply if1_conseq;
      [|apply conseq_refl
       |apply conseq_refl
       |apply subst_eq with (y:=v_ p'); simpl];
      subst_simpl.

    eapply if1_andI.

    - eapply if1_if.
      eapply if_start.
      eapply conseq_and1, conseq_and2.


    extract3 (v_ a) 100;
      eapply if1_conseq;
      [|apply conseq_refl
       |apply conseq_refl
       |apply subst_eq with (y:=v_ b); simpl];
      subst_simpl.

    eapply if1_classical;
      [|auto].

  Admitted.

  Lemma balanceEncaps :
    forall b b' a bal 


  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End BankAccount.
