Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import chainmail.
Require Import hoare.
Require Import List.
Require Import String.
Require Import inference.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module BankAccount(L : LanguageDef).

  Module L_Inference := Inference(L).
  Import L_Inference.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.
  Open Scope hoare_scope.
  Open Scope inference_scope.

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
                                    ⟦ authenticate ↦ authenticateBody  ⟧
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

  Lemma eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).
    Admitted.

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
    admit. (* add normal hoare logic rules *)

  Admitted.

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
      [|auto]. (* add simplification to tactic*)
    eapply hoare_consequence2; [|apply eq_implies_not_lt].
    admit. (* add normal hoare logic rules *)

  Admitted.

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
    
  Admitted.

  Lemma bankTransferBalChange :
    forall l a b b' bal ps v,
      BankMdl ⊢ ((a_class (e_ l) Ledger) ∧
                 (a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_class (e_ b') Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_val v))) ∧
                (∃x.[ (a♢ 0) calls (a_ b) ◌ (am_ transfer) ⟨ ps ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ b) ◌ (am_ transfer) ⟨ ⟦ pwd ↦ (av_ v)⟧
                                                                                ⟦ amt ↦ (a♢ 1)⟧
                                                                                ⟦ fromAcc ↦ (a_ a) ⟧
                                                                                ⟦ toAcc ↦ (a♢ 2) ⟧
                                                                                empty ⟩]]]).
  Proof.
    intros.
    
  Admitted.


  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End BankAccount.
