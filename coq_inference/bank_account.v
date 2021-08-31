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

  Open Scope chainmail_scope.
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
                (C = Bank /\ m = transfer) \/
                (C = Ledger /\ m = ledgerTransfer) \/
                (C = Account /\ (m = authenticate \/ m = changePassword)).
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
                   (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ a) ◌ authenticate ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                        ⟦ newPwd ↦ a♢ 2 ⟧empty⟩ ]]]).

  (** #<h2>#Account Specifications#</h2># *)

  Parameter authenticateBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧
                                    (a_class (e_ a) Account)}
                            m_call a authenticate β
                            {post: a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))}.

  Parameter changePasswordBalanceChangeSpecification :
    forall a a' b β bal, BankMdl ⊢ {pre: (a_class (e_ a') Account) ∧
                                    (a_class (e_ b)  Bank) ∧
                                    (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧
                                    (a_class (e_ a) Account)}
                            m_call a changePassword β
                            {post: a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))}.

  Parameter transferBalanceChangeSpecification :
    forall a a' b b' p p' bal β,
      BankMdl ⊢ {pre: (a_class (e_ a) Account) ∧
                      (a_class (e_ b)  Bank) ∧
                      (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                      (a_exp ((e_acc_f (e_ a) password) ⩵ (e_val p))) ∧
                      (a_class (e_ b') Bank) ∧
                      (¬ ((a_exp (e_val p' ⩵ e_val p)) ∧
                          (a_exp (e_val a' ⩵ e_ a)) ∧
                          (a_exp (e_ b' ⩵ e_ b))))}
              m_call b' transfer (⟦ pwd ↦ p'⟧ ⟦ fromAcc ↦ a' ⟧ β)
              {post: (a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩵ (e_int bal)))}.

  Lemma authBalChange :
    forall a a' b bal ps,
      BankMdl ⊢ ((a_class (e_ a') Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a')) ⩵ (e_int bal))) ∧
                 (a_class (e_ a) Account) ∧
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ authenticate ⟨ (fun v => Some (av_ v)) ∘ ps ⟩]))
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
                 (∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ (fun v => Some (av_ v)) ∘ ps ⟩]))
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
                 (∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ps ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[∃x.[∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ (av_ v)⟧
                                                                      ⟦ fromAcc ↦ (a_ a) ⟧
                                                                      ⟦ amt ↦ (a♢ 1)⟧
                                                                      ⟦ toAcc ↦ (a♢ 2) ⟧
                                                                      empty ⟩]]]).
  Proof.
    intros.
    eapply (if1_conseq);
      [|apply conseq_refl
       |apply conseq_refl
       |apply conseq_absurd].
    eapply (if1_conseq);
      [|apply conseq_refl
       |apply conseq_refl
       |apply neg_false with (A:=wrapped(a_ l))].
    apply if1_andI.

    - apply if1_if.
      eapply if_conseq;
        [ apply if_start
        | apply conseq_refl
        | apply conseq_refl
        | ].
      apply conseq_trans with (A2 := a_class (e_ l) Ledger);
        [apply conseq_and1|apply inside_wrapped with (Def:=LedgerDef); auto].
      repeat apply conseq_and1; spec_auto.

    - eapply if1_if, if_conseq;
        [ apply if_start
        | apply conseq_refl
        | apply conseq_refl
        | ].
      repeat apply conseq_and2.
      spec_auto.
      apply recv_not_wrapped.
  Qed.

  Lemma bankTransferBalChange' :
    forall a b b' bal p p' a' m a'',
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                 (a_class (e_ b') Bank) ∧
                 (∃x.[ (a♢ 0) calls (a_ b') ◌ transfer ⟨ ⟦ pwd ↦ a_ p' ⟧
                                                           ⟦ fromAcc ↦ a_ a' ⟧
                                                           ⟦ amt ↦ av_ m ⟧
                                                           ⟦ toAcc ↦ av_ a'' ⟧
                                                           empty  ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (a_exp (e_ p' ⩵ e_ p) ∧ (a_exp (e_ a' ⩵ e_ a)) ∧ (a_exp (e_ b' ⩵ e_ b))).
  Proof.
    intros.

    apply if1_classical with (β:=⟦ pwd ↦ v_ p' ⟧
                                   ⟦ fromAcc ↦ v_ a' ⟧
                                   ⟦ amt ↦ m ⟧
                                   ⟦ toAcc ↦ a'' ⟧
                                   empty);
      [|repeat compose_simpl; auto].
    repeat hoare_simpl.

    match goal with
    | [|- _ ⊢ {pre: _ } _ {post: ¬ a_exp (?e1 ⩻ ?e2)}] =>
      eapply hoare_consequence2 with (A2':=a_exp (e1 ⩵ e2))
    end.
    apply transferBalanceChangeSpecification.
    apply eq_implies_not_lt.

  Qed.

  Lemma a_val_update_subst :
    forall (f : partial_map name a_val) a  b c d,
      ([d /s c](⟦ a ↦ b ⟧ f)) =
      (⟦ a ↦ ([d /s c] b) ⟧ ([d /s c] f)).
    apply (update_subst).
  Qed.

  Lemma a_val_empty_subst :
    forall c d,
      ([d /s c](@empty name a_val eqbName)) = (@empty name a_val eqbName).
    apply (empty_subst).
    * apply pwd.
    * apply (av_ (v_true)).
  Qed.

  Lemma bankTransferBalChange :
    forall a b b' bal p p' a' m a'',
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))) ∧
                 (a_class (e_ b') Bank) ∧
                 (∃x.[ (a♢ 0) calls (a_ b') ◌ transfer ⟨ ⟦ pwd ↦ a_ p' ⟧
                                                           ⟦ fromAcc ↦ a_ a' ⟧
                                                           ⟦ amt ↦ av_ m ⟧
                                                           ⟦ toAcc ↦ av_ a'' ⟧
                                                           empty  ⟩ ]))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ a_ p ⟧
                                                                        ⟦ fromAcc ↦ a_ a ⟧
                                                                        ⟦ amt ↦ a♢ 1 ⟧
                                                                        ⟦ toAcc ↦ a♢ 2 ⟧
                                                                        empty  ⟩ ]]]).
  Proof.
    intros.
    specX_cnf_l.

    apply if1_ex1;
      intros;
      subst_simpl.

    (* this should be done by subst_simpl, but for some unknown reason it doesn't. shrug.*)
    repeat rewrite a_val_update_subst;
      subst_simpl.
    repeat rewrite a_val_empty_subst;
      subst_simpl.

    repeat specX_cnf_r;
      repeat spec_auto.

    match goal with
    | [|- _ ⊢ _ ∧ ?A to1 _ onlyIf _] =>
      apply if1_conseq1 with (A1:=A);
        [repeat spec_auto|]
    end.

    match goal with
    | [|- _ ⊢ _ ∧ ?A to1 _ onlyIf _] =>
      apply if1_conseq1 with (A1:=A);
        [repeat spec_auto|]
    end.

    extract (v_ b) 0;
      subst.
    rewrite <- empty_subst with (c:=0)(d:=v_ b);
      [
       | apply pwd
       | apply (a_ a)].
    repeat rewrite <- a_val_update_subst.
    extract (v_ b) 0;
      subst.

    eapply if1_conseq.
      apply subst_eq;
      subst_simpl.

    match goal with
    | [|- _ ⊢ _ ∧ ?A to1 _ onlyIf _] =>
      apply if1_conseq1 with (A1:=A);
        [repeat spec_auto|]
    end.
    apply if1_conseq1.

    match goal with
    | [|- _ ⊢  _ to1 _ onlyIf _] =>
      eapply if1_conseq;
        [eapply if1_andI;
         [apply bankTransferBalChange'
         |apply if1_start]
        |
        |apply conseq_refl
        |]
    end.
    repeat apply and_assoc1.
    apply conseq_ex_and1;
      intros;
      subst_simpl.
    repeat apply and_assoc2.
    extract (v_ p') 0;
      subst;
      apply subst_eq;
      subst_simpl.
    extract (v_ a') 0;
      subst;
      apply subst_eq;
      subst_simpl.
    extract (v_ b') 0;
      subst;
      apply subst_eq;
      subst_simpl.
    repeat apply conseq_and2.
    apply conseq_ex2;
      exists a'';
      subst_simpl.
    apply conseq_ex2;
      exists m;
      subst_simpl.
    apply conseq_ex2;
      exists x;
      subst_simpl.
    apply conseq_refl.
  Qed.

  Lemma balanceChange :
    forall a b bal p,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))))
              to1 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyIf (∃x.[ ∃x.[ ∃x.[ (a♢ 0) calls (a_ b) ◌ transfer ⟨ ⟦ pwd ↦ a_ p ⟧
                                                                        ⟦ fromAcc ↦ a_ a ⟧
                                                                        ⟦ toAcc ↦ a♢ 1 ⟧
                                                                        ⟦ amt ↦ a♢ 2 ⟧
                                                                        empty  ⟩ ]]]).
  Proof.
    intros.
    apply if1_internal.

    * intros.

  Admitted.

  Lemma balanceChange' :
    forall a b bal p,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))))
              to (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyThrough (∃x.[ ¬ wrapped (a♢ 1) ∧
                                (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 0)))]).
  Proof.

  Admitted.

  Lemma passwordChange :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧
                      (a_exp (e_acc_f (e_ a) password ⩵ e_ p)))
                   to1 (¬ a_exp (e_acc_f (e_ a) password ⩵ e_ p))
                   onlyIf (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ a_ p ⟧ ⟦ newPwd ↦ a♢ 1 ⟧ empty  ⟩ ] ]).
  Proof.

  Admitted.

  (** Password Leaking **)
  (** add to paper: Sematic protection not syntactic protection **)

  Parameter passwordLeakAuthenticateSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                                (a_class (e_ a')  Account) ∧
                                (a_class (e_ a) Account) ∧
                                ¬ (a_false)}
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

    * apply passwordLeakAuthenticateSpecification.

    * repeat compose_simpl;
        auto.
  Qed.

  Parameter passwordLeakChangePasswordSpecification :
    forall a a' p β, BankMdl ⊢ {pre: (a_exp ((e_acc_f (e_ a') password) ⩵ (e_ p))) ∧
                                (a_class (e_ a')  Account) ∧
                                (a_class (e_ a) Account) ∧
                                ¬ (a_false)}
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

    * apply passwordLeakChangePasswordSpecification.

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
                              (∃x.[ (a♢ 0) calls (a_ l) ◌ ledgerTransfer ⟨ ⟦ amt ↦ (av_ m) ⟧
                                                                             ⟦ fromAcc ↦ (av_ f) ⟧
                                                                             ⟦ toAcc ↦ (av_ t) ⟧ empty⟩]))
                           to1 ¬ wrapped (a_ p)
                           onlyIf (a_false).
  Proof.
    intros.
    apply if1_wrapped with (β:=⟦ amt ↦ m ⟧ ⟦ fromAcc ↦ f ⟧ ⟦ toAcc ↦ t ⟧ empty).

    * apply passwordLeakLedgerTransferSpecification.

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

    * apply passwordLeakBankTransferSpecification.

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

      match goal with
      | [Ha : ⟦ ?C' ↦ ?CDef' ⟧_∈ _,
              Hb : ?m' ∈ c_meths _ |-_] =>
        destruct BankMdlMethods
          with (C:=C')(CDef:=CDef')(m:=m');
          auto;
          repeat andDestruct;
          subst
      end.

      ** match goal with
         | [|- _ ⊢ ?Aa ∧ (∃x.[ a♢ 0 calls ?b ◌ transfer ⟨ ?β ⟩ ]) to1 _ onlyIf _] =>
           apply if1_conseq1 with
               (A1:= Aa ∧ ∃x.[∃x.[∃x.[∃x.[∃x.[a♢ 0 calls b ◌ transfer ⟨ ⟦ pwd ↦ a♢ 1 ⟧
                                                                          ⟦ fromAcc ↦ a♢ 2 ⟧
                                                                          ⟦ toAcc ↦ a♢ 3 ⟧
                                                                          ⟦ amt ↦ a♢ 4⟧ empty⟩]]]]])
         end.

         *** repeat spec_auto.
             apply conseq_trans with (A2:=(a_class (e_ α) Bank) ∧ (∃x.[ a♢ 0 calls a_ α ◌ transfer ⟨ β ⟩])).

             **** repeat spec_auto.
                  apply conseq_and1.
                  repeat spec_auto.

             **** apply bankTransferParameters.

         *** repeat (intro_ex_if1;
                     subst_simpl).
             apply if1_conseq1
               with (A1:=(((a_exp (e_acc_f (e_ a) password ⩵ (e_ p)) ∧
                            a_class (e_ a) Account ∧
                            wrapped (a_ p) ∧
                            a_class (e_ α) Bank) ∧
                           (∃x.[a♢ 0 calls a_ α ◌ transfer ⟨ ⟦ pwd ↦ av_ v2 ⟧
                                                               ⟦ fromAcc ↦ av_ v1 ⟧
                                                               ⟦ toAcc ↦ av_ v0 ⟧
                                                               ⟦ amt ↦ av_ v ⟧ empty⟩])))).
             **** repeat apply and_assoc2;
                    repeat spec_auto;
                    try solve [ apply conseq_and2, conseq_and1; repeat spec_auto].
                  ***** apply conseq_and2, conseq_and2; repeat spec_auto.
                  ***** repeat apply conseq_and2; spec_auto.

             **** apply bankTransferLeak.

      ** disj_split;
           andDestruct;
           subst.

         *** repeat apply if1_and_assoc1.
             match goal with
             | [|- _ ⊢ _ ∧ (_ ∧ ((a_class (e_ ?l) Ledger) ∧ (∃x.[ a♢ 0 calls a_ ?l ◌ ledgerTransfer ⟨ _ ⟩]))) to1 _ onlyIf _] =>
               eapply if1_conseq1;
                 [eapply and_consequence2;
                  eapply and_consequence2;
                  apply ledgerTransferParameters
                 |]
             end.
             


             eapply if1_conseq1.
             apply and_consequence2.
             apply and_consequence2.
             apply conseq_ex1;
               intros;
               subst_simpl.
             apply conseq_ex1;
               intros;
               subst_simpl.
             apply conseq_ex1;
               intros;
               subst_simpl.
             apply conseq_refl.

             apply if1_classical
               with (β:=β).


  Qed.

  (** BankSpec **)

  Lemma necessityBankSpec :
    forall a b bal p, BankMdl ⊢ (a_class (e_ a) Account ∧ 
                            a_class (e_ b) Bank ∧
                            (a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩵ (e_int bal))) ∧
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
        apply and_distributive_trans_2.
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

      + apply balanceChange'.

    - apply if_conseq3 with (A3:= ¬ wrapped (a_ p) ∨ ¬ wrapped (a_ p));
        [apply or_dumb2|].
      apply if_orI2.

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
               **** repeat apply conseq_and1;
                      apply conseq_refl.
               **** apply conseq_and1, conseq_and2, conseq_refl.

           *** apply ot_conseq2 with
                   (A2:=¬ ((a_class (e_ a) Account) ∧ (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)) ∧ wrapped (a_ p)))).

               **** apply conseq_trans
                      with (A2:=(¬ a_class (e_ a) Account) ∨
                                (¬ (a_exp (e_acc_f (e_ a) password ⩵ (e_ p)))) ∨
                                ¬ wrapped (a_ p)).
                    ***** apply or_r; spec_auto.
                    ***** admit. (* negation distribution *)

               **** apply ot_changes.
                    apply if1_conseq2
                      with (A2:=¬ wrapped (a_ p)).
                    ***** admit.
                    ***** apply passwordLeak.

      * (* Case B *)
        apply if_trans with (∃x.[ ∃x.[ (a♢ 0) calls (a_ a) ◌ changePassword ⟨ ⟦ pwd ↦ a_ p ⟧ ⟦ newPwd ↦ a♢ 1 ⟧ empty  ⟩ ] ]).

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
                    ***** apply or_r, conseq_refl.

                    ***** apply neg_distr_and_2.

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

                    ***** apply passwordChange.
                    ***** match goal with
                          | [|- _ ⊢ ?Aa ∧ _ to1 _ onlyIf _] =>
                            apply if1_conseq1 with (A1:=Aa);
                              [repeat spec_auto
                              |apply change_class_absurd]
                          end.

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

                    ****** (repeat apply conseq_and1;
                           apply conseq_refl).
                    ****** (apply conseq_and1, conseq_and2, conseq_refl).

                    ***** apply ot_if.
                    apply passwordLeak.

  Qed.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End BankAccount.
