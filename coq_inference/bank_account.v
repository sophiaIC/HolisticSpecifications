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
              {post: (¬ a_exp (e_acc_g (e_ b) getBalance (e_ a) ⩻ (e_int bal)))}.

  Lemma eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).
  Admitted.

  Lemma lt_implies_not_eq :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩻ e2)) ⊇ (¬ a_exp (e1 ⩵ e2)).
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
    forall M A1 A2 A, M ⊢ (A1 ∧ A2) ⊇ A ->
                 M ⊢ (A2 ∧ A1) ⊇ A.
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

  Lemma conseq_and :
    forall M A A1 A2,  M ⊢ A ⊇ A1 ->
                       M ⊢ A ⊇ A2 ->
                       M ⊢ A ⊇ A1 ∧ A2.
  Admitted.

  (*
    I *think* conseq_ex is true based on the natural deduction inference rule for existentials:

                      -------           ----------
                      y term            [y / x] A1
                                 .
                                 .
                                 .
                                 .
                                 .
      ∃x.[A1]                   A2
    ---------------------------------------------------
                          A2

   The equivalent version for '⊇' would conseq_ex
   *)
  Lemma conseq_ex :
    forall M A1 A2, (forall x, M ⊢ [x /s 0] A1 ⊇ A2) ->
                    M ⊢ (∃x.[A1]) ⊇ A2.
  Admitted.

  Lemma subst_eq :
    forall M x y z A1 A2, M ⊢ [y /s z] A1 ⊇ A2 ->
                     M ⊢ ([x /s z](a_exp (e♢ z ⩵ e_val y))) ∧ ([x /s z]A1) ⊇ A2.
  Admitted.

  Lemma caller_unique :
    forall M v v' a a' m m' β β',
      M ⊢ (av_ v) calls a ◌ m ⟨ β ⟩ ∧ (av_ v') calls a' ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma recv_unique :
    forall M v v' a a' m m' β β',
      M ⊢ a calls (av_ v) ◌ m ⟨ β ⟩ ∧ a' calls (av_ v) ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma param_unique :
    forall M a1 a1' a2 a2' m m' x v v' β β',
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ (av_ v) ⟧ β ⟩ ∧ a1' calls a2' ◌ m' ⟨ ⟦ x ↦ (av_ v') ⟧ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma neg_distr_and_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∧ A2) ⊇ ¬ A1 ∨ ¬ A2.
  Admitted.

  Lemma neg_distr_and_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∨ ¬ A2 ⊇ ¬ (A1 ∧ A2).
  Admitted.

  Lemma or_l :
    forall M A A1 A2, M ⊢ A ⊇ A1 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_r :
    forall M A A1 A2, M ⊢ A ⊇ A2 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_lr :
    forall M A1 A2 A, M ⊢ A1 ⊇ A ->
                 M ⊢ A2 ⊇ A ->
                 M ⊢ (A1 ∨ A2) ⊇ A.
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
    |[|- _ ⊢ _ ⊇ _ ∧ _] =>
     apply conseq_and
    end.

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

  Lemma if1_start :
    forall M A1 A2, M ⊢ A1 to1 A2 onlyIf A1.
  Proof.
    auto with inference_db.
  Qed.

  Hint Resolve if1_start : inference_db.

  Lemma if1_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                           M ⊢ A1 to1 A2 onlyIf A3 ->
                           M ⊢ A1' to1 A2 onlyIf A3.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if1_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to1 A2 onlyIf A3 ->
                           M ⊢ A1 to1 A2' onlyIf A3.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if1_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to1 A2 onlyIf A3 ->
                           M ⊢ A1 to1 A2 onlyIf A3'.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve if1_conseq1 if1_conseq2 if1_conseq3 : inference_db.

  Lemma if_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1' to A2 onlyIf A3.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1 to A2' onlyIf A3.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1 to A2 onlyIf A3'.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve if_conseq1 if_conseq2 if_conseq3 : inference_db.

  Lemma ot_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1' to A2 onlyThrough A3.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma ot_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1 to A2' onlyThrough A3.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma ot_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1 to A2 onlyThrough A3'.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve ot_conseq1 ot_conseq2 ot_conseq3 : inference_db.

  Lemma if1_start_conseq :
    forall M A1 A2 A1', M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 to1 A2 onlyIf A1'.
  Proof.
    intros.
    eapply if1_conseq3;
      eauto with inference_db.
  Qed.

  Hint Resolve if1_start if1_start_conseq : inference_db.

  Lemma if_start_conseq :
    forall M A1 A2 A1', M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 to A2 onlyIf A1'.
  Proof.
    intros.
    eapply if_conseq3;
      eauto with inference_db.
  Qed.

  Hint Resolve if_start_conseq : inference_db.

  Lemma if1_andE :
    forall M A1 A2 A A', M ⊢ A1 to1 A2 onlyIf A ∧ A' ->
                         M ⊢ A1 to1 A2 onlyIf A.
  Proof.
    intros.
    eapply if1_conseq with (A':=A ∧ A');
      [ eauto
      | apply conseq_refl
      | apply conseq_refl
      | apply conseq_and1, conseq_refl].
  Qed.

  Lemma compose_update :
    forall {A B C : Type}`{Eq A} (f : B -> C) (a : A) (b : B) (g : partial_map A B),
      (fun b => Some (f b)) ∘ (⟦ a ↦ b ⟧ g) = ⟦ a ↦ f b ⟧ (fun b => Some (f b)) ∘ g.
  Proof.
    intros.
    simpl.
    apply functional_extensionality;
      intros.
    repeat map_rewrite.
    destruct (eqb x a);
      auto.
  Qed.

  Lemma compose_empty :
    forall {A B C}`{Eq A} (f : B -> C),
      (fun b => Some (f b)) ∘ empty = empty.
  Proof.
    intros;
      auto.
  Qed.

  Ltac compose_simpl :=
    match goal with
    | [|- context[(fun _ => Some (?f _)) ∘ ⟦ _ ↦ _ ⟧ _]] =>
      rewrite compose_update
    | [H : context[(fun _ => Some (?f _)) ∘ ⟦ _ ↦ _ ⟧ _] |- _] =>
      rewrite compose_update in H
    | [|- context[(fun _ => Some (?f _)) ∘ empty]] =>
      rewrite compose_empty
    | [H : context[(fun _ => Some (?f _)) ∘ empty] |- _] =>
      rewrite compose_empty in H
    end.

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

    apply transferBalanceChangeSpecification.

  (*    apply hoare_consequence1 with
        (A1':=(a_class (e_addr a) Account) ∧
              (a_class (e_addr b) Bank) ∧
              (a_exp (e_acc_g (e_addr b) getBalance (e_addr a) ⩵ (e_int bal))) ∧
              (a_exp (e_acc_f (e_addr a) password ⩵ (e_addr p))) ∧
              (a_class (e_addr b') Bank) ∧
              ¬ (a_exp (e_ p' ⩵ e_ p) ∧
                 a_exp (e_ a' ⩵ e_ a) ∧
                 a_exp (e_ b' ⩵ e_ b))).

      - apply transferBalanceChangeSpecification.

    - repeat spec_auto.
      apply conseq_and2.
      match goal with
      | [|- _ ⊢ _ ⊇ ¬ (?Aa ∧ ?Ab)] =>
        apply consequence_transitivity with (A2:= ¬ Aa ∨ ¬ Ab)
      end.
      + apply or_l, conseq_refl.

      + apply neg_distr_and_2.*)

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
    match goal with
    | [|- _ ⊢  _ to1 _ onlyIf _] =>
      eapply if1_conseq;
        [apply if1_start
        |apply conseq_refl
        |apply conseq_refl
        |]
    end.
    repeat spec_auto.
  Admitted.

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

  Admitted.

  Lemma balanceChange' :
    forall a b bal p,
      BankMdl ⊢ ((a_class (e_ a) Account) ∧
                 (a_class (e_ b) Bank) ∧
                 (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩵ (e_int bal))) ∧
                 (a_exp ((e_acc_f (e_ a) password) ⩵ (e_ p))))
              to (a_exp ((e_acc_g (e_ b) getBalance (e_ a)) ⩻ (e_int bal)))
              onlyThrough (∃x.[ ¬ wrapped (a♢ 0) ∧
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

  Lemma passwordLeak :
    forall a p, BankMdl ⊢ (a_class (e_ a) Account ∧
                      (a_exp (e_acc_f (e_ a) password ⩵ e_ p) ∧
                       (wrapped (a_ p))))
                   to (¬ (wrapped (a_ p)))
                   onlyIf (a_exp (e_false)).
  Proof.

  Admitted.

  Lemma or_dumb1 :
    forall M A, M ⊢ A ⊇ A ∨ A.
  Proof.
  Admitted.

  Lemma or_dumb2 :
    forall M A, M ⊢ A ∨ A ⊇ A.
  Proof.
  Admitted.

  Lemma conseq_excluded_middle :
    forall M A, M ⊢ (a_exp (e_true)) ⊇ (A ∨ ¬ A).
  Admitted.

  Lemma change_class_absurd :
    forall M x C, M ⊢ (a_class (e_ x) C) to1 ¬ (a_class (e_ x) C) onlyIf (a_false).
  Admitted.

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
                                      (a_exp (e_acc_f (e_ a) password ⩵ (e♢ 0)))]).
      + apply conseq_ex;
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

        * repeat match goal with
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
          apply subst_eq.


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

           *** apply ot_if.
               apply passwordLeak.

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

           *** admit.

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
