Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import exp.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import hoare.
Require Import always.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Definition changes (a : a_val)(f : fld) :=
  match a with
  | a♢ m =>
    ∃[x⦂ a_Obj]∙(((ex_acc_f (e♢ (S m)) f) ⩶ (e♢ 0))
                 ∧
                 (a_next (∃[x⦂ a_Val]∙ ((ex_acc_f (e♢ (S (S m))) f) ⩶ (e♢ 0)
                                        ∧
                                        ((e♢ 0) ⩶̸ (e♢ 1))))))
  | a_ α =>
    ∃[x⦂ a_Obj]∙(((ex_acc_f (e_ α) f) ⩶ (e♢ 0))
                 ∧
                 (a_next (∃[x⦂ a_Val]∙ ((ex_acc_f (e_ α) f) ⩶ (e♢ 0)
                                        ∧
                                        ((e♢ 0) ⩶̸ (e♢ 1))))))
  | _ => (a_expr (ex_false))
  end.

Module BankAccount.

  (** #<h3>#Definitions#</h3># *)

  Definition Bank := classID 1.

  Definition Account := classID 2.

  Definition balance := fieldID 0.

  Definition myBank := fieldID 1.

  Definition deposit := methID 0.

  Definition src := bnd 1.

  Definition amt := bnd 2.

  Definition srcBank := bnd 3.

  Definition srcBalance := bnd 4.

  Definition thisBank := bnd 5.

  Definition thisBalance := bnd 6.

  Definition x := bnd 7.

  Definition tmp := bnd 8.

  (**
     #<h3>#Bank Account Definition#</h3>#
   *)

  Definition depositBody := s_stmts
                              (x ≔′ e_null)
                              (s_stmts ((r_ thisBank) ≔ (this ◌ myBank))
                                       (s_stmts ((r_ thisBalance) ≔ (this ◌ balance))
                                                (s_stmts ((r_ srcBank) ≔ (src ◌ myBank))
                                                         (s_stmts ((r_ srcBalance) ≔ (src ◌ balance))
                                                                  (s_stmts
                                                                     (s_if ((e_int 0 ⩻ e_var amt)
                                                                              ⩑
                                                                              (e_var srcBank ⩵ e_var thisBank)
                                                                              ⩑
                                                                              (e_var amt ⩻ e_var srcBalance))
                                                                           (s_stmts
                                                                              (tmp ≔′ (e_plus (e_var thisBalance) (e_var amt)))
                                                                              (s_stmts
                                                                                 ((r_ thisBalance ≔ (r_ tmp)))
                                                                                 (s_stmts
                                                                                    (tmp ≔′ (e_minus (e_var srcBalance) (e_var amt)))
                                                                                    ((r_ srcBalance ≔ (r_ tmp))))))
                                                                           (s_rtrn x))
                                                                     (s_rtrn x)))))).

  Definition BankDef := clazz Bank
                              nil
                              nil
                              empty
                              empty.

  Definition AccountDef := clazz Account
                                 (myBank :: balance :: nil)
                                 nil
                                 (update
                                    deposit (src :: amt :: nil, depositBody)
                                    empty)
                                 empty.

  Definition MyModule := update
                           Account AccountDef
                           (update
                              Bank BankDef
                              empty).

  Definition BankAccountPrivateBody := (((e_hole 0) ⩵ (e_var this))
                                          ⩒
                                          ((e_hole 0) ⩵ (e_acc_f (e_var this) myBank))).

  Parameter deposit_into_account :
    forall M σ0 σ α1 α2 α3 i bal1 bal2, MyModule ⦂ M ◎ σ0 … ̱ ⊨
                                            {pre: (a_expr ((ex_int 0) ⩻′ (ex_val i))
                                                   ∧
                                                   ((ex_acc_f (e_ α1) myBank) ⩶  ex_acc_f (e_ α2) myBank)
                                                   ∧
                                                   ((ex_acc_f (e_ α1) balance) ⩶  (ex_val bal1))
                                                   ∧
                                                   ((ex_acc_f (e_ α2) balance) ⩶  (ex_val bal2))
                                                   ∧
                                                   a_expr ((ex_val i) ⩻′ ex_acc_f (e_ α2) balance)
                                                   ∧
                                                   ((a_ α3) calls (a_ α1) ▸ (am_ deposit)
                                                            ⟨update amt (av_bnd i) (update src (a_ α2) empty)⟩))}
                                            σ
                                            {post: (ex_acc_f (e_ α1) balance) ⩶  (ex_plus (ex_val bal1) (ex_val i))
                                                   ∧
                                                   ((ex_acc_f (e_ α2) balance) ⩶  (ex_minus (ex_val bal2) (ex_val i)))}.

  Lemma external_step_does_not_change_balance :
    forall M σ0 σ α bal, external_step MyModule M σ ->
                    MyModule ⦂ M ◎ σ0 … ̱ ⊨
                             {pre: (a_ α) internal ∧
                                   ((ex_acc_f (e_ α) balance) ⩶ (ex_val bal))}
                             σ
                             {post: (ex_acc_f (e_ α) balance) ⩶ (ex_val bal)}.
  Proof.
    intros.
    apply external_step_does_not_mutate_internal_fields;
      auto.
  Qed.

  Lemma internal_step_is_deposit :
    forall M σ, internal_step MyModule M σ ->
           forall σ0, exists x y β, MyModule ⦂ M ◎ σ0 … σ ⊨ (x calls y ▸ (am_ deposit) ⟨ β ⟩).
  Proof.
    
  Qed.

  Definition HolisticSpec :=
    (∀[x⦂ a_Obj]∙
      (((a_class (a♢ 0) Account)
        ∧
        (changes (a♢ 0) balance))
         ⟶
         (∃[x⦂ a_Obj]∙
             ∃[x⦂ a_Obj]∙
                ∃[x⦂ a_Val]∙
                 (((a♢ 2) calls (a♢ 3) ▸ (am_ deposit) ⟨ update
                                                           src (a♢ 1)
                                                           (update
                                                              amt (a♢ 0)
                                                              empty) ⟩)
                  ∨
                  ((a♢ 2) calls (a♢ 1) ▸ (am_ deposit) ⟨ update
                                                           src (a♢ 3)
                                                           (update
                                                              amt (a♢ 0)
                                                              empty) ⟩)
    )))).

  Lemma bank_account_sat :
    MyModule ⊨m HolisticSpec.
  Proof.
    unfold mdl_sat, HolisticSpec;
      intros;
      a_intros;
      a_prop.

    a_destruct;
      simpl in *;
      andDestruct;
      a_prop.

    a_exists α0 α0 v_true;
      eauto with chainmail_db.
    a_prop.



    (* if balance changes, then there is deposit was called *)

    (* if deposit was called, and the balance of α changed, then
       α was either the receiver or the src *)
    
  Qed.


End BankAccount.
