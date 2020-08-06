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

Definition changes (a : a_var)(f : fld) :=
  match a with
  | a♢ m =>
    ∃x∙(((ex_acc_f (e♢ (S m)) f) ⩶ (e♢ 0))
        ∧
        (a_will (∃x∙ ((ex_acc_f (e♢ (S (S m))) f) ⩶ (e♢ 0)
                      ∧
                      ((e♢ 0) ⩶̸ (e♢ 1))))))
  | a_ α =>
    ∃x∙(((ex_acc_f (e_ α) f) ⩶ (e♢ 0))
        ∧
        (a_will (∃x∙ ((ex_acc_f (e_ α) f) ⩶ (e♢ 0)
                      ∧
                      ((e♢ 0) ⩶̸ (e♢ 1))))))
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


  Definition HolisticSpec :=
    (∀x∙ (((a_class (a♢ 0) Account)
           ∧
           (changes (a♢ 0) balance))
            ⟶
            (∃x∙ (((a♢ 0) calls (a♢ 1) ▸ (am_ deposit) ⟨ update
                                                           src (a♢ 0)
                                                           (update
                                                              amt (a♢ 0)
                                                              empty) ⟩)
                  ∨
                  ((a♢ 0) calls (a♢ 0) ▸ (am_ deposit) ⟨ update
                                                           src (a♢ 1)
                                                           (update
                                                              amt (a♢ 0)
                                                              empty) ⟩))))).


End BankAccount.