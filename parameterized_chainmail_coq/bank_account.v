Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import chainmail.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module BankAccount(L : LanguageDef).

  Import L.
  Module L_Chainmail := Chainmail(L).
  Import L_Chainmail.
  Import L_Semantics.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.

  (** #<h2>#Variables#</h2>#*)

  Definition src := n_ 0.
  Definition amt := n_ 1.

  (** #<h2>#Account Class#</h2># *)

  Definition Account := classID 1.

  Definition deposit := methID 0.

  Parameter deposit_body : continuation.

  Definition AccountDef := clazz Account
                                 (update deposit deposit_body empty)
                                 empty.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End BankAccount.
