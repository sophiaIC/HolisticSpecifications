Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import List.
Require Import chainmail.

Module Inference(L : LanguageDef).

  Import L.
  Module L_Semantics := AbstractOperationalSemantics(L).
  Import L_Semantics.
  Module L_Chainmail := Chainmail(L).
  Import L_Chainmail.

  Reserved Notation "M '⊢' A1 'to' A2 'onlyIf' A3" (at level 40).
  Reserved Notation "M '⊢' A1 'to' A2 'onlyThrough' A3" (at level 40).
  Reserved Notation "M '⊢' A1 'to1' A2 'onlyIf' A3" (at level 40).

  Open Scope chainmail_scope.
  Open Scope reduce_scope.

  Lemma caller_ext :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 external.
    Admitted.

  Lemma calls_recv :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 access α2.
  Admitted.

  Lemma class_internal :
    forall M α C, C ∈ M -> M ⊢ a_class (e_addr α) C ⊇ (a_ α) internal.
  Admitted.

  Definition wrapped := (fun α => ∀x.[ (a♢ 0) internal ∨ ¬ (a♢ 0) access α]).

  Lemma inside_wrapped :
    forall M α C Def, ⟦ C ↦ Def ⟧_∈ M ->
                 annot Def = inside ->
                 M ⊢ a_class (e_addr α) C ⊇ wrapped (a_ α).
  Admitted.

  Lemma fld_type :
    forall M e C CDef f D, ⟦ C ↦ CDef ⟧_∈ M ->
                      ⟦ f ↦ D ⟧_∈ c_fields CDef ->
                      M ⊢ a_class e C ⊇ a_class ((e_acc_f e f)) D.
  Admitted.

  Inductive only_if : mdl -> asrt -> asrt -> asrt -> Prop :=
  | if_start  : forall M A1 A2, M ⊢ A1 to A2 onlyIf A1
  | if_conseq : forall M A1 A1' A2 A2' A A', M ⊢ A1' to A2' onlyIf A' ->
                                        M ⊢ A1 ⊇ A1' ->
                                        M ⊢ A2 ⊇ A2' ->
                                        M ⊢ A' ⊇ A ->
                                        M ⊢ A1 to A2 onlyIf A
  | if_orI1   : forall M A1 A1' A2 A A', M ⊢ A1 to A2 onlyIf A ->
                                    M ⊢ A1' to A2 onlyIf A' ->
                                    M ⊢ A1 ∨ A1' to A2 onlyIf A ∨ A'
  | if_orI2   : forall M A1 A2 A2' A A', M ⊢ A1 to A2 onlyIf A ->
                                    M ⊢ A1 to A2' onlyIf A' ->
                                    M ⊢ A1 to A2 ∨ A2' onlyIf A ∨ A'
  | if_orE    : forall M A1 A2 A A', M ⊢ A1 to A2 onlyIf A ∨ A' ->
                                M ⊢ A' to A2 onlyThrough a_exp (e_false) ->
                                M ⊢ A1 to A2 onlyIf A
  | if_trans  : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A' ->
                                M ⊢ A1 to A' onlyIf A ->
                                M ⊢ A1 to A2 onlyIf A

  where
  "M '⊢' A1 'to' A2 'onlyIf' A3" := (only_if M A1 A2 A3)

  with only_through : mdl -> asrt -> asrt -> asrt -> Prop :=
  | ot_end      : forall M A1 A2, M ⊢ A1 to A2 onlyThrough A2
  | ot_if       : forall M A1 A2 A, M ⊢ A1 to A2 onlyIf A ->
                               M ⊢ A1 to A2 onlyThrough A
  | ot_changes  : forall M A A', M ⊢ A to1 ¬ A onlyIf A' ->
                            M ⊢ A to ¬ A onlyThrough A'
  | ot_conseq   : forall M A1 A1' A2 A2' A A', M ⊢ A1' to A2' onlyThrough A' ->
                                          M ⊢ A1 ⊇ A1' ->
                                          M ⊢ A2 ⊇ A2' ->
                                          M ⊢ A' ⊇ A ->
                                          M ⊢ A1 to A2 onlyThrough A
  | ot_orI1     : forall M A1 A1' A2 A A', M ⊢ A1 to A2 onlyThrough A ->
                                      M ⊢ A1' to A2 onlyThrough A' ->
                                      M ⊢ A1 ∨ A1' to A2 onlyThrough A ∨ A'
  | ot_orI2     : forall M A1 A2 A2' A A', M ⊢ A1 to A2 onlyThrough A ->
                                      M ⊢ A1 to A2' onlyThrough A' ->
                                      M ⊢ A1 to A2 ∨ A2 onlyThrough A ∨ A'
  | ot_orE1     : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A ∨ A' ->
                                  M ⊢ A1 to A' onlyThrough a_exp (e_false) ->
                                  M ⊢ A1 to A2 onlyThrough A
  | ot_orE2     : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A ∨ A' ->
                                  M ⊢ A' to A2 onlyThrough a_exp (e_false) ->
                                  M ⊢ A1 to A2 onlyThrough A
  | ot_trans1   : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A' ->
                                  M ⊢ A1 to A' onlyThrough A ->
                                  M ⊢ A1 to A2 onlyThrough A
  | ot_trans2   : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A' ->
                                  M ⊢ A' to A2 onlyThrough A ->
                                  M ⊢ A1 to A2 onlyThrough A
  | ot_inv      : forall M A1 A2 A3 A, M ⊢ A to ¬ A onlyThrough a_exp (e_false) ->
                                  M ⊢ A1 to A2 onlyThrough A3 ->
                                  M ⊢ A1 ∧ A to A2 onlyThrough A3 ∧ A

  where
  "M '⊢' A1 'to' A2 'onlyThrough' A3" := (only_through M A1 A2 A3)

  with only_if1 : mdl -> asrt -> asrt -> asrt -> Prop :=
  | if1_if : forall M A1 A2 A3, M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1 to1 A2 onlyIf A3
  | if1_conseq : forall M A1 A1' A2 A2' A A', M ⊢ A1' to1 A2' onlyIf A' ->
                                         M ⊢ A1 ⊇ A1' ->
                                         M ⊢ A2 ⊇ A2' ->
                                         M ⊢ A' ⊇ A ->
                                         M ⊢ A1 to1 A2 onlyIf A
  | if1_orI1  : forall M A1 A1' A2 A A', M ⊢ A1 to A2 onlyIf A ->
                                    M ⊢ A1' to A2 onlyIf A' ->
                                    M ⊢ A1 ∨ A1' to1 A2 onlyIf A ∨ A'
  | if1_orI2  : forall M A1 A2 A2' A A', M ⊢ A1 to1 A2 onlyIf A ->
                                    M ⊢ A1 to1 A2' onlyIf A' ->
                                    M ⊢ A1 to1 A2 ∨ A2' onlyIf A ∨ A'
  | if1_orE   : forall M A1 A2 A A', M ⊢ A1 to1 A2 onlyIf A ∨ A' ->
                                M ⊢ A' to A2 onlyThrough a_exp (e_false) ->
                                M ⊢ A1 to1 A2 onlyIf A

  where
  "M '⊢' A1 'to1' A2 'onlyIf' A3" := (only_if1 M A1 A2 A3).



End Inference.
