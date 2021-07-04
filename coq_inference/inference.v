Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import List.
Require Import chainmail.
Require Import hoare.

Module Inference(L : LanguageDef).

  Export L.
  Module L_Hoare := Hoare(L).
  Export L_Hoare.
  (*)Module L_Chainmail := Chainmail(L).
  Import L_Chainmail.*)

  Open Scope chainmail_scope.
  Open Scope reduce_scope.
  Open Scope hoare_scope.
  Declare Scope inference_scope.

  Reserved Notation "M '⊢' A1 'to' A2 'onlyIf' A3" (at level 40).
  Reserved Notation "M '⊢' A1 'to' A2 'onlyThrough' A3" (at level 40).
  Reserved Notation "M '⊢' A1 'to1' A2 'onlyIf' A3" (at level 40).

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

  Lemma recv_not_wrapped :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (α2).
  Admitted.

  Lemma inside_wrapped :
    forall M α C Def, ⟦ C ↦ Def ⟧_∈ M ->
                      annot Def = inside ->
                      M ⊢ a_class (e_addr α) C ⊇ wrapped (a_ α).
  Admitted.

  Lemma fld_type :
    forall M e C CDef f D, ⟦ C ↦ CDef ⟧_∈ M ->
                           ⟦ f ↦ (t_cls D) ⟧_∈ c_fields CDef ->
                           M ⊢ a_class e C ⊇ a_class ((e_acc_f e f)) D.
  Admitted.

  Lemma absurd :
    forall M A, M ⊢ (a_exp (e_false)) ⊇ A.
  Admitted.

  Lemma conseq_refl :
    forall M A, M ⊢ A ⊇ A.
  Admitted.

  Lemma neg_false :
    forall M A, M ⊢ (A ∧ ¬ A) ⊇ (a_exp (e_false)).
  Admitted.

  Lemma consequence_transitivity :
    forall M A1 A2 A3, M ⊢ A1 ⊇ A2 ->
                       M ⊢ A2 ⊇ A3 ->
                       M ⊢ A1 ⊇ A3.
  Admitted.

  Inductive intrnl : mdl -> asrt -> exp -> Prop :=
  | i_int : forall M A i, intrnl M A (e_int i)
  | i_true : forall M A, intrnl M A (e_true)
  | i_false : forall M A, intrnl M A (e_false)
  | i_null : forall M A, intrnl M A (e_null)
  | i_obj : forall M A α C, M ⊢ A ⊇ (a_class (e_addr α) C) ->
                            C ∈ M ->
                            intrnl M A (e_addr α)
(*  | i_var : forall M A x C, M ⊢ A ⊇ (a_class (e_var x) C) ->
                            C ∈ M ->
                            intrnl M A (e_var x)*)
  | i_fld : forall M A e C CDef f D, intrnl M A e ->
                                     M ⊢ A ⊇ (a_class e C) ->
                                     ⟦ C ↦ CDef ⟧_∈ M ->
                                     ⟦ f ↦ (t_cls D) ⟧_∈ c_fields CDef ->
                                     D ∈ M ->
                                     intrnl M A (e_acc_f e f)
  | i_ghost : forall M A e1 e2 C CDef e g, intrnl M A e1 ->
                                           intrnl M A e2 ->
                                           M ⊢ A ⊇ (a_class e1 C) ->
                                           ⟦ C ↦ CDef ⟧_∈ M ->
                                           ⟦ g ↦ (int, e) ⟧_∈ c_g_fields CDef ->
                                           intrnl M A (e_acc_g e1 g e2).

  Hint Constructors intrnl : inference_db.

  Inductive enc : mdl -> asrt -> asrt -> Prop :=
  | enc_intrnl : forall M A e, intrnl M A e ->
                               enc M A (a_exp e)
  | enc_field : forall M A e f, intrnl M A e ->
                                enc M A (a_exp (e_acc_f e f))
  | enc_int_acc : forall M A α1 α2, M ⊢ A ⊇ (α1 internal) ->
                                    enc M A (α1 access α2)
  | enc_wrapped1 : forall M A α, enc M A (wrapped α)
  | enc_wrapped2 : forall M A α1 α2, M ⊢ A ⊇ (wrapped α2) ->
                                     enc M A (¬ α1 access α2)
  | enc_conseq : forall M A1 A2 A, M ⊢ A1 ⊇ A2 ->
                                   enc M A2 A ->
                                   enc M A1 A.

  Hint Constructors enc : inference_db.

  Inductive only_if : mdl -> asrt -> asrt -> asrt -> Prop :=
  | if_start  : forall M A1 A2 A, M ⊢ A1 ⊇ A ->
                                  M ⊢ A1 to A2 onlyIf A
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
  | if_andI : forall M A1 A2 A A', M ⊢ A1 to A2 onlyIf A ->
                                   M ⊢ A1 to A2 onlyIf A' ->
                                   M ⊢ A1 to A2 onlyIf A ∧ A'
  | if_trans  : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A' ->
                                     M ⊢ A1 to A' onlyIf A ->
                                     M ⊢ A1 to A2 onlyIf A

  where
  "M '⊢' A1 'to' A2 'onlyIf' A3" := (only_if M A1 A2 A3)

  with only_through : mdl -> asrt -> asrt -> asrt -> Prop :=
  | ot_end      : forall M A1 A2, M ⊢ A1 to A2 onlyThrough A2
  | ot_if       : forall M A1 A2 A, M ⊢ A1 to A2 onlyIf A ->
                                    M ⊢ A1 to A2 onlyThrough A
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
                                  M ⊢ A1 ⊇ ¬ A' ->
                                  M ⊢ A1 to A' onlyThrough a_exp (e_false) ->
                                  M ⊢ A1 to A2 onlyThrough A
  | ot_orE2     : forall M A1 A2 A A', M ⊢ A1 to A2 onlyThrough A ∨ A' ->
                                  M ⊢ A2 ⊇ ¬ A' ->
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
  | if1_classical : forall M P1 α C m β β' P2 P,
      M ⊢ {pre: ((a_class (e_addr α) C) ∧ P1 ∧ ¬ P) } (m_call α m β) {post: ¬ P2} ->
      β' = (fun v => Some (av_ v)) ∘ β  ->
      M ⊢ (P1 ∧ (a_class (e_addr α) C) ∧ (∃x.[ (a♢ 0) calls (a_ α) ◌ m ⟨ β' ⟩])) to1 P2 onlyIf P
  | if1_wrapped : forall M α C P m β α',
      M ⊢ {pre: (a_class (e_addr α) C) ∧ ¬ P } (m_call α m β) {post: a_exp ((e♢ 0) ⩵̸ (e_ α'))} ->
      M ⊢ (wrapped (a_ α') ∧ (a_class (e_ α) C) ∧ (∃x.[ (a♢ 0) calls (a_ α) ◌ m ⟨ (fun v => Some (av_ v)) ∘ β ⟩ ]))
        to1 (¬ (wrapped (a_ α'))) onlyIf P
  | if1_internal : forall M A1 A2 A3,
      (forall C CDef m α β, ⟦ C ↦ CDef ⟧_∈ M ->
                            m ∈ c_meths CDef ->
                            M ⊢ (A1 ∧ (a_class (e_ α) C) ∧ ∃x.[ (a♢ 0) calls (a_ α) ◌ m ⟨ β ⟩]) to1 A2 onlyIf A3) ->
      M ⊢ A1 to1 A2 onlyIf A3
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
  | if1_andI : forall M A1 A2 A A', M ⊢ A1 to1 A2 onlyIf A ->
                                    M ⊢ A1 to1 A2 onlyIf A' ->
                                    M ⊢ A1 to1 A2 onlyIf A ∧ A'

  where
  "M '⊢' A1 'to1' A2 'onlyIf' A3" := (only_if1 M A1 A2 A3).

  Hint Constructors only_through only_if only_if1 : inference_db.


  Scheme onlyThrough_mutind := Induction for only_through Sort Prop
    with onlyIf_mutind := Induction for only_if Sort Prop
    with onlyIf1_mutind := Induction for only_if1 Sort Prop.

  Combined Scheme necessity_mutind from onlyThrough_mutind, onlyIf_mutind, onlyIf1_mutind.

  Close Scope inference_scope.
  Close Scope chainmail_scope.
  Close Scope reduce_scope.

End Inference.
