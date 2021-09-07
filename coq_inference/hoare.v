Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import operational_semantics.
Require Import specw.
Require Import classical.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module Hoare(L : LanguageDef).

  Import L.
  Module L_Classical := ClassicalProperties(L).
  Export L_Classical.

  Open Scope reduce_scope.
  Open Scope specw_scope.

  Declare Scope hoare_scope.

  Reserved Notation "M '⊢' '{pre:' P '}' m '{post:' Q '}'" (at level 40).

  Inductive classical : asrt -> Prop :=
  | cl_exp : forall e, classical (a_exp e)
  | cl_class : forall e C, classical (a_class e C)
  | cl_neg : forall P, classical P ->
                  classical (¬ P)
  | cl_and : forall P1 P2, classical P1 ->
                      classical P2 ->
                      classical (P1 ∧ P2)
  | cl_or : forall P1 P2, classical P1 ->
                     classical P2 ->
                     classical (P1 ∨ P2)
  | cl_all : forall P, classical P ->
                  classical (∀x.[P])
  | cl_ex : forall P, classical P ->
                 classical (∃x.[P]).


  Inductive meth_call : Type :=
  | m_call : addr -> mth -> partial_map name value -> meth_call.

  Inductive is_call : config -> name -> meth_call -> Prop :=
  | is_meth_call : forall χ ϕ x y b ψ α m β β',
      contn ϕ = c_ ((call x y m β);; b) ->
      ⟦ y ↦ v_ α⟧_∈ local ϕ ->
      β' = (local ϕ) ∘ β ->
      is_call (χ, ψ) x (m_call α m β').

  Inductive hoare_triple : mdl -> asrt -> meth_call -> asrt -> Prop :=
  | ht_r : forall M α m β P Q, (forall M' x σ σ', is_call σ x (m_call α m β) ->
                                        M ◎ σ ⊨ P ->
                                        M ⦂ M' ⦿ σ ⤳ σ' ->
                                        exists v χ ϕ ψ, σ' = (χ, ϕ :: ψ) /\
                                                   ⟦ x ↦ v ⟧_∈ local ϕ /\
                                                   M ◎ σ' ⊨ [v /s 0]Q) ->
                          M ⊢ {pre: P} (m_call α m β) {post: Q}

  where "M '⊢' '{pre:' P '}' m '{post:' Q '}'"
          := (hoare_triple M P m Q).

  Parameter hoare_consequence1 :
    forall M A1 C A2 A1', M ⊢ {pre: A1'} C {post: A2} ->
                     M ⊢ A1 ⊇ A1' ->
                     M ⊢ {pre: A1} C {post: A2}.

  Parameter hoare_consequence2 :
    forall M A1 C A2 A2', M ⊢ {pre: A1} C {post: A2'} ->
                     M ⊢ A2' ⊇ A2 ->
                     M ⊢ {pre: A1} C {post: A2}.

  Close Scope hoare_scope.
  Close Scope specw_scope.
  Close Scope reduce_scope.
End Hoare.
