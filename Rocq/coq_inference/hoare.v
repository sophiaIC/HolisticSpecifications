Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import operational_semantics.
Require Import assert.
Require Import classical.
Require Import assert_proofsystem.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module Hoare(L : LanguageDef).

  Import L.
  Module L_AssertProofSystem := AssertProofSystem(L).
  Export L_AssertProofSystem.

  Open Scope reduce_scope.
  Open Scope assert_scope.

  Declare Scope hoare_scope.

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

  Parameter hoare_triple : mdl -> asrt -> meth_call -> asrt -> Prop.

  Notation "M '⊢' '{pre:' P '}' m '{post:' Q '}'" := (hoare_triple M P m Q) (at level 40).

  Inductive wf_value : config -> value -> Prop :=
  | wf_true : forall σ, wf_value σ v_true
  | wf_false : forall σ, wf_value σ v_false
  | wf_null : forall σ, wf_value σ v_null
  | wf_addr : forall χ ψ a, a ∈ χ ->
                       wf_value (χ, ψ) (v_ a)
  | wf_int : forall σ z, wf_value σ (v_int z).

  Inductive wf_exp : config -> exp -> Prop :=
  | wf_val : forall σ v, wf_value σ v ->
                    wf_exp σ (e_val v)
  | wf_var : forall σ x, wf_exp σ (e_var x)
  | wf_hole : forall σ n, wf_exp σ (e_hole n)
  | wf_eq : forall σ e1 e2, wf_exp σ e1 ->
                       wf_exp σ e2 ->
                       wf_exp σ (e_eq e1 e2)
  | wf_lt : forall σ e1 e2, wf_exp σ e1 ->
                       wf_exp σ e2 ->
                       wf_exp σ (e_eq e1 e2)
  | wf_plus : forall σ e1 e2, wf_exp σ e1 ->
                         wf_exp σ e2 ->
                         wf_exp σ (e_plus e1 e2)
  | wf_minus : forall σ e1 e2, wf_exp σ e1 ->
                          wf_exp σ e2 ->
                          wf_exp σ (e_minus e1 e2)
  | wf_mult : forall σ e1 e2, wf_exp σ e1 ->
                         wf_exp σ e2 ->
                         wf_exp σ (e_mult e1 e2)
  | wf_div : forall σ e1 e2, wf_exp σ e1 ->
                        wf_exp σ e2 ->
                        wf_exp σ (e_div e1 e2)
  | wf_if : forall σ e1 e2 e3, wf_exp σ e1 ->
                          wf_exp σ e2 ->
                          wf_exp σ e3 ->
                          wf_exp σ (e_if e1 e2 e3)
  | wf_acc_f : forall σ e f, wf_exp σ e ->
                        wf_exp σ (e_acc_f e f)
  | wf_acc_g : forall σ e1 g e2, wf_exp σ e1 ->
                            wf_exp σ e2 ->
                            wf_exp σ (e_acc_g e1 g e2).

  Inductive wf_aval : config -> a_val -> Prop :=
  | wf_ahole : forall σ n, wf_aval σ (a♢ n)
  | wf_abnd : forall χ ψ a, a ∈ χ ->
                       wf_aval (χ, ψ) (a_ a).

  Definition wf_args (σ : config)(m : partial_map name a_val) : Prop :=
    forall x a, ⟦ x ↦ a ⟧_∈ m ->
           wf_aval σ a.

  Inductive wf_asrt : config -> asrt -> Prop :=
  | wf_expr : forall σ e,  wf_exp σ e ->
                      wf_asrt σ (a_exp e)
  | wf_class : forall σ e C, wf_exp σ e ->
                        wf_asrt σ (a_class e C)
  | wf_arr : forall σ A1 A2, wf_asrt σ A2 ->
                        wf_asrt σ A1 ->
                        wf_asrt σ (A1 ⟶ A2)
  | wf_and : forall σ A1 A2, wf_asrt σ A2 ->
                        wf_asrt σ A1 ->
                        wf_asrt σ (A1 ∧ A2)
  | wf_or : forall σ A1 A2, wf_asrt σ A2 ->
                        wf_asrt σ A1 ->
                        wf_asrt σ (A1 ∨ A2)
  | wf_neg : forall σ A, wf_asrt σ A ->
                    wf_asrt σ (¬ A)
  | wf_all : forall σ A, wf_asrt σ A ->
                    wf_asrt σ (∀x.[A])
  | wf_ex : forall σ A, wf_asrt σ A ->
                   wf_asrt σ (∃x.[A])
  | wf_acc : forall σ a1 a2, wf_aval σ a1 ->
                        wf_aval σ a2 ->
                        wf_asrt σ (a1 access a2)
  | wf_call : forall σ a1 a2 m args, wf_aval σ a1 ->
                                wf_aval σ a2 ->
                                wf_args σ args ->
                                wf_asrt σ (a1 calls a2 ◌ m ⟨ args ⟩)
  | wf_intrn : forall σ a, wf_aval σ a ->
                      wf_asrt σ (a internal)
  | wf_extrn : forall σ a, wf_aval σ a ->
                      wf_asrt σ (a external).

  Inductive ht_semantics : mdl -> asrt -> meth_call -> asrt -> Prop :=
  | ht_r : forall M α m β P Q, (forall M' x σ σ', is_call σ x (m_call α m β) ->
                                        M ◎ σ ⊨ P ->
                                        M ⦂ M' ⦿ σ ⤳ σ' ->
                                        exists v χ ϕ ψ, σ' = (χ, ϕ :: ψ) /\
                                                   ⟦ x ↦ v ⟧_∈ local ϕ /\
                                                   M ◎ σ' ⊨ [v /s 0]Q) ->
                          ht_semantics M P (m_call α m β) Q.

  Parameter hoare_soundness :
    forall M P m Q, M ⊢ {pre: P} m {post: Q} ->
               ht_semantics M P m Q.

  Parameter hoare_consequence1 :
    forall M A1 C A2 A1', M ⊢ {pre: A1'} C {post: A2} ->
                     M ⊢ A1 ⊇ A1' ->
                     M ⊢ {pre: A1} C {post: A2}.

  Parameter hoare_consequence2 :
    forall M A1 C A2 A2', M ⊢ {pre: A1} C {post: A2'} ->
                     M ⊢ A2' ⊇ A2 ->
                     M ⊢ {pre: A1} C {post: A2}.

  Parameter class_change_classical_spec :
    forall M x C m, M ⊢ {pre: a_class (e_ x) C} m {post: a_class (e_ x) C}.

  Close Scope hoare_scope.
  Close Scope assert_scope.
  Close Scope reduce_scope.
End Hoare.
