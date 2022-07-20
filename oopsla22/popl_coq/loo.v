Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Import chainmail.defs.
Require Import chainmail.L_def.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Loo <: LanguageDef.

  Inductive read_visibility : config -> addr -> value -> Prop :=
  | vr_refl : forall σ α, read_visibility σ α (v_addr α)
  | vr_local : forall χ ϕ ψ v, In v (local ϕ) ->
                          read_visibility (χ, ϕ :: ψ) (this ϕ) v
  | vr_field : forall χ ϕ ψ α1 α2 v o f C,
      classOf (χ, ϕ :: ψ) α1 C ->
      classOf (χ, ϕ :: ψ) α2 C ->
      χ α2 = Some o ->
      flds o f = Some v ->
      read_visibility (χ, ϕ :: ψ) α1 v.

  Definition visible_r := read_visibility.

  Inductive write_visibility : config -> addr -> addr -> fld -> Prop :=
  | vw_class : forall χ ϕ ψ α1 α2 v o f C,
      classOf (χ, ϕ :: ψ) α1 C ->
      classOf (χ, ϕ :: ψ) α2 C ->
      χ α2 = Some o ->
      flds o f = Some v ->
      write_visibility (χ, ϕ :: ψ) α1 α2 f.

  Definition visible_w := write_visibility.

  Definition visible_m (σ : config)(α1 α2 : addr)(m : mth) := True.

  Definition visible_c (σ : config)(α : addr)(c : cls) := True.

  Definition L_config : Type := (heap * stack).

  Definition config_translation (σ : L_config) := σ.

  Notation "'⟦' σ '⟧'" := (config_translation σ)(at level 40) : Loo_scope.

  Inductive loo_reduction : mdl -> mdl -> L_config -> L_config -> Prop :=
  | red_refl : forall M1 M2 σ, loo_reduction M1 M2 σ σ.

  Definition L_red := loo_reduction.

End Loo.

Require Import operational_semantics.

Module LooSemanticProperties <: SemanticProperties(Loo).

  Import Loo.
  Module LSemantics := AbstractOperationalSemantics(Loo).
  Import LSemantics.
  Open Scope reduce_scope.
  Open Scope Loo_scope.

  Lemma semantic_equivalence :
    forall M1 M2 σ1 σ2, L_red M1 M2 σ1 σ2 <->
                   M1 ⦂ M2 ⦿ ⟦ σ1 ⟧ ⤳ ⟦ σ2 ⟧.
  Proof.
  Admitted.


  Close Scope Loo_scope.
  Close Scope reduce_scope.
End LooSemanticProperties.
