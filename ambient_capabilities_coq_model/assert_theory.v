Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import assert.
Require Export operational_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module AssertTheory.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.

  Definition entails (M : module)(A1 A2 : asrt) : Prop := forall σ, sat M σ (A1 ⟶ A2).

  Notation "M ⊢ A1 ⊆ A2" := (entails M A1 A2)(at level 40).

  Lemma entails_strengthening :
    forall M σ A1 A2, sat M σ A1 ->
                 sat M σ (A1 ⟶ A2) ->
                 sat M σ A2.
  Proof.
  Admitted.

End AssertTheory.
