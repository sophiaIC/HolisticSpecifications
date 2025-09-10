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

  Parameter entails : module -> asrt -> asrt -> Prop.

  (*Definition entails (M : module)(A1 A2 : asrt) : Prop := forall σ, sat M σ (A1 ⟶ A2).*)

  Notation "M ⊢ A1 ⊆ A2" := (entails M A1 A2)(at level 40).

  Parameter entails_sound :
    forall M A1 A2, entails M A1 A2 <-> (forall σ, sat M σ A1 -> sat M σ A2).

End AssertTheory.
