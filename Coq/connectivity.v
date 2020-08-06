Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import hoare.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Definition access (χ, φ :: _) (α β : Address) : Prop :=
  (exists f, χ α = (_, (f, β))) \/ ⌊this⌋ σ ≜ α /\ (exists γ, φ γ = β) 

Lemma connectivity : H.