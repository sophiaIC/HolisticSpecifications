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
Require Import constrained_reduction_properties.
Require Import adaptation.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Definition always_will (A : asrt) :=
  ¬ (a_will (¬ A)).

Definition always_was (A : asrt) :=
  ¬ (a_was (¬ A)).

Definition always (A : asrt) :=
  A ∧ (always_was A) ∧ (always_will A).

Definition invariant_always_will :
  forall M1 M2 A, (forall σ0 σ, M1 ⦂ M2 ◎ σ0 … ̱ ⊨ {pre: A} σ {post: A}) ->
             forall σ0 σ, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                     M1 ⦂ M2 ◎ σ0 … σ ⊨ (always_will A).
Proof.
  intros.
  unfold always_will.
  a_contradiction.
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ a_will _ |- _ ] =>
    inversion H; subst
  end.
  unfold constrained_pair_reductions in H2;
    repeat destruct_exists_loo;
    andDestruct;
    subst.

  destruct (sat_change_pair_reductions M1 M2 (χ, ϕ :: nil) σ1)
    with
      (χ0:=χ)(ϕ0:=ϕ)(ψ:=ψ)(σ0:=σ0)(A:=A)
  as [σ];
    auto;
    destruct_exists_loo;
    andDestruct.
  apply adapted_pair_reduction with (ψ:=ψ) in Ha1.
  specialize (H σ0 (σ ◁ ψ)).
  apply hoare_triple_pr_inversion with (σ':=σ2 ◁ ψ) in H;
    auto.
  a_prop.
Qed.

Definition always_will_conj_decompose :
  forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (always_will (A1 ∧ A2)) ->
                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (always_will A1) /\
                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (always_will A2).
Proof.
  intros.
  unfold always_will in *.
  split.

  - a_contradiction.
    inversion H;
      subst.
    inversion H5;
      subst.
    inversion Hcontra;
      subst.
    specialize (H6 σ');
      auto_specialize.
    inversion H6;
      subst.
    a_prop.

  - a_contradiction.
    inversion H;
      subst.
    inversion H5;
      subst.
    inversion Hcontra;
      subst.
    specialize (H6 σ');
      auto_specialize.
    inversion H6;
      subst.
    a_prop.
Qed.

Ltac a_always :=
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ always_will (_ ∧ _) |- _] =>
    apply always_will_conj_decompose in H
  end.

Lemma always_will_not_contra :
  forall {M1 M2 σ0 σ A}, M1 ⦂ M2 ◎ σ0 … σ ⊨ always_will A ->
                    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will (¬ A) ->
                    False.
Proof.
  intros.
  unfold always_will in *.
  a_prop.
Qed.

Lemma always_will_will_conj :
  forall {M1 M2 σ0 σ A2}, M1 ⦂ M2 ◎ σ0 … σ ⊨ always_will A2 ->
                     forall {A1}, M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will A1 ->
                             M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will (A1 ∧ A2).
Proof.
  intros.
  inversion H0;
    subst.
  apply sat_will with (σ':=σ');
    auto.
  unfold always_will in *.
  a_contradiction_neg.
  a_prop.
  match goal with
  | [H : _ \/ _ |- _] =>
    destruct H
  end;
    a_prop.
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ a_will _) |- _] =>
    inversion H;
      subst
  end.
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊭ (a_will (¬ _)) |- _] =>
    inversion H;
      subst
  end.
  match goal with
  | [H : forall σ : config, _ -> _,
       H' : _ ⦂ _ ⦿ _ ⌈⤳⋆⌉ ?σ' |- _ ] =>
    specialize (H σ')
  end;
    auto_specialize.
  a_prop.
Qed.