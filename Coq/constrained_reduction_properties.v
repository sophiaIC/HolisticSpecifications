Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import function_operations.
Require Import decoupling.
Require Import decoupled_classical_properties.
Require Import adaptation.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma reduction_path_unique_prev :
  forall M1 M2 σ σ1, M1 ⦂ M2 ⦿ σ ⤳⋆ σ1 ->
                forall σ2, M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                      forall σ3, M1 ⦂ M2 ⦿ σ1 ⤳ σ3 ->
                            M1 ⦂ M2 ⦿ σ2 ⤳ σ3 ->
                            σ1 = σ2.
Proof.
  intros M1 M2 σ σ1 Hred;
    induction Hred;
    intros.

  - inversion H0;
      subst.
    + repeat unique_reduction_auto.
    + admit.
      (* acylic contradiction: there are three paths between σ1 and σ3, and 
         their sizes don't match
       *)

  - admit.
    
Admitted.

(*Lemma sat_change_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall χ ϕ,
                   σ1 = (χ, ϕ :: nil) ->
                   forall σ0 ψ A,
                     M1 ⦂ M2 ◎ σ0 … (σ1 ◁ ψ) ⊨ A ->
                     (forall σ, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ ->
                           M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                           M1 ⦂ M2 ◎ σ0 … (σ ◁ ψ) ⊨ A) \/
                     (exists σ σ', (M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ \/
                               σ1 = σ) /\
                              (M1 ⦂ M2 ⦿ σ ⤳ σ') /\
                              (M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2 \/
                               σ' = σ2) /\
                              (M1 ⦂ M2 ◎ σ0 … (σ ◁ ψ) ⊨ A) /\
                              (M1 ⦂ M2 ◎ σ0 … (σ' ◁ ψ) ⊨ ¬ A) /\
                              (forall σ'', M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ'' ->
                                      M1 ⦂ M2 ⦿ σ'' ⤳⋆ σ ->
                                      M1 ⦂ M2 ◎ σ0 … (σ'' ◁ ψ) ⊨ A)).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  - left;
      intros.
    admit. (* acylic contradiction: σ cannot exist *)

  - specialize (IHHred χ ϕ);
      auto_specialize.
    specialize (IHHred σ0 ψ A);
      auto_specialize.
    destruct IHHred as [Ha|Ha].

    + destruct (sat_excluded_middle M1 M2 σ0 (σ ◁ ψ) A).

      * left; intros.
        specialize (Ha σ);
          auto_specialize.

Qed.*)

Lemma sat_change_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall χ ϕ,
                   σ1 = (χ, ϕ :: nil) ->
                   forall σ0 ψ A,
                     M1 ⦂ M2 ◎ σ0 … (σ1 ◁ ψ) ⊨ A ->
                     M1 ⦂ M2 ◎ σ0 … (σ2 ◁ ψ) ⊨ (¬ A) ->
                     exists σ σ', (M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ \/
                              σ1 = σ) /\
                             (M1 ⦂ M2 ⦿ σ ⤳ σ') /\
                             (M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2 \/
                              σ' = σ2) /\
                             (M1 ⦂ M2 ◎ σ0 … (σ ◁ ψ) ⊨ A) /\
                             (M1 ⦂ M2 ◎ σ0 … (σ' ◁ ψ) ⊨ ¬ A).
  (*/\
                             (forall σ'', M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ'' ->
                                     M1 ⦂ M2 ⦿ σ'' ⤳⋆ σ ->
                                     M1 ⦂ M2 ◎ σ0 … (σ'' ◁ ψ) ⊨ A).*)
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  - exists σ1, σ2;
      subst;
      repeat split;
      auto;
      intros.
    (*admit.  acylic contradiction: σ'' cannot exist *)

  - destruct (sat_excluded_middle M1 M2 σ0 (σ ◁ ψ) A).
    + exists σ, σ2;
        repeat split;
        auto.

    + destruct (IHHred χ ϕ) with (σ0:=σ0)(ψ:=ψ)(A:=A);
        eauto with chainmail_db;
        repeat destruct_exists_loo;
        andDestruct.
      exists x, σ3;
        repeat split;
        auto.
      match goal with
      | [Ha : _ ⦂ _ ⦿ ?σ1 ⤳⋆ ?σ \/ ?σ1 = ?σ,
              Hb : _ ⦂ _ ⦿ ?σ ⤳ ?σ',
                   Hc : _ ⦂ _ ⦿ ?σ' ⤳⋆ ?σ2 \/ ?σ' = ?σ2,
                        Hd : _ ⦂ _ ⦿ ?σ2 ⤳ ?σ3
         |- _ ⦂ _ ⦿ ?σ' ⤳⋆ ?σ3 \/ ?σ' = ?σ3] =>
        left;
          destruct Ha, Hc;
          subst;
          auto
      end;
        try solve [eapply pair_reductions_transitive; eauto with loo_db];
        eauto with loo_db.
Qed.