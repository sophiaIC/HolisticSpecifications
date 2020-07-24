Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma reduction_implies_stack_head1 :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             exists χ ϕ ψ, σ1 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    eauto.
Qed.

Lemma reduction_implies_stack_head2 :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    eauto.
Qed.

Lemma internal_reductions_implies_stack_head1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 exists χ ϕ ψ, σ1 = (χ, ϕ :: ψ).
Proof.
  intros.
  induction H;
    subst;
    eauto.
  eapply reduction_implies_stack_head1;
    eauto.
Qed.
                 
Lemma internal_reduction_implies_stack_head2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    subst;
    eauto;
    eapply reduction_implies_stack_head2;
    eauto.
Qed.
                 
Lemma pair_reduction_implies_stack_head1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 exists χ ϕ ψ, σ1 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    subst;
    eauto.
  - eapply internal_reductions_implies_stack_head1;
      eauto.
  - eapply reduction_implies_stack_head1;
      eauto.
Qed.
                 
Lemma pair_reduction_implies_stack_head2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    subst;
    eauto;
    eapply reduction_implies_stack_head2;
    eauto.
Qed.
                 
Lemma pair_reductions_implies_stack_head1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 exists χ ϕ ψ, σ1 = (χ, ϕ :: ψ).
Proof.
  intros.
  induction H;
    subst;
    eauto.
  - eapply pair_reduction_implies_stack_head1;
      eauto.
Qed.
                 
Lemma pair_reductions_implies_stack_head2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
Proof.
  intros.
  inversion H;
    subst;
    eapply pair_reduction_implies_stack_head2;
    eauto.
Qed.

Lemma adapted_mapping_var :
  forall σ (x : var) o, mapp σ x = o ->
                   forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                            forall ψ', mapp (σ ◁ ψ') x = o.
Proof.
  intro σ;
    intros;
    subst.
  unfold stack_append in *;
    simpl in *.
  repeat map_rewrite;
    simpl in *.
  auto.
Qed.

Lemma adapted_mapping_addr :
  forall σ (α : addr) o, mapp σ α = o ->
                   forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                            forall ψ', mapp (σ ◁ ψ') α = o.
Proof.
  intro σ;
    intros;
    subst.
  unfold stack_append in *;
    simpl in *.
  repeat map_rewrite;
    simpl in *.
  auto.
Qed.

Lemma adapted_interpretation :
  forall σ x v, ⌊ x ⌋ σ ≜ v ->
           forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                    forall ψ', ⌊ x ⌋ (σ ◁ ψ') ≜ v.
Proof.
  intros;
    subst;
    apply int_x.
  eapply adapted_mapping_var;
    eauto.
  match goal with
  | [H : ⌊ _ ⌋ _ ≜ _ |- _] =>
    inversion H;
      subst;
      auto
  end.
Qed.

Hint Resolve adapted_mapping_var adapted_mapping_addr adapted_interpretation : loo_db.
Hint Rewrite adapted_mapping_var adapted_mapping_addr adapted_interpretation : loo_db.

Lemma adapted_update_σ_map :
  forall χ ϕ ψ ψ' x v, update_σ_map ((χ, ϕ :: ψ) ◁ ψ') x v =
                  (update_σ_map (χ, ϕ :: ψ) x v) ◁ ψ'.
Proof.
  intros.
  unfold stack_append.
  repeat map_rewrite;
    simpl;
    auto.
Qed.

Lemma adapted_evaluation :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                      forall ψ', M ∙ (σ ◁ ψ') ⊢ e ↪ v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    subst;
    eauto with loo_db.

  - eapply v_f_ghost;
      eauto.

    unfold update_σ_map in *; simpl in *.
    unfold stack_append in *; simpl in *.
    eauto.
Qed.

Lemma adapted_classOf :
  forall x σ C, classOf x σ C ->
           forall χ ϕ ψ ψ', σ = (χ, ϕ :: ψ) ->
                       classOf x (σ ◁ ψ') C.
Proof.
  intros;
    subst.
  inversion H;
    subst;
    unfold stack_append;
    simpl in *.
  eapply adapted_interpretation with (ψ':=ψ') in H0;
    eauto.
  eapply cls_of;
    eauto.
Qed.

Lemma adapted_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall ψ, M ∙ (σ1 ◁ ψ) ⤳ (σ2 ◁ ψ).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    repeat match goal with
           | [H : classOf _ (_ , _ :: _) _ |- context[_ ◁ ?ψ]] =>
             eapply adapted_classOf with (ψ':=ψ) in H;
               eauto
           end;
    repeat match goal with
           | [H : _ ∙ (_ , _ :: _) ⊢ _ ↪ _ |- context[_ ◁ ?ψ]] =>
             eapply adapted_evaluation with (ψ':=ψ) in H;
               eauto
           end;
    repeat match goal with
           | [H : ⌊ _ ⌋ (_ , _ :: _) ≜ _ |- context[_ ◁ ?ψ]] =>
             eapply adapted_interpretation with (ψ':=ψ) in H;
               eauto
           end;  
    unfold stack_append in *;
    simpl in *;
    try solve [eapply r_mth; eauto];
    try solve [eapply r_new; eauto];
    try solve [eauto with loo_db].
Qed.

Lemma adapted_is_internal :
  forall M1 M2 σ x, is_internal M1 M2 σ x ->
               forall ψ, is_internal M1 M2 (σ ◁ ψ) x.
Proof.
  intros;
    unfold is_internal in *;
    intros;
    repeat destruct_exists_loo;
    andDestruct;
    subst.
  destruct σ as [χ ψ'].
  assert (exists ϕ ψ'', ψ' = ϕ :: ψ'');
  [|repeat destruct_exists_loo; subst].
  + destruct ψ' as [|ϕ ψ''];
      [|eauto].
    repeat map_rewrite;
      crush.
  + repeat match goal with
           | [H : mapp (_, _ :: _) _ = _ |- context[_ ◁ ?ψ]] =>
             try (eapply adapted_mapping_addr with (ψ':=ψ) in H);
               try (eapply adapted_mapping_var with (ψ':=ψ) in H);
               eauto
           end.
    repeat eexists; eauto.
Qed.

Lemma adapted_is_external :
  forall M1 M2 σ x, is_external M1 M2 σ x ->
               forall ψ, is_external M1 M2 (σ ◁ ψ) x.
Proof.
  intros;
    unfold is_external in *;
    intros;
    repeat destruct_exists_loo;
    andDestruct;
    subst.
  destruct σ as [χ ψ'].
  assert (exists ϕ ψ'', ψ' = ϕ :: ψ'');
  [|repeat destruct_exists_loo; subst].
  + destruct ψ' as [|ϕ ψ''];
      [|eauto].
    repeat map_rewrite;
      crush.
  + repeat match goal with
         | [H : mapp (_, _ :: _) _ = _ |- context[_ ◁ ?ψ]] =>
           try (eapply adapted_mapping_addr with (ψ':=ψ) in H);
           try (eapply adapted_mapping_var with (ψ':=ψ) in H);
             eauto
         end.
Qed.

Lemma adapted_internal_self :
  forall M1 M2 σ, internal_self M1 M2 σ ->
             forall ψ, internal_self M1 M2 (σ ◁ ψ).
Proof.
  intros;
    unfold internal_self in *;
    intros;
    subst.
  eapply adapted_is_internal; eauto.
Qed.

Lemma adapted_external_self :
  forall M1 M2 σ, external_self M1 M2 σ ->
             forall ψ, external_self M1 M2 (σ ◁ ψ).
Proof.
  intros;
    unfold external_self in *;
    intros;
    subst.
  eapply adapted_is_external;
    eauto.
Qed.

Lemma adapted_internal_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳… (σ2 ◁ ψ).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    try match goal with
        | [H : ?M ∙ ?σ1 ⤳ ?σ2 |- context[_ ◁ ?ψ']] =>
          notHyp (M ∙ σ1 ◁ ψ' ⤳ (σ2 ◁ ψ'));
            eapply adapted_reduction with (ψ':=ψ') in H;
            eauto
        end;
    try match goal with
        | [H : internal_self _ _ _ |- context[_ ◁ ?ψ']] =>
          eapply adapted_internal_self with (ψ:=ψ') in H;
            eauto
        end;
    try match goal with
        | [H : external_self _ _ _ |- context[_ ◁ ?ψ']] =>
          eapply adapted_external_self with (ψ:=ψ') in H;
            eauto
        end.

  - eapply pr_single; eauto.

  - eapply pr_trans; eauto.
Qed.

Lemma adapted_pair_reduction :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳ (σ2 ◁ ψ).
Proof.
  intros.
  inversion H;
    subst;
    try match goal with
        | [H : ?M ∙ ?σ1 ⤳ ?σ2 |- context[_ ◁ ?ψ']] =>
          notHyp (M ∙ σ1 ◁ ψ' ⤳ (σ2 ◁ ψ'));
            eapply adapted_reduction with (ψ':=ψ') in H;
            eauto
        end;
    try match goal with
        | [H : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳… ?σ2 |- context[_ ◁ ?ψ']] =>
          notHyp (M1 ⦂ M2 ⦿ σ1 ◁ ψ' ⤳… (σ2 ◁ ψ'));
            eapply adapted_internal_reductions with (ψ':=ψ') in H;
            eauto
        end;
    try match goal with
        | [H : internal_self _ _ _ |- context[_ ◁ ?ψ']] =>
          eapply adapted_internal_self with (ψ:=ψ') in H;
            eauto
        end;
    try match goal with
        | [H : external_self _ _ _ |- context[_ ◁ ?ψ']] =>
          eapply adapted_external_self with (ψ:=ψ') in H;
            eauto
        end.
  - eapply p_internal;
      eauto.
  - eapply p_external;
      eauto.
    eapply adapted_external_self; eauto.
Qed.

Lemma adapted_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳⋆ (σ2 ◁ ψ).
Proof.
  intros;
    induction H;
    subst.
  - eapply prs_single; eauto.
    eapply adapted_pair_reduction;
      eauto.
  - eapply prs_trans; eauto.
    eapply adapted_pair_reduction;
      eauto.
Qed.

Lemma constrained_pair_reduction_is_reduction :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⌈⤳⋆⌉ σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
Proof.
  intros.
  unfold constrained_pair_reductions in *.
  repeat destruct_exists_loo;
    andDestruct;
    subst.
  apply adapted_pair_reductions with (ψ:=ψ) in Ha0;
    auto.
Qed.