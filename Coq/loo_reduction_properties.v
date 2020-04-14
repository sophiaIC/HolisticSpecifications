Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma reduction_preserves_well_formed_heap :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             χ_wf M (fst σ1) ->
             χ_wf M (fst σ2).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    try solve [crush];
    subst;
    apply heap_wf;
    intros;
    subst.

  - (*field assign reduce*)
    simpl in H.
    unfold update, t_update in H.
    destruct (eq_dec α0 α) as [Heq|Hneq];
      [subst; rewrite eqb_refl in H; auto
      |apply neq_eqb in Hneq; rewrite Hneq in H;
       inversion H11; subst; apply (H7 α0); auto].
    inversion H11; subst.
    destruct (H7 α o (cname o)) as [CDef Hwf]; auto;
      destruct Hwf as [Hwf1 Hwf2];
      destruct Hwf2 as [Hwf2 Hwf3].
    exists CDef; split;
      [inversion H; subst; auto
      |split;
       [intros
       |inversion H; subst; auto]].
    inversion H; subst; simpl.
    destruct (eq_dec f0 f) as [Heq|Hneq];
      [destruct f0; subst; rewrite <- beq_nat_refl; exists v; auto
      |destruct f0, f;
       assert (Hneq' : n <> n0);
       [intros Hcontra; subst; crush| apply Nat.eqb_neq in Hneq'; rewrite Hneq'; auto]].

  - (*new object initialization*)
    simpl in *.
    unfold update, t_update in H0.
    destruct (eq_dec α0 α) as [Heq|Hneq];
      [subst; rewrite eqb_refl in H0
      |apply neq_eqb in Hneq; rewrite Hneq in H0;
       inversion H9; subst; apply (H6 α0); auto].
    exists CDef;
      split; [inversion H0; subst; auto
             |split;
              [intros
              |inversion H0; subst; auto]].
    inversion H0; subst; simpl.
    assert (Hin : fMap f = None -> ~ In f (c_flds CDef));
      [intros;
       apply not_in_map_implies_not_in_dom with (m:=fMap); auto
      |].
    remember (fMap f) as res.
    destruct res as [y|];
      [
      |contradiction Hin; auto].
    destruct (H5 f y) as [v];
      auto.
    exists v; auto.
Qed.

Ltac reduce_heap_wf_auto :=
  match goal with
  | [Hred : ?M ∙ ?σ1 ⤳ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply reduction_preserves_well_formed_heap; eauto
  end.

Lemma reductions_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M, M1 ⋄ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto;
    link_unique_auto;
    reduce_heap_wf_auto.
Qed.

Ltac reduces_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳… ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply reductions_preserves_heap_wf; eauto
  end.

Lemma pair_reduction_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall M, M1 ⋄ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.
  link_unique_auto.
  reduce_heap_wf_auto.
  reduces_heap_wf_auto.
Qed.

Ltac pair_reduce_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply pair_reduction_preserves_heap_wf; eauto
  end.

Lemma pair_reductions_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall M, M1 ⋄ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto;
    try solve pair_reduce_heap_wf_auto.
  eapply IHHred; eauto;
    pair_reduce_heap_wf_auto.
Qed.

Ltac pair_reduces_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳⋆ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply pair_reductions_preserves_heap_wf; eauto
  end.

Ltac obj_defn_rewrite :=
  match goal with
  | [H : M_wf ?M |- context[?M ObjectName]] => rewrite (M_wf_ObjectDefn M H)
  end.

Lemma linked_wf :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             M_wf M1 ->
             M_wf M2 ->
             M_wf M.
Proof.
  intros M1 M2 M Hlink Hwf1 Hwf2;
    inversion Hlink; subst;
      inversion Hwf1; subst;
        inversion Hwf2; subst.
  apply module_wf;
    auto; intros.
  unfold extend;
    destruct (M1 ObjectName); auto.
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush.
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush; eauto.
Qed.

Ltac linking_wf :=
  match goal with
  | [H1 : M_wf ?M1, H2 : M_wf ?M2, Hlink : ?M1 ⋄ ?M2 ≜ ?M |- M_wf ?M] => eapply linked_wf; eauto
  end.

Lemma reduction_preserves_config_finiteness :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             finite_σ σ1 ->
             finite_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    finite_auto;
    simpl in *;
    intros;
    auto.

  - destruct H0 as [Ha|Ha];
      [|destruct Ha as [Ha|Ha]];
      subst;
      simpl;
      [apply fin_update;
       apply finite_map_composition;
       auto
      | |];
      try solve [crush;
                 eauto];
      eauto with loo_db.

  - 

  - unfold update_ψ_map, update_ϕ_map in H0;
      inversion H0;
      subst;
      [simpl; apply fin_update|];
      apply H8; crush.

  - destruct H; [subst; simpl|]; eauto.

  - destruct H0; crush.

  - crush.

  - crush.

  - crush.

  - crush.
Qed.

Hint Resolve reduction_preserves_config_finiteness : loo_db.

Lemma reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    crush;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_finiteness : loo_db.

Lemma pair_reduction_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    subst;
    intros;
    crush;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_finiteness : loo_db.

Lemma pair_reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    subst;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_finiteness : loo_db.

Lemma reduction_preserves_config_not_stuck :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             not_stuck_σ σ1 ->
             not_stuck_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    unfold not_stuck_σ in *;
    simpl in *;
    try solve [eexists; crush; eauto].

  - exists ϕ'', (ϕ'::ψ); split;
      unfold not_stuck_ϕ;
      subst;
      simpl in *;
      eauto with loo_db.

  - exists ϕ', ψ;
      subst;
      simpl in *;
      split;
      auto;
      unfold not_stuck_ϕ;
      simpl in *;
      auto with loo_db.

  - subst σ'; simpl;
      exists ϕ', ψ;
      split;
      auto;
      subst ϕ';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.

  - exists ϕ', ψ;
      split;
      auto;
      subst;
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db;
      crush.

  - repeat eexists.

  - repeat eexists.

  - exists ϕ'', ψ;
      split;
      auto;
      subst ϕ'';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.

  - exists ϕ'', ψ;
      split;
      auto;
      subst ϕ'';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.
Qed.

Hint Resolve reduction_preserves_config_not_stuck : loo_db.

Lemma reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_not_stuck : loo_db.

Lemma pair_reduction_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_not_stuck : loo_db.

Lemma pair_reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_not_stuck : loo_db.

Lemma reduction_preserves_config_waiting :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             waiting_σ σ1 ->
             waiting_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    unfold waiting_σ in *;
    simpl in *;
    try solve [eexists; crush; eauto].

  - exists ϕ'', (ϕ'::ψ); split;
      unfold waiting_ψ, waiting_ϕ in *;
      subst;
      intros;
      auto;
      match goal with
      | [H : In ?ϕ0 _ |- waiting (contn ?ϕ0)] => destruct H; subst; crush
      end.

  - exists ϕ'', ψ; subst;
      split;
      auto;
      unfold waiting_ψ, waiting_ϕ in *;
      intros;
      simpl in *;
      auto;
      crush.

  - exists ϕ'', ψ; subst;
      split;
      auto;
      unfold waiting_ψ, waiting_ϕ in *;
      intros;
      simpl;
      auto;
      crush.

Qed.

Hint Resolve reduction_preserves_config_waiting : loo_db.

Lemma reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_waiting : loo_db.

Lemma pair_reduction_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_waiting : loo_db.

Lemma pair_reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_waiting : loo_db.

Lemma reduction_preserves_config_has_self :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             has_self_σ σ1 ->
             has_self_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros Hself;
    inversion Hself;
    subst;
    eauto.

  - (* meth *)
    inversion H10; subst.
    apply self_config;
      intros ϕ' Hin;
      inversion Hin;
      auto;
      [subst|].
    apply self_frm;
      exists α, o;
      split;
      auto.
    inversion H0;
      subst.
    assert (Hinϕ : In ϕ (ϕ::ψ));
      [apply in_eq|apply H9 in Hinϕ].
    apply self_frm;
      inversion Hinϕ;
      auto.
    apply H9;
      simpl in *;
      inversion H1;
      auto.

  - (* var asgn *)
    apply has_self_update_σ_contn
      with
        (c:=c_stmt s)
      in Hself.
    apply has_self_update_σ
      with
        (x:=x)(v:=v)
      in Hself;
      auto.

  - (* field asgn*)
    inversion H12;
      subst.
    apply self_config;
      intros.
    inversion H;
      subst;
      remember {| cname := cname o; flds := update f v (flds o); meths := meths o |} as o'.
    assert (Hin : In ϕ (ϕ::ψ));
      [apply in_eq|apply H11 in Hin].
    destruct Hin.
    destruct H7 as [α0 Ha];
      destruct Ha as [o0];
      andDestruct.
    apply self_frm.
    exists α0.
    destruct (eq_dec α0 α) as [|Hneq];
      [subst α0;
       exists o'
      |simpl;
       exists o0];
      split;
      simpl;
      auto;
      unfold update, t_update;
      [rewrite eqb_refl; auto
      |rewrite neq_eqb; auto].  
    assert (Hin : In ϕ0 (ϕ::ψ));
      [apply in_cons; auto|apply H11 in Hin].
    destruct Hin.
    destruct H8 as [α0 Ha];
      destruct Ha as [o0];
      andDestruct.
    apply self_frm.
    exists α0.
    destruct (eq_dec α0 α) as [|Hneq];
      [subst α0;
       exists o'
      |simpl;
       exists o0];
      split;
      simpl;
      auto;
      unfold update, t_update;
      [rewrite eqb_refl; auto
      |rewrite neq_eqb; auto].

  - (* new *)
    inversion H10;
      subst.
    apply self_config;
      intros.
    inversion H0;
      subst;
      remember {| cname := C; flds := fMap ∘ (vMap ϕ); meths := c_meths CDef |} as o'.
    + apply self_frm; simpl.
      assert (Hin : In ϕ (ϕ::ψ));
        [apply in_eq
        |apply H9 in Hin].
      destruct Hin as [χ ϕ Ha];
        destruct Ha as [α0 Ha];
        destruct Ha as [o0];
        andDestruct.
      exists α0.
      destruct (eq_dec α0 α) as [|Hneq];
        [subst α0;
         exists o'
        |simpl;
         exists o0];
        simpl;
        auto;
        unfold update, t_update;
        [rewrite neq_eqb; auto
        |rewrite neq_eqb; auto];
        split;
        auto;
        [rewrite eqb_refl
        |rewrite neq_eqb; auto];
        auto.

    + apply self_frm.
      unfold update, t_update.
      assert (Hin : In ϕ0 (ϕ::ψ));
        [apply in_cons; auto
        |apply H9 in Hin;
         destruct Hin as [χ ϕ' Ha];
         destruct Ha as [α0 Ha];
         destruct Ha as [o0];
         andDestruct].
      exists α0.
      destruct (eq_dec α0 α) as [|Hneq];
        [subst α0;
         exists o'
        |exists o0];
        [rewrite eqb_refl; auto
        |rewrite neq_eqb; auto];
        auto.

  - apply self_config;
      intros.
    inversion H1; subst;
      [
      |specialize (H2 ϕ0)].
    + apply self_frm.
      specialize (H2 ϕ (in_eq ϕ ψ)).
      inversion H2; subst; auto.
    + specialize (H2 (in_cons ϕ ϕ0 ψ H3));
        assumption.

  - apply self_config;
      intros.
    inversion H1; subst;
      [
      |specialize (H2 ϕ0)].
    + apply self_frm.
      specialize (H2 ϕ (in_eq ϕ ψ)).
      inversion H2; subst; auto.
    + specialize (H2 (in_cons ϕ ϕ0 ψ H3));
        assumption.

  - (* ret 1 *)
    apply self_config;
      intros.
    inversion H6;
      subst.
    inversion H;
      subst.
    apply has_self_update_ϕ_contn, has_self_update_ϕ;
      auto.
    apply H5, in_cons, in_eq.
    apply H5, in_cons, in_cons;
      auto.

  - (* ret 2*)
    apply self_config;
      intros.
    inversion H6;
      subst.
    inversion H;
      subst.
    apply has_self_update_ϕ_contn, has_self_update_ϕ;
      auto.
    apply H5.
    apply in_cons, in_eq.
    apply H5, in_cons, in_cons;
      auto.
Qed.

Hint Resolve reduction_preserves_config_has_self : loo_db.

Lemma reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reduction_preserves_config_has_self : loo_db.

Lemma pair_reduction_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
  eapply reduction_preserves_config_has_self;
    eauto.
  eapply reductions_preserves_config_has_self;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_has_self : loo_db.

Lemma pair_reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_has_self : loo_db.

Lemma reduction_preserves_config_wf :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             σ_wf σ1 ->
             σ_wf σ2.
Proof.
  intros M σ1 σ2 Hred Hwf;
    inversion Hred;
    subst;
    apply config_wf;
    inversion Hwf;
    eauto with loo_db;
    subst.
Qed.

Hint Resolve reduction_preserves_config_wf : loo_db.

Lemma reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
             σ_wf σ1 ->
             σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_wf : loo_db.

Lemma pair_reduction_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_wf : loo_db.

Lemma pair_reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_wf : loo_db.

Theorem eval_unique :
  forall M σ e v1, M ∙ σ ⊢ e ↪ v1 ->
              forall v2, M ∙ σ ⊢ e ↪ v2 ->
                    v2 = v1.
Proof.
  intros M σ e v1 Heval;
    induction Heval;
    intros;
    try solve [inversion H; subst; [eauto| eauto];
               apply IHHeval1 in H6; inversion H6].

  (** Case 1: eval v *)
  - inversion H; eauto.

  (** Case 2: eval x *)
  - inversion H0; subst; crush.

  (** Case 3: e.f *)
  - inversion H1; subst; crush.
    apply IHHeval in H4; subst; crush.

  (** Case 4: e0.g(e) *)
  - inversion H2; subst.
    apply IHHeval1 in H6; inversion H6; subst.
    rewrite H7 in H; inversion H; subst.
    rewrite H8 in H0; inversion H0; subst.
    rewrite H11 in H1; inversion H1; subst.
    apply IHHeval2 in H13; subst.
    apply IHHeval3 in H14; subst; auto.

  (** Case 5: e1 = e2 *) 
  - inversion H; subst; eauto.
    apply IHHeval1 in H2; apply IHHeval2 in H5; subst; crush.

  (** Case 6: e1 ≠ e2 *)
  - inversion H0; subst; eauto.
    apply IHHeval1 in H5; apply IHHeval2 in H7; subst; crush.

  (** Case 7 : e1 + e2 *)
  - inversion H; subst; eauto.
    apply IHHeval1 in H4; apply IHHeval2 in H6; subst; crush.

  (** Case 8 : e1 - e2 *)
  - inversion H; subst; eauto.
    apply IHHeval1 in H4; apply IHHeval2 in H6; subst; crush.

  (** Case 9 : e1 * e2 *)
  - inversion H; subst; eauto.
    apply IHHeval1 in H4; apply IHHeval2 in H6; subst; crush.

  (** Case 10 : e1 / e2 *)
  - inversion H; subst; eauto.
    apply IHHeval1 in H4; apply IHHeval2 in H6; subst; crush.
Qed.

Hint Rewrite eval_unique : loo_db.

Ltac eval_rewrite :=
  repeat match goal with
         | [H1 : ?M ∙ ?σ ⊢ ?e ↪ ?v1, H2 : ?M ∙ ?σ ⊢ ?e ↪ ?v2 |- _] =>
           eapply (eval_unique M σ e v1 H1) in H2;
           eauto;
           subst
         end.

Lemma pair_reductions_transitive :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ3 ->
                       M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Lemma reduction_preserves_addr_classes :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall (α : addr) o1,
               mapp σ1 α = Some o1 ->
               exists o2, mapp σ2 α = Some o2 /\
                     cname o2 = cname o1.
Proof.
  intros M σ1 σ2 Hred;
    destruct Hred;
    intros;
    subst;
    eauto;
    unfold mapp, configMapHeap in *;
    simpl in *.

  - (* asgn fld*)
    destruct (eq_dec α0 α) as [|Hneq];
      [subst|].
    + exists {| cname := cname o; flds := update f v (flds o); meths := meths o |};
        simpl;
        unfold update, t_update;
        rewrite eqb_refl;
        split;
        simpl;
        crush.

    + exists o1;
        unfold update, t_update;
        rewrite neq_eqb;
        auto.

  - destruct (eq_dec α0 α) as [|Hneq];
      [subst; eapply fresh_heap_some_contradiction; eauto|].

    + exists o1;
        unfold update, t_update;
        rewrite neq_eqb;
        auto.
  
Qed.

Hint Resolve reduction_preserves_addr_classes : loo_db.
Hint Rewrite reduction_preserves_addr_classes : loo_db.

Lemma reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                   cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.

  destruct IHHred with (α:=α)(o1:=o1) as [o Hclass];
    eauto; auto;
      andDestruct.

  edestruct reduction_preserves_addr_classes as [o' Hclass1];
    eauto.

  andDestruct.

  eexists; split; eauto; crush.
Qed.

Hint Resolve reductions_preserves_addr_classes : loo_db.
Hint Rewrite reductions_preserves_addr_classes : loo_db.

Lemma pair_reduction_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_addr_classes : loo_db.
Hint Rewrite pair_reduction_preserves_addr_classes : loo_db.

Lemma pair_reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.

  destruct (pair_reduction_preserves_addr_classes M1 M2 σ1 σ)
    with
      (α:=α)(o1:=o1)
    as [o Hclass1];
    auto;
    andDestruct.

  edestruct IHHred as [o' Hclass2];
    eauto;
    andDestruct.

  eexists; split; eauto; crush.
  
Qed.

Hint Resolve pair_reductions_preserves_addr_classes : loo_db.
Hint Rewrite pair_reductions_preserves_addr_classes : loo_db.

Lemma reduction_unique :
  forall M σ σ1, M ∙ σ ⤳ σ1 ->
            forall σ2, M ∙ σ ⤳ σ2 ->
                  σ2 = σ1.
Proof.
  intros M σ σ1 Hred;
    induction Hred;
    intros.

  - (* meth *)
    simpl in *;
      subst.
    inversion H2;
      subst;
      crush.
    inversion H9;
      subst;
      crush.
    inversion H8; subst.
    rewrite H1 in H10.
    inversion H10; subst.
    interpretation_rewrite.
    crush.

  - (* vAssgn *)
    inversion H8;
      subst;
      crush.
    inversion H10; subst.
    rewrite H1 in H11;
      inversion H11;
      subst.
    interpretation_rewrite;
      crush.

  - (* fAssgn *)
    simpl in *.
    inversion H11;
      subst;
      crush.
    inversion H12; subst.
    rewrite H13 in H0;
      inversion H0;
      subst.
    interpretation_rewrite.
    crush.

  - (* new *)
    inversion H9;
      subst;
      crush.
    inversion H11; subst.
    rewrite H1 in H12;
      inversion H12;
      subst;
      crush.
    match goal with
    | [H1 : fresh_χ ?χ ?αa,
            H2 : fresh_χ ?χ ?αb |- _] =>
      apply fresh_heap_unique with (α1:=αa) in H2;
        subst;
        auto
    end.
    crush.

  - inversion H1;
      subst;
      crush.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    eval_rewrite.
    crush.

  - inversion H1;
      subst;
      crush.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    eval_rewrite.
    crush.

  - (* ret1 *)
    subst.
    inversion H5;
      subst;
      crush.
    inversion H; subst.
    rewrite H0 in H4;
      inversion H4;
      subst.
    interpretation_rewrite.
    crush.


  - crush.
    inversion H5;
      subst;
      crush.
    inversion H;
      subst.
    rewrite H0 in H4;
      inversion H4;
      subst.
    interpretation_rewrite.
    crush.

Qed.

Hint Resolve reduction_unique : loo_db.

Lemma pair_reduction_unique :
  forall M1 M2 σ σ1, M1 ⦂ M2 ⦿ σ ⤳ σ1 ->
                forall σ2, M1 ⦂ M2 ⦿ σ ⤳ σ2 ->
                      σ1 = σ2.
Proof.
Admitted.

Ltac unique_reduction_auto :=  
    match goal with
    | [Ha : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σa,
            Hb : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σb |- _] =>
      eapply pair_reduction_unique with (σ1:=σa) in Hb;
        eauto;
        subst
    end.

Lemma list_does_not_contain_itself :
  forall {A : Type} (l : list A) a,
    a :: l = l ->
    False.
Proof.
  intros A l;
    induction l;
    intros;
    crush.
Qed.

Inductive reductions : mdl -> config -> config -> Prop :=
| red_single : forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                          reductions M σ1 σ2
| red_trans : forall M σ1 σ2 σ3, reductions M σ1 σ2 ->
                            M ∙ σ2 ⤳ σ3 ->
                            reductions M σ1 σ3.

Hint Constructors reductions : loo_db.

Inductive substmt : stmt -> stmt -> Prop :=
| sub_refl : forall s1 s2, substmt s1 s2
| sub_if1 : forall s e s1 s2, substmt s s1 ->
                         substmt s (s_if e s1 s2)
| sub_if2 : forall s e s1 s2, substmt s s2 ->
                         substmt s (s_if e s1 s2)
| sub_stmt1 : forall s s1 s2, substmt s s1 ->
                         substmt s (s_stmts s1 s2)
| sub_stmt2 : forall s s1 s2, substmt s s2 ->
                         substmt s (s_stmts s1 s2).

Hint Constructors substmt : loo_db.

Parameter stmt_not_strict_substatement_of_itself :
  forall s s', substmt s s' ->
          s = s' ->
          False.

Lemma acyclic_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intro Hcontra;
    subst.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    apply list_does_not_contain_itself in H8; auto.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H7 in H1;
      simpl in *.
    inversion H1; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H8 in H0;
      simpl in *.
    inversion H0; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H7 in H1;
      simpl in *.
    inversion H1; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - simpl_crush; subst.
    rewrite <- H2 in H.
    simpl in *.
    inversion H; subst;
      simpl in *.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - simpl_crush; subst.
    rewrite <- H2 in H.
    simpl in *.
    inversion H; subst;
      simpl in *.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    eapply list_does_not_contain_itself; eauto.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    eapply list_does_not_contain_itself; eauto.
Qed.

Hint Resolve acyclic_reduction : loo_db.

Lemma acyclic_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred.

  - eauto with loo_db.

  - intro Hcontra;
      subst.
  
Admitted.

Lemma acyclic_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ1 <> σ2.
Proof.
Admitted.

Lemma pair_reductions_path_unique :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall σ, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ ->
                      M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                      False.
Proof.
Admitted.

Lemma pair_reductions_unique_prev :
  forall M1 M2 σ σ1, M1 ⦂ M2 ⦿ σ ⤳⋆ σ1 ->
                forall σ2, M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                      forall σ', M1 ⦂ M2 ⦿ σ1 ⤳ σ' ->
                            M1 ⦂ M2 ⦿ σ2 ⤳ σ' ->
                            σ1 = σ2.
Proof.
  intros M1 M2 σ σ1 Hred;
    induction Hred;
    intros.

  - inversion H0; subst.
    unique_reduction_auto.
    unique_reduction_auto.
    inversion H4; subst.
    unique_reduction_auto.
    contradiction (acyclic_pair_reductions M1 M2 σ0 σ0);
      auto with loo_db.
    unique_reduction_auto.
    contradiction (acyclic_pair_reductions M1 M2 σ3 σ3);
      auto with loo_db.
    apply pair_reductions_transitive with (σ2:=σ0);
      auto with loo_db.

  - inversion H0; subst;
      unique_reduction_auto;
      eauto.
    contradiction (pair_reductions_path_unique M1 M2 σ0 σ')
      with (σ:=σ2);
      auto with loo_db.
Qed.
Print red_single.

(* call block *)

(*Lemma reduction_call_rtrn :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ ϕ, reductions M (χ, ϕ::nil) σ1 ->
                    (exists χ' χ'' ϕ' ψ' x y m β, reductions M (χ, ϕ::nil) (χ', ϕ'::ψ') /\
                    contn ϕ' = (c_stmt ())).*)
  
