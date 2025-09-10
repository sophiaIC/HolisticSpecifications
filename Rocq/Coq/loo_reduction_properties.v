Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import function_operations.
Require Import adaptation.
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
      destruct Hwf as [Hwf1 Hwf2].
    exists CDef; split;
      [inversion H; subst; auto
      |intros].
    inversion H; subst; simpl.
    destruct (eq_dec f0 f) as [Heq|Hneq];
      [destruct f0; subst; rewrite <- beq_nat_refl; exists v; auto
      |destruct f0, f;
       assert (Hneq' : n <> n0);
       [intros Hcontra; subst; crush| apply Nat.eqb_neq in Hneq'; rewrite Hneq'; auto]].

  - (*new object initialization*) (* newly written by mrr, may not be ideal solution? *)
    simpl in *.
    unfold update, t_update in H0.
    inversion H7 as [HinF [HinfM Huniq]].
    destruct (eq_dec α0 α) as [Heq|Hneq].
      + exists CDef. subst. rewrite eqb_refl in H0. crush.
      + apply neq_eqb in Hneq. rewrite Hneq in H0.
        inversion H13. subst. apply (H9 α0). auto. reflexivity.
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
  - link_unique_auto.
    reduce_heap_wf_auto.
    reduces_heap_wf_auto.

  - link_unique_auto.
    reduce_heap_wf_auto.
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
Qed.

Ltac pair_reduces_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳⋆ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply pair_reductions_preserves_heap_wf; eauto
  end.

Ltac obj_defn_rewrite :=
  match goal with
  | [H : M_wf ?M |- context[?M Object]] => rewrite (M_wf_ObjectDefn M H)
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
    destruct (M1 Object); auto.
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
    auto;
    try solve [crush].

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

  (* copied from s_meth above for introduction of 
     constructors, may not be optimal *)
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
    try solve [eexists; crush; eauto]; try solve [repeat eexists].

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

  -  subst σ'; simpl;
      exists ϕ', ψ;
      split;
      auto;
      subst ϕ';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.

  - exists ϕ'', (ϕ'::ψ); split;
      unfold not_stuck_ϕ;
      subst;
      simpl in *;
      eauto with loo_db.

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
    try solve [eexists; crush; eauto];
    try solve [exists ϕ'', ψ; split; unfold waiting_ψ, waiting_ϕ in *; crush].

  - exists ϕ'', (ϕ'::ψ); split;
      unfold waiting_ψ, waiting_ϕ in *;
      subst;
      intros;
      auto;
      match goal with
      | [H : In ?ϕ0 _ |- waiting (contn ?ϕ0)] => destruct H; subst; crush
      end.

  - exists ϕ'', (ϕ'::ψ); split;
      unfold waiting_ψ, waiting_ϕ in *;
      subst;
      intros;
      auto;
      match goal with
      | [H : In ?ϕ0 _ |- waiting (contn ?ϕ0)] => destruct H; subst; crush
      end.
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
    inversion H11; subst.                       (* Get rid of χ0, ψ0 in favour of χ, ϕ :: ψ *)
    apply self_config.                          (* Transform has_self_σ to a check that all frames in ϕ?1::ϕ?2::ψ are s.t. has_self_ϕ *)
    intros ϕ' Hin.                              (* Introduce the frame in the list *)
    inversion Hin as [| Hin'];                  (* Use inversion to say it's either the head ϕ?1 or in the tail ϕ?2::ψ *)
      auto;
      [subst|].                                   (* and substitute the head into place for simplification *)
    apply self_frm.                             (* Transform has_self_ϕ to a check `this` maps to an address in vMap, which locates an object in heap *)
    exists α, o.                                (* Pick α, o, the object being called (at ⌊y⌋=α), set to `this` in the new configuration *)
    split;                                      (* Split `this` maps to α, and α maps to o checks *)
      auto.                                       (* both of which are evident from the hypotheses *)
    inversion Hin';                             (* Use inversion to say it's either the head ϕ?2 or in the tail ψ  *)
      subst.                                      (* and substitute the head into place for simplification *)
    assert (Hinϕ : In ϕ (ϕ::ψ)). {              (* Assert that the original frame was in the original list *)
      apply in_eq.
    }
    apply H10 in Hinϕ.                            (* so we can prove it has_self_ϕ *)
    apply self_frm.                             (* Transform has_self_ϕ to a check `this` maps to an address in vMap, which locates an object in heap *)
    inversion Hinϕ.                             (* Inversion on the has_self_ϕ to not only get the exists, but also the equalities *)
    auto.                                         (* allowing the result to be solved, this also yield `In ϕ' ψ` *)
    apply H10.                                  (* Convert has_self_ϕ to `In ϕ' (ϕ :: ψ)` form from initial *)
    simpl in *.                                 (* Unfold `In` one step to `ϕ = ϕ' \/ In ϕ' ψ` *)
    right; assumption.

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

  - apply self_config;
      intros;
      apply self_frm;
      simpl_crush.
    destruct H0; subst;
      simpl.
    map_rewrite.
    unfold t_update; eq_auto.
    specialize (H8 ϕ (in_eq ϕ ψ)).
    inversion H8; subst; auto.
    specialize (H8 ϕ0 (in_cons ϕ ϕ0 ψ H0));
      inversion H8; auto.

  - (* field asgn*)
    inversion H12;
      subst.
    apply self_config;
      intros.
    inversion H;
      subst;
      remember {| cname := cname o; flds := update f v (flds o) |} as o'.
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

  - (* new *) (* written by mrr (based v. loosely on method case above), rewrite if bad *)
    inversion H14;
      subst. (* get rid of χ0 etc.*)
    assert (Hupdate : forall (tk tv: Type) (k: tk) (v: tv) `{Eq tk} m, update k v m k = Some v). {
      intros. unfold update, t_update. rewrite eqb_refl. reflexivity.
    }
    apply self_config.
    intros ϕ' Hin.
    inversion Hin as [| Hin'];
      auto;
      [subst|].
    remember {| cname := C; flds := fMap |} as o.
    apply self_frm.
    exists α, o.
    split;
      auto.
    inversion Hin' as [| Hin''];
      subst.
    assert (Hinϕ : In ϕ (ϕ::ψ)). {
      apply in_eq.
    }
    apply H13 in Hinϕ.
    remember {| cname := C; flds := fMap |} as o.
    apply self_frm.
    inversion Hinϕ; simpl in *.
    destruct H0 as [α' [o' [H0l  H0r]]].
    exists α', o'.
    split; [assumption |].
    apply update_doesn't_remove. assumption.
    apply fresh_heap_none in H2 as Hαnone. crush.

    apply has_self_update_χ_fresh. apply H2.
    assert (Hinϕ' : In ϕ' (ϕ::ψ)). {
      simpl. right. apply Hin''.
    }
    apply H13.
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
  - eapply reduction_preserves_config_has_self;
      eauto.
    eapply reductions_preserves_config_has_self;
      eauto.
  - eapply reduction_preserves_config_has_self;
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

  (** Case: e1 < e2 *)
  - inversion H0; subst; eauto.
    specialize (IHHeval1 (v_int i0));
      specialize (IHHeval2 (v_int i3));
      auto_specialize;
      crush.

  (** Case: e1 >= e2 *)
  - inversion H0; subst; eauto.
    specialize (IHHeval1 (v_int i0));
      specialize (IHHeval2 (v_int i3));
      auto_specialize;
      crush.

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

Lemma pair_reductions_transitive_alt :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ0, M1 ⦂ M2 ⦿ σ0 ⤳ σ1 ->
                       M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred.
  induction Hred;
    intros.
  - apply prs_trans with (σ:=σ1);
      eauto with loo_db.

  - eauto with loo_db.
Qed.

Lemma pair_reductions_transitive_single :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳ σ3 ->
                       M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
Proof.
  intros M1 M2 σ1 σ2 Hred.
  induction Hred;
    intros.
  - eapply pair_reductions_transitive_alt;
      eauto with loo_db.

  - eauto with loo_db.
Qed.

Lemma pair_reductions_transitive :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ3 ->
                       M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
Proof.
  intros M1 M2 σ1 σ2 Hred.
  induction Hred;
    intros.
  - eapply pair_reductions_transitive_alt;
      eauto with loo_db.

  - apply IHHred.
    eapply pair_reductions_transitive_alt;
      eauto.
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
    + exists {| cname := cname o; flds := update f v (flds o) |};
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
  edestruct reductions_preserves_addr_classes with (σ1:=σ1)(σ2:=σ); eauto;
    andDestruct;
    eauto.
  edestruct reduction_preserves_addr_classes;
    eauto;
    andDestruct;
    eexists;
    split;
    crush.
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

  specialize (IHHred α o1);
    auto_specialize;
    destruct_exists_loo;
    andDestruct.

  destruct (pair_reduction_preserves_addr_classes M1 M2 σ σ2)
    with
      (α:=α)(o1:=o)
    as [o' Hclass1];
    auto;
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
    inversion H10;
      subst;
      crush.
    inversion H9; subst.
    rewrite H1 in H11.
    inversion H11; subst.
    interpretation_rewrite.
    crush.

  - (* eAssgn *)
    inversion H3; subst; crush.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    eval_rewrite.
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

  - (* new *) (*entirely written by mrr, may be bad? *)
    simpl in *; subst.
    inversion H13; subst; crush.
    inversion H9; subst.
    assert (α0 = α). { apply (fresh_heap_unique χ0); assumption. }
    subst.
    rewrite H1 in H10. inversion H10; subst.
    rewrite H3 in H12. inversion H12; subst.
    rewrite <- H4 in H14. inversion H14; subst.
    assert (HfMapeq : fMap = fMap0). {
      apply functional_extensionality.
      intros x. inversion H7 as [H7a [H7b H7c]]; subst; simpl in *. inversion H17 as [H17a [H17b H17c]]; subst; simpl in *.
      remember (fMap x) as y. destruct y as [ y' |].
        + symmetry in Heqy. apply H8 in Heqy as Heqy'. subst. symmetry.
          inversion H7c as [ Hnil | f l Hnin Huniq Hcons ]; try (apply H7a in Heqy as Heqy').
            * rewrite <- Hnil in Heqy'. destruct Heqy'.
            * apply H17b in Heqy' as [x' Heqy'']. apply H18 in Heqy'' as Heqy'''. subst. assumption.
        + inversion H7c as [ Hnil | f l Hnin Huniq Hcons ].
            * rewrite <- Hnil in *. 
              assert (HnIn : forall t (x: t), In x nil = False). { crush. } 
              remember (H17a x) as H17ax. destruct HeqH17ax. rewrite (HnIn fld x) in H17ax.
              apply not_some_implies_none in H17ax. symmetry. assumption.
            * assert (Hnone_implies_not_some : forall tk `{Eq tk} tv (m : partial_map tk tv) k, None = m k -> ~(exists v, m k = Some v)). {
                intros a b Hab.
                crush.
              }
              assert (Hmodus_tollens : forall (p q : Prop), (p -> q) -> ~q -> ~p). { auto. }
              apply Hnone_implies_not_some in Heqy as Heqy'.
              remember (H7b x) as H7bx. apply Hmodus_tollens in H7bx as H7bx'; try (assumption).
              remember (H17a x) as H17ax.
              assert (H17axe : (exists b, fMap0 x = Some b) -> In x (c_flds CDef0)). {
                intros [ b' Hb' ]. apply (H17ax b'). apply Hb'.
              }
              apply Hmodus_tollens in H17axe; try (assumption).
              assert (H17ax' : forall b : value, fMap0 x <> Some b). {
                intros b' Hb'. apply H17axe. exists b'. assumption.
              }
              apply not_some_implies_none in H17ax'.
              symmetry. assumption.
    }
    rewrite <- HfMapeq. reflexivity.

(* alt formulation for proving a0 = a: 
    inversion H11; subst.
    inversion H2; subst.
    assert (α0 = α1). { apply (max_χ_injective obj χ0); assumption. }
*)

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

Lemma constrained_pair_reductions_is_reductions :
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

Lemma constrained_pair_reduction_is_reduction :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⌈⤳⌉ σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳ σ2.
Proof.
  intros.
  unfold constrained_pair_reduction in *.
  repeat destruct_exists_loo;
    andDestruct;
    subst.
  apply adapted_pair_reduction with (ψ:=ψ) in Ha0;
    auto.
Qed.

Lemma constrained_pair_reduction_unique :
  forall M1 M2 σ σ1, M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ1 ->
                forall σ2, M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ2 ->
                      σ1 = σ2.
Proof.
  intros.
  apply constrained_pair_reduction_is_reduction in H.
  apply constrained_pair_reduction_is_reduction in H0.
  eapply pair_reduction_unique;
    eauto.
Qed.

Ltac unique_reduction_auto :=  
    match goal with
    | [Ha : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σa,
            Hb : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σb |- _] =>
      eapply pair_reduction_unique with (σ1:=σa) in Hb;
        eauto;
        subst
    | [Ha : ?M ∙ ?σ ⤳ ?σa,
            Hb : ?M ∙ ?σ ⤳ ?σb |- _] =>
      eapply reduction_unique with (σ1:=σa) in Hb;
        eauto;
        subst
    | [Ha : ?M1 ⦂ ?M2 ⦿ ?σ ⌈⤳⌉ ?σa,
            Hb : ?M1 ⦂ ?M2 ⦿ ?σ ⌈⤳⌉ ?σb |- _] =>
      eapply constrained_pair_reduction_unique with (σ1:=σa) in Hb;
        eauto;
        subst
    end.

Lemma list_does_not_contain_itself :
  forall {A : Type} (l : list A) a,
    a :: l <> l.
Proof.
  intros A l;
    induction l;
    intros;
    crush.
Qed.

Reserved Notation "M '∙' σ1 '⤳⋆' σ2" (at level 40).

Inductive reductions : mdl -> config -> config -> Prop :=
| red_single : forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                          M ∙ σ1 ⤳⋆ σ2
| red_trans : forall M σ1 σ2 σ3, M ∙ σ1 ⤳ σ2 ->
                            M ∙ σ2 ⤳⋆ σ3 ->
                            M ∙ σ1 ⤳⋆ σ3

where "M '∙' σ1 '⤳⋆' σ2" := (reductions M σ1 σ2).

Hint Constructors reductions : loo_db.

Fixpoint stmt_size (s : stmt) : nat :=
  match s with
  | s1 ;; s2 => 1 + stmt_size s1 + stmt_size s2
  | s_if e s1 s2 => 1 + stmt_size s1 + stmt_size s2
  | _ => 1
  end.

Lemma stmt_size_eq :
  forall s1 s2, s1 = s2 ->
           stmt_size s1 = stmt_size s2.
Proof.
  intros;
    subst;
    auto.
Qed.

Inductive substmt : stmt -> stmt -> Prop :=
| sub_refl : forall s, substmt s s
| sub_trans : forall s1 s2 s3, substmt s1 s2 ->
                          substmt s2 s3 ->
                          substmt s1 s3
| sub_if1 : forall e s1 s2, substmt s1 (s_if e s1 s2)
| sub_if2 : forall e s1 s2, substmt s2 (s_if e s1 s2)
| sub_stmts1 : forall s1 s2, substmt s1 (s_stmts s1 s2)
| sub_stmts2 : forall s1 s2, substmt s2 (s_stmts s1 s2).

Hint Constructors substmt : loo_db.

Lemma merge_stmt_size :
  forall s1 s2, stmt_size (merge s1 s2) = 1 + stmt_size s1 + stmt_size s2.
Proof.
  intro s1;
    induction s1;
    intros;
    simpl;
    auto.
  rewrite IHs1_2;
    crush.
Qed.

Lemma acyclic_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intro Hcontra;
    subst;

    (* assignment *)
    try solve [simpl_crush; 
               match goal with
               | [Ha : _ = ?ϕ, Hb : contn ?ϕ = _ |-_] =>
                 rewrite <- Ha in Hb;
                 simpl in *;
                 inversion Hb;
                 subst
               end;
               match goal with
               | [H : ?s = _ ;; ?s |- _] =>
                 apply stmt_size_eq in H;
                 simpl in *;
                 crush
               end];
    (* meth & rtrn *)
    try solve [simpl_crush; eapply list_does_not_contain_itself; eauto];
    (* if *)
    try solve [simpl_crush;
               match goal with
               | [Ha : _ = ?ϕ, Hb : contn ?ϕ = _ |-_] =>
                 rewrite <- Ha in Hb;
                 simpl in *;
                 inversion Hb;
                 subst
               end;
               match goal with
               | [H : merge _ _ = _ ;; ?s |- _] =>
                 apply stmt_size_eq in H;
                 rewrite merge_stmt_size in H;
                 simpl in *;
                 crush
               end].
Qed.

Hint Resolve acyclic_reduction : loo_db.

Lemma acyclic_reductions :
  forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred.
  induction Hred.
  - eauto with loo_db.
  - intro Hcontra; subst. apply red_trans with (σ3:=σ1) in H as H'; try assumption. inversion H'; subst.
    + apply acyclic_reduction in H0. apply H0. reflexivity.
    (* + this should be induction but I don't get what I want for the base case?  *)
Admitted.

Lemma acyclic_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ1 <> σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred.
  induction Hred.
    - intros Hcontra; subst. inversion H; subst. inversion H0; subst.
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

  - admit.
    (* acyclic *)

  - admit.
    (* i'm not sure if this lemma is necessary *)
Admitted.

Lemma internal_reductions_external_initial :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 external_self M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    eauto.
Qed.

Lemma pair_reduction_external_self1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 external_self M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    auto.
  eapply internal_reductions_external_initial; eauto.
Qed.

Lemma pair_reduction_external_self2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 external_self M1 M2 σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    auto.
Qed.

Lemma pair_reductions_external_self1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 external_self M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto;
    try solve [eapply pair_reduction_external_self1; eauto].
Qed.

Lemma pair_reductions_external_self2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 external_self M1 M2 σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    [eapply pair_reduction_external_self2; eauto|].
  eapply pair_reduction_external_self2; eauto.
Qed.

Lemma external_self_head1 :
  forall M1 M2 χ ϕ ψ, external_self M1 M2 (χ, ϕ :: nil) ->
                 external_self M1 M2 (χ, ϕ :: ψ).
Proof.
  intros;
    unfold external_self, is_external in *;
    repeat destruct_exists_loo;
    andDestruct.
  exists α, o; split; auto.
Qed.

Lemma external_self_head2 :
  forall M1 M2 χ ϕ ψ, external_self M1 M2 (χ, ϕ :: ψ) ->
                 external_self M1 M2 (χ, ϕ :: nil).
Proof.
  intros;
    unfold external_self, is_external in *;
    repeat destruct_exists_loo;
    andDestruct.
  exists α, o; split; auto.
Qed.

(* call block *)

(*Lemma reduction_call_rtrn :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ ϕ, reductions M (χ, ϕ::nil) σ1 ->
                    (exists χ' χ'' ϕ' ψ' x y m β, reductions M (χ, ϕ::nil) (χ', ϕ'::ψ') /\
                    contn ϕ' = (c_stmt ())).*)
