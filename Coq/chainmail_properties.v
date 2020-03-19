Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import chainmail.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma adaptation_exists :
  forall χ1 ϕ1 ψ1
    χ2 ϕ2 ψ2, finite_ϕ ϕ1 ->
              finite_ϕ ϕ2 ->
              not_stuck_ϕ ϕ2 ->
              forall σ1 σ2, σ1 = (χ1, ϕ1::ψ1) ->
                       σ2 = (χ2, ϕ2::ψ2) ->
                       exists σ, σ1 ◁ σ2 ≜ σ.
Proof.
  intros; subst.

  inversion H1; subst.

  remember (vMap ϕ1) as β1.
  remember (vMap ϕ2) as β2.
  let H := fresh in
  (destruct (@disjointedness_for_finite_variable_maps value value β1)
     with (g:=β2)(s:=s)
    as [f H];
   try solve [finite_auto; subst; eauto with map_db];
   destruct H as [f'];
   andDestruct).

  exists (χ2, (frm (f ∘ β2 ∪ β1) (c_stmt (❲ f' ↦ s ❳))::ψ2)).
  apply a_adapt
    with
      (χ:=χ1)(ψ:=ψ1)(ϕ:=ϕ1)(ϕ':=ϕ2)(c:=contn ϕ1)
      (β:=β1)(β':=β2)(f':=f')
      (s:=s)
      (f:=f);
    auto with map_db.
  - destruct ϕ1; crush.
  - destruct ϕ2; crush.
Qed.

Hint Resolve adaptation_exists : loo_db.

Lemma adaptation_exists_wf :
  forall σ1 σ2, σ_wf σ1 ->
                σ_wf σ2 ->
                exists σ, σ1 ◁ σ2 ≜ σ.
Proof.
  intros σ1 σ2; intros.
  repeat match goal with
         | [H : σ_wf ?σ |- _] =>
           inversion H; subst;
             clear H
         end.
  destruct σ1 as [χ1 ψ1];
    destruct σ2 as [χ2 ψ2].
  not_stuck_auto;
    repeat destruct_exists_loo;
    simpl in *;
    andDestruct;
    subst.
  unfold finite_σ in *;
    unfold snd in *.
  unfold finite_ψ in *.
  repeat match goal with
         | [H : forall ϕ', In ϕ' (?ϕ::?ψ) -> finite_ϕ ϕ' |- _ ] =>
           specialize (H ϕ (in_eq ϕ ψ))
         end.
  eauto with loo_db.
Qed.



Lemma initial_wf :
  forall σ, initial σ ->
       σ_wf σ.
Proof.
  intros σ Hinit;
    inversion Hinit.
  destruct H as [ϕ];
    andDestruct;
    subst.
  apply config_wf;
    auto.
  
  apply self_config;
    intros.
  inversion H;
    [subst|crush].
  apply self_frm.
  exists x, ObjectInstance;
    split;
    auto.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
  
  waiting_auto.
  exists ϕ, nil;
    simpl;
    split;
    intros;
    crush.
Qed.

Hint Resolve initial_wf : loo_db.

Lemma fresh_x_ϕ_implies_σ :
  forall x ϕ A, fresh_x x ϕ A ->
           forall χ ψ, fresh_x_σ x (χ, ϕ::ψ) A.
Proof.
  intros x ϕ A Hfresh χ ψ;
    unfold fresh_x_σ;
    exists χ, ϕ, ψ;
    split;
    auto.
Qed.

Hint Resolve fresh_x_ϕ_implies_σ : loo_db.

Lemma fresh_x_σ_implies_ϕ :
  forall x χ ϕ ψ A, fresh_x_σ x (χ, ϕ::ψ) A ->
               fresh_x x ϕ A.
Proof.
  intros x χ ϕ ψ A Hfresh;
    unfold fresh_x_σ in *;
    repeat destruct_exists;
    andDestruct;
    match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst; clear H
    end;
    auto.
Qed.

Hint Resolve fresh_x_σ_implies_ϕ : loo_db.
  
Lemma has_self_update_ϕ_map :
  forall χ ϕ, has_self_ϕ χ ϕ ->
         forall x v A, fresh_x x ϕ A ->
                  has_self_ϕ χ (update_ϕ_map ϕ x v).
Proof.
  intros.

  inversion H;
    subst.
  apply self_frm.
  destruct H1 as [α Htmp];
    destruct Htmp as [o];
    andDestruct.
  exists α, o;
    split;
    auto.
  unfold update_ϕ_map, update, t_update;
    simpl.
  destruct x as [n];
    destruct n as [|n'];
    auto.
  inversion H0;
    subst;
    simpl in *.
  unfold mapp, stackMap, mapp in H1;
    unfold this in Ha; rewrite Ha in H1;
      crush.
Qed.

Hint Resolve has_self_update_ϕ_map : loo_db.

Lemma has_self_update_ϕ_map_σ :
  forall χ ϕ, has_self_ϕ χ ϕ ->
         forall x v ψ A, fresh_x_σ x (χ, ϕ::ψ) A ->
                    has_self_ϕ χ (update_ϕ_map ϕ x v).
Proof.
  intros.

  match goal with
  | [H : fresh_x_σ _ _ _ |- _] =>
    inversion H; subst; repeat destruct_exists; andDestruct
  end.
  match goal with
  | [H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
  end.
  eauto with loo_db.

Qed.

Hint Resolve has_self_update_ϕ_map_σ : loo_db.

Lemma has_self_update_σ_map :
  forall σ, has_self_σ σ ->
       forall x v A, fresh_x_σ x σ A ->
                has_self_σ (update_σ_map σ x v).
Proof.
  intros σ;
    intros.
  inversion H0; subst;
    repeat destruct_exists;
    andDestruct;
    subst.
  auto.

  apply self_config; intros;
    simpl in *.

  destruct H1; subst.

  - apply has_self_update_ϕ_map with (A:=A); auto.
    inversion H; subst.
    apply H2, in_eq.

  - inversion H; subst.
    apply H3, in_cons; auto.
Qed.

Hint Resolve has_self_update_σ_map : loo_db.

Lemma wf_update_σ_map :
  forall σ, σ_wf σ ->
       forall x α A, fresh_x_σ x σ A ->
                σ_wf (update_σ_map σ x α).
Proof.
  intros σ Hwf; intros.
  inversion Hwf;
    subst.
  apply config_wf;
    eauto with loo_db.
Qed.

Lemma adaptation_preserves_mapping :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall z (v : value), mapp σ1 z = Some v ->
                              mapp σ z = Some v.
Proof.
  intros.
  inversion H;
    subst.

  repeat map_rewrite; simpl.
  apply extend_some_2; auto.
  apply disjoint_dom_symmetry.
  eapply disjoint_composition; auto with map_db.
Qed.

Lemma update_fresh_preserves_map :
  forall x σ A, fresh_x_σ x σ A ->
           forall z v v', mapp σ z = Some v ->
                     mapp (update_σ_map σ x v') z = Some v.
Proof.
  intros x σ A Hfrsh;
    inversion Hfrsh;
    subst;
    intros.

  unfold fresh_x_σ in *;
    repeat destruct_exists;
    andDestruct;
    subst.
  match goal with
  | [H : (_, _) = (_, _) |- _] =>
    inversion H; subst
  end.
  repeat map_rewrite;
    simpl in *;
    repeat map_rewrite.
  inversion Hb; subst.
  destruct (eq_dec x z);
    subst;
    eq_auto;
    crush.
Qed.

Lemma fresh_and_elim :
  forall x σ A1 A2,
    fresh_x x σ (A1 ∧ A2) ->
    fresh_x x σ A1 /\ fresh_x x σ A2.
Proof.
  intros.
  inversion H;
    subst.

  inversion H1;
    subst;
    auto with chainmail_db.
Qed.

Lemma fresh_and_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ∧ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto with chainmail_db.
Qed.

Lemma fresh_arr_elim :
  forall x σ A1 A2,
    fresh_x x σ (A1 ⇒ A2) ->
    fresh_x x σ A1 /\ fresh_x x σ A2.
Proof.
  intros.
  inversion H;
    subst.

  inversion H1;
    subst;
    auto with chainmail_db.
Qed.

Lemma fresh_arr_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ⇒ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto with chainmail_db.
Qed.

Lemma fresh_all_elim :
  forall x σ A,
    fresh_x x σ (∀x∙A) ->
    fresh_x x σ A.
Proof.
  intros.
  inversion H;
    subst;
    inversion H1;
    auto with chainmail_db.
Qed.

Lemma fresh_all_intro :
  forall x σ A,
    fresh_x x σ A ->
    fresh_x x σ (∀x∙A).
Proof.
  intros.
  inversion H; subst; auto with chainmail_db.
Qed.

Lemma fresh_notin :
  forall x σ A1 A2,
    fresh_x x σ A1 ->
    notin_Ax A2 x ->
    fresh_x x σ A2.
Proof.
  intros x σ A1 A2 Hfrsh Hnotin.
  inversion Hfrsh; auto with chainmail_db.
Qed.

Parameter fresh_exists_for_expression :
  forall e, exists x, notin_exp e x.

Parameter fresh_exists_for_assertion :
  forall A, exists x, notin_Ax A x.


Parameter fresh_x_exists_for_finite_config :
  forall σ, finite_σ σ ->
       forall A, exists x, fresh_x_σ x σ A.

Parameter fresh_address_rename_equality_heap :
  forall α1 α2 (χ : heap),  χ α1 = None ->
                       χ α2 = None ->
                       forall o, update α1 o χ = update α2 o χ.

Parameter fresh_address_rename_equality_state :
  forall α1 α2 (χ : heap),  χ α1 = None ->
                       χ α2 = None ->
                       forall m (x:var), update x (v_addr α1) m = update x (v_addr α2) m.

Lemma initial_heap_wf :
  forall σ, initial σ ->
       forall M, M_wf M ->
            χ_wf M (fst σ).
Proof.
  intros σ Hinit;
    destruct Hinit as [α Hinit];
    destruct Hinit as [ϕ Hinit];
    andDestruct;
    subst;
    intros.
  apply heap_wf;
    intros.
  simpl in H0; inversion H0; subst.
  update_auto;
    [exists ObjectDefn;
     split; simpl; auto;
     try solve [obj_defn_rewrite; auto];
     crush
    |empty_auto].
Qed.

Ltac initial_heap_wf_auto :=
  match goal with
  | [H : initial ?σ |- χ_wf ?M (fst ?σ)] => eapply initial_heap_wf; eauto
  end.

Lemma arising_heap_wf :
  forall M1 M2 σ, arising M1 M2 σ ->
             M_wf M1 ->
             M_wf M2 ->
             forall M, M1 ⋄ M2 ≜ M ->
                  χ_wf M (fst σ).
Proof.
  intros.
  inversion H; subst.
  pair_reduces_heap_wf_auto.
  initial_heap_wf_auto.
  linking_wf.
Qed.

Lemma arising_wf :
  forall M1 M2 σ, arising M1 M2 σ ->
             σ_wf σ.
Proof.
  intros M1 M2 σ Harise.
  inversion Harise;
    subst.
  eapply pair_reductions_preserves_config_wf; eauto with loo_db.
Qed.

Hint Resolve arising_wf : loo_db.
