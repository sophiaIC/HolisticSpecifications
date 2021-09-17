Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import operational_semantics.
Require Import specw.
Require Import classical.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module SpecWInference(L : LanguageDef).

  Import L.
  Module L_Classical := ClassicalProperties(L).
  Export L_Classical.

  Open Scope reduce_scope.
  Open Scope specw_scope.

  Declare Scope hoare_scope.

  Parameter entails_inf : mdl -> asrt -> asrt -> Prop.

  Notation "M '⊢' A1 '⊇' A2" := (entails_inf M A1 A2)(at level 40).

  Parameter entails_inf_soundness :
    forall M A1 A2, M ⊢ A1 ⊇ A2 ->
               entails M A1 A2.

  Lemma intrnl_reductions_start_external_self :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   external_self M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto.
  Qed.

  Hint Resolve intrnl_reductions_start_external_self : loo_db.

  Lemma pair_reduction_start_external_self :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   external_self M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      eauto with loo_db.
  Qed.

  Lemma pair_reduction_end_external_self :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   external_self M1 M2 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      eauto with loo_db.
  Qed.

  Hint Resolve pair_reduction_start_external_self pair_reduction_end_external_self : loo_db.

  Lemma pair_reductions_start_external_self :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   external_self M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      eauto with loo_db.
  Qed.

  Lemma pair_reductions_end_external_self :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   external_self M1 M2 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      eauto with loo_db.
  Qed.

  Hint Resolve pair_reductions_start_external_self pair_reductions_end_external_self : loo_db.

  Lemma initial_external :
    forall σ, initial σ ->
         forall M1 M2, external_self M1 M2 σ.
  Proof.
    intros.
    unfold initial, external_self, is_external in *.
    destruct_exists_loo;
      subst.
    match goal with
    | [|- exists _ _ _, (?χa, ?ϕa :: ?ψa) = _ /\ _] =>
      exists χa, ϕa, ψa
    end.
    split;
      auto.
    simpl.
    exists ObjectInstance;
      auto.
  Qed.

  Lemma reduction_config_components_exists :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      auto;
      intros;
      eauto.
  Qed.

  Hint Resolve reduction_config_components_exists : loo_db.

  Lemma intrnl_reductions_config_components_exists :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto;
      intros;
      subst;
      eauto with loo_db.
  Qed.

  Hint Resolve intrnl_reductions_config_components_exists : loo_db.

  Lemma pair_reduction_config_components_exists :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   exists χ ϕ ψ, σ2 = (χ, ϕ :: ψ).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto;
      intros;
      subst;
      eauto with loo_db.
  Qed.

  Lemma pair_reductions_config_components_exists :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall χ1 ϕ1 ψ1, σ1 = (χ1, ϕ1 :: ψ1) ->
                               exists χ2 ϕ2 ψ2, σ2 = (χ2, ϕ2 :: ψ2).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto;
      intros;
      subst;
      eauto with loo_db.
    let χ := fresh "χ" in
    destruct (pair_reduction_config_components_exists M1 M2 (χ1, ϕ1 :: ψ1) σ H) as [χ];
      auto;
      repeat destruct_exists_loo;
      subst.
    specialize (IHHred χ ϕ ψ).
    apply IHHred;
      auto.
  Qed.

  Ltac reduction_exists_self_object_disj_tactic :=
    disj_split;
    auto;
    subst;
    simpl in *.

  Ltac reduction_exists_self_object_match_tactic :=
     match goal with
     | [H : forall (ϕ : frame), ?ϕa = ϕ \/ _ -> _ |- _ ] =>
       specialize (H ϕa);
       destruct H;
       auto
     end;
     simpl in *;
     eauto.

  Lemma reduction_exists_self_object :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall χ1 ψ1
                 χ2 ψ2, σ1 = (χ1, ψ1) ->
                        σ2 = (χ2, ψ2) ->
                        (forall ϕ1, In ϕ1 ψ1 -> this ϕ1 ∈ χ1) ->
                        (forall ϕ2, In ϕ2 ψ2 -> this ϕ2 ∈ χ2).
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      simpl;
      simpl_crush;
      eauto;
      simpl_crush;
      simpl in *;
      auto;
      try solve [repeat reduction_exists_self_object_disj_tactic;
                 reduction_exists_self_object_match_tactic];
      try solve [reduction_exists_self_object_disj_tactic;
                 match goal with
                 | [H : forall (ϕ : frame), _ = _ \/ ?ϕa = ϕ \/ _ -> _ |- _ ] =>
                   specialize (H ϕa);
                     destruct H;
                     auto
                 end;
                   simpl in *;
                   eauto].

    - reduction_exists_self_object_disj_tactic.
      destruct (eq_dec self α);
        subst;
        simpl in *;
        eauto.
      + repeat map_rewrite;
          eauto.
      + repeat map_rewrite.
        reduction_exists_self_object_match_tactic.
      + destruct (eq_dec (this ϕ2) α);
          subst;
          eauto.
        * repeat map_rewrite.
          reduction_exists_self_object_match_tactic.
        * repeat map_rewrite.

    - reduction_exists_self_object_disj_tactic.
      destruct (eq_dec self (inc α));
        subst;
        simpl in *;
        eauto.
      + repeat map_rewrite;
          eauto.
      + repeat map_rewrite.
        reduction_exists_self_object_match_tactic.
      + destruct (eq_dec (this ϕ2) (inc α));
          subst;
          eauto.
        * rewrite e.
          repeat map_rewrite.
          reduction_exists_self_object_match_tactic.
        * repeat map_rewrite.

  Qed.

  Hint Resolve reduction_exists_self_object : loo_db.

  Lemma intrnl_reductions_exists_self_object :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   forall χ1 ψ1
                     χ2 ψ2, σ1 = (χ1, ψ1) ->
                            σ2 = (χ2, ψ2) ->
                            (forall ϕ1, In ϕ1 ψ1 -> this ϕ1 ∈ χ1) ->
                            (forall ϕ2, In ϕ2 ψ2 -> this ϕ2 ∈ χ2).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      subst;
      eauto with loo_db.
    edestruct (intrnl_reductions_config_components_exists M1 M2 (χ1, ψ1) σ Hred).
    repeat destruct_exists_loo;
      subst.
    eauto with loo_db.
  Qed.

  Hint Resolve intrnl_reductions_exists_self_object : loo_db.

  Lemma pair_reduction_exists_self_object :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   forall χ1 ψ1
                     χ2 ψ2, σ1 = (χ1, ψ1) ->
                            σ2 = (χ2, ψ2) ->
                            (forall ϕ1, In ϕ1 ψ1 -> this ϕ1 ∈ χ1) ->
                            (forall ϕ2, In ϕ2 ψ2 -> this ϕ2 ∈ χ2).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      subst;
      eauto with loo_db.
    edestruct (intrnl_reductions_config_components_exists M1 M2 (χ1, ψ1) σ);
      auto.
    repeat destruct_exists_loo;
      subst.
    eauto with loo_db.
  Qed.

  Lemma pair_reductions_exists_self_object :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall χ1 ψ1
                     χ2 ψ2, σ1 = (χ1, ψ1) ->
                            σ2 = (χ2, ψ2) ->
                            (forall ϕ1, In ϕ1 ψ1 -> this ϕ1 ∈ χ1) ->
                            (forall ϕ2, In ϕ2 ψ2 -> this ϕ2 ∈ χ2).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      subst.

    + simpl_crush.
      eauto.

    + edestruct (pair_reduction_config_components_exists M1 M2 (χ1, ψ1) σ);
        auto.
      repeat destruct_exists_loo;
        subst.
      eapply IHHred; eauto.
      eapply pair_reduction_exists_self_object;
        eauto.
  Qed.

  Lemma initial_exists_self_object :
    forall χ ψ, initial (χ, ψ) ->
           (forall ϕ, In ϕ ψ -> this ϕ ∈ χ).
  Proof.
    intros;
      match goal with
      | [ H : initial _ |- _] =>
        inversion H;
          subst
      end.
    simpl_crush.
    simpl in *.
    disj_split;
      [subst; simpl in *|crush].
    repeat map_rewrite;
      eauto.
  Qed.

  Lemma arising_exists_self_object :
    forall M1 M2 χ ψ, arising M1 M2 (χ, ψ) ->
                 forall ϕ, In ϕ ψ -> this ϕ ∈ χ.
  Proof.
    intros.
    unfold arising, initial in *.
    repeat (destruct_exists_loo;
            andDestruct);
      subst.
    eapply pair_reductions_exists_self_object; intros; eauto.
    simpl  in *;
      disj_split;
      subst;
      simpl in *;
      repeat map_rewrite;
      eauto;
      crush.
  Qed.

  Lemma arising_external :
    forall M1 M2 σ, arising M1 M2 σ ->
               external_self M1 M2 σ.
  Proof.
    intros.
    unfold arising in *.
    destruct_exists_loo;
      andDestruct.
    eauto with loo_db.
  Qed.

  Parameter conseq_true :
    forall M A, M ⊢ A ⊇ (a_true).

  Parameter conseq_or_comm :
    forall M A1 A2, M ⊢ A1 ∨ A2 ⊇ A2 ∨ A1.

  Parameter caller_ext :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 external.

  Parameter calls_recv :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 access α2.

  Parameter calls_param1 :
    forall M a1 a2 a3 m x β,
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ a_ a3 ⟧ β ⟩ ⊇ a1 access (a_ a3).

  Parameter class_internal :
    forall M α C, C ∈ M -> M ⊢ a_class (e_addr α) C ⊇ (a_ α) internal.

  Parameter recv_not_wrapped :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (α2).

  Parameter param_not_wrapped :
    forall M α1 α2 x p m β, ⟦ x ↦ p ⟧_∈ β -> M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (p).

  Parameter inside_wrapped :
    forall M α C Def, ⟦ C ↦ Def ⟧_∈ M ->
                 annot Def = inside ->
                 M ⊢ a_class (e_addr α) C ⊇ wrapped (a_ α).

  Parameter fld_type :
    forall M e C CDef f D, ⟦ C ↦ CDef ⟧_∈ M ->
                      ⟦ f ↦ (t_cls D) ⟧_∈ c_fields CDef ->
                      M ⊢ a_class e C ⊇ a_class ((e_acc_f e f)) D.

  Parameter conseq_absurd :
    forall M A, M ⊢ (a_exp (e_false)) ⊇ A.

  Parameter conseq_refl :
    forall M A, M ⊢ A ⊇ A.

  Parameter neg_false :
    forall M A, M ⊢ (A ∧ ¬ A) ⊇ (a_exp (e_false)).

  Parameter conseq_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊇ A2 ->
                       M ⊢ A2 ⊇ A3 ->
                       M ⊢ A1 ⊇ A3.

  Parameter conseq_excluded_middle :
    forall M A, M ⊢ (a_exp (e_true)) ⊇ (A ∨ ¬ A).

  Parameter eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).

  Parameter lt_implies_not_eq :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩻ e2)) ⊇ (¬ a_exp (e1 ⩵ e2)).

  Parameter not_false_is_true :
    forall M, M ⊢ (¬ a_exp (e_false)) ⊇ (a_exp (e_true)).

  Parameter true_is_not_false :
    forall M, M ⊢ (a_exp (e_true)) ⊇ (¬ a_exp (e_false)).

  Parameter and_true1 :
    forall M A, M ⊢ (A ∧ (a_exp (e_true))) ⊇ A.

  Parameter and_true2 :
    forall M A, M ⊢ A ⊇ (A ∧ (a_exp (e_true))).

  Parameter and_comm :
    forall M A1 A2 A, M ⊢ (A1 ∧ A2) ⊇ A ->
                 M ⊢ (A2 ∧ A1) ⊇ A.

  Parameter and_assoc1 :
    forall M A A1 A2 A3, M ⊢ (A1 ∧ A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ (A2 ∧ A3)) ⊇ A.

  Parameter and_assoc2 :
    forall M A A1 A2 A3, M ⊢ A1 ∧ (A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ A2) ∧ A3 ⊇ A.

  Parameter and_consequence1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                   M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2.

  Parameter and_consequence2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                   M ⊢ A1 ∧ A2 ⊇ A1 ∧ A2'.

  Parameter conseq_and1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 ∧ A2 ⊇ A1'.

  Parameter conseq_and2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                   M ⊢ A1 ∧ A2 ⊇ A2'.

  Parameter conseq_and :
    forall M A A1 A2,  M ⊢ A ⊇ A1 ->
                  M ⊢ A ⊇ A2 ->
                  M ⊢ A ⊇ A1 ∧ A2.

  Parameter conseq_ex1 :
    forall M A1 A2, (forall x, M ⊢ [x /s 0] A1 ⊇ A2) ->
               M ⊢ (∃x.[A1]) ⊇ A2.

  Parameter conseq_ex_and1 :
    forall M A1 A2 A, (forall x, M ⊢ A1 ∧ ([x /s 0] A2) ⊇ A) ->
                 M ⊢ A1 ∧ (∃x.[A2]) ⊇ A.

  Parameter conseq_ex2 :
    forall M A1 A2, (exists x, M ⊢ A1 ⊇ [x /s 0] A2) ->
               M ⊢ A1 ⊇ ∃x.[A2].

  Parameter subst_eq :
    forall M x y z A1 A2, M ⊢ [y /s z] A1 ⊇ A2 ->
                     M ⊢ [x /s z] (a_exp (e♢ z ⩵ e_val y) ∧ A1) ⊇ A2.

  Parameter caller_unique :
    forall M v v' a a' m m' β β',
      M ⊢ (av_ v) calls a ◌ m ⟨ β ⟩ ∧ (av_ v') calls a' ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).

  Parameter recv_unique :
    forall M v v' a a' m m' β β',
      M ⊢ a calls (av_ v) ◌ m ⟨ β ⟩ ∧ a' calls (av_ v) ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).

  Parameter param_unique :
    forall M a1 a1' a2 a2' m m' x v v' β β',
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ (av_ v) ⟧ β ⟩ ∧ a1' calls a2' ◌ m' ⟨ ⟦ x ↦ (av_ v') ⟧ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).

  Parameter neg_distr_and_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∧ A2) ⊇ ¬ A1 ∨ ¬ A2.

  Parameter neg_distr_and_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∨ ¬ A2 ⊇ ¬ (A1 ∧ A2).

  Parameter neg_distr_or_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∨ A2) ⊇ ¬ A1 ∧ ¬ A2.

  Parameter neg_distr_or_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∧ ¬ A2 ⊇ ¬ (A1 ∨ A2).

  Parameter or_l :
    forall M A A1 A2, M ⊢ A ⊇ A1 ->
                 M ⊢ A ⊇ A1 ∨ A2.

  Parameter or_r :
    forall M A A1 A2, M ⊢ A ⊇ A2 ->
                 M ⊢ A ⊇ A1 ∨ A2.

  Parameter or_lr :
    forall M A1 A2 A, M ⊢ A1 ⊇ A ->
                 M ⊢ A2 ⊇ A ->
                 M ⊢ (A1 ∨ A2) ⊇ A.

  Parameter conseq_exp_eq_neq :
    forall M e1 e2 e3, M ⊢ (a_exp (e1 ⩵ e2)) ∧ (¬ a_exp (e2 ⩵ e3)) ⊇ (¬ a_exp (e1 ⩵ e3)).

  Parameter conseq_ex_and_expand_r_1 :
    forall A2 M A1, M ⊢ (∃x.[A1]) ∧ A2 ⊇ (∃x.[A1 ∧ (A2 ↑ 0)]).

  Parameter conseq_ex_and_expand_l_1 :
    forall A2 M A1, M ⊢ A1 ∧ (∃x.[A2]) ⊇ (∃x.[(A1 ↑ 0) ∧ A2]).

  Parameter conseq_and_components :
    forall M A1 A2 A1' A2', M ⊢ A1 ⊇ A1' ->
                       M ⊢ A2 ⊇ A2' ->
                       M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2'.

  Parameter conseq_not_not1 :
    forall M A, M ⊢ ¬ (¬ A) ⊇ A.

  Parameter conseq_not_not2 :
    forall M A, M ⊢ A ⊇ ¬ (¬ A).

  Parameter or_dumb1 :
    forall M A, M ⊢ A ⊇ A ∨ A.

  Parameter or_dumb2 :
    forall M A, M ⊢ A ∨ A ⊇ A.

  Parameter conseq_not_wrapped :
    forall M x y, M ⊢ x external ∧ x access y ⊇ ¬ wrapped y.

  Parameter calls_implies_concrete_parameters :
    forall M x y m β, (forall β', β <> (fun v => Some (av_ v)) ∘ β') -> M ⊢ x calls y ◌ m ⟨ β ⟩ ⊇ (a_false).

  Parameter and_distr1:
    forall M A1 A2 A3, M ⊢ ((A1 ∨ A2) ∧ A3) ⊇ ((A1 ∧ A3) ∨ (A2 ∧ A3)).

  Parameter and_distr2:
    forall M A1 A2 A3, entails M ((A1 ∧ A3) ∨ (A2 ∧ A3)) ((A1 ∨ A2) ∧ A3).

  Parameter and_distr_trans1:
    forall M A1 A2 A3 A, M ⊢ ((A1 ∨ A2) ∧ A3) ⊇ A ->
                    M ⊢ ((A1 ∧ A3) ∨ (A2 ∧ A3)) ⊇ A.

  Parameter and_distr_trans2:
    forall M A1 A2 A3 A, M ⊢ ((A1 ∧ A3) ∨ (A2 ∧ A3)) ⊇ A ->
                    M ⊢ ((A1 ∨ A2) ∧ A3) ⊇ A.

End SpecWInference.


(*


  Lemma conseq_true :
    forall M A, M ⊢ A ⊇ (a_true).
  Proof.
    intros.
    apply ent;
      intros.
    auto with specw_db.
  Qed.

  Lemma conseq_or_comm :
    forall M A1 A2, M ⊢ A1 ∨ A2 ⊇ A2 ∨ A1.
  Proof.
    intros.
    apply ent;
      intros.
    a_prop;
      disj_split;
      auto.
  Qed.

  Lemma caller_ext :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 external.
  Proof.
    intros.
    apply ent;
      intros.
    match goal with
    | [H : _ ◎ _ ⊨ _ calls _ ◌ _ ⟨ _ ⟩ |- _] =>
      inversion H;
        subst
    end.
    match goal with
    | [H : makes_call _ _ _ _ _  |- _ ] =>
      inversion H;
        subst
    end.
    apply sat_extrn.
    match goal with
    | [H : arising _ _ (_, ?ϕa :: _) |- _ ] =>
      apply arising_external in H
    end.
    unfold external_self, is_external in *.
    repeat destruct_exists_loo;
      andDestruct;
      subst.
    repeat destruct_exists_loo;
      andDestruct;
      subst.
    simpl_crush.
    eapply is_ext;
    eauto.
  Qed.

  Lemma calls_recv :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 access α2.
  Proof.
    intros.
    apply ent;
      intros.
    match goal with
    | [H : _ ◎ _ ⊨ _ calls _ ◌ _ ⟨ _ ⟩ |- _ ] =>
      inversion H;
        subst
    end.
    match goal with
    | [H : makes_call _ _ _ _ _  |- _ ] =>
      inversion H;
        subst
    end.
    apply sat_access.
    apply acc_lcl with (x:=y).
    match goal with
    | [|- exists _, In _ (?ϕ :: _) /\ _ ] =>
      exists ϕ;
        repeat split;
        auto
    end.
    apply in_eq.

  Qed.

  Lemma calls_param1 :
    forall M a1 a2 a3 m x β,
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ a_ a3 ⟧ β ⟩ ⊇ a1 access (a_ a3).
  Proof.
    intros.
    apply ent;
      intros.
    match goal with
    | [H : _ ◎ _ ⊨ _ calls _ ◌ _ ⟨ _ ⟩ |- _ ] =>
      inversion H;
        subst
    end.
    match goal with
    | [H : makes_call _ _ _ _ _ |- _ ] =>
      inversion H;
        subst
    end.
    apply sat_access.

    apply acc_lcl with (x:=x).
    match goal with
    | [ |- exists _, In _ (?ϕ :: _) /\ _ ] =>
      exists ϕ;
        repeat split;
        simpl in *;
        auto
    end. 
  Admitted.

  Lemma class_internal :
    forall M α C, C ∈ M -> M ⊢ a_class (e_addr α) C ⊇ (a_ α) internal.
  Admitted.

  Lemma recv_not_wrapped :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (α2).
  Admitted.

  Lemma param_not_wrapped :
    forall M α1 α2 x p m β, ⟦ x ↦ p ⟧_∈ β -> M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (p).
  Admitted.

  Lemma inside_wrapped :
    forall M α C Def, ⟦ C ↦ Def ⟧_∈ M ->
                 annot Def = inside ->
                 M ⊢ a_class (e_addr α) C ⊇ wrapped (a_ α).
  Admitted.

  Lemma fld_type :
    forall M e C CDef f D, ⟦ C ↦ CDef ⟧_∈ M ->
                           ⟦ f ↦ (t_cls D) ⟧_∈ c_fields CDef ->
                           M ⊢ a_class e C ⊇ a_class ((e_acc_f e f)) D.
  Admitted.

  Lemma conseq_absurd :
    forall M A, M ⊢ (a_exp (e_false)) ⊇ A.
  Admitted.

  Lemma conseq_refl :
    forall M A, M ⊢ A ⊇ A.
  Admitted.

  Lemma neg_false :
    forall M A, M ⊢ (A ∧ ¬ A) ⊇ (a_exp (e_false)).
  Admitted.

  Lemma conseq_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊇ A2 ->
                       M ⊢ A2 ⊇ A3 ->
                       M ⊢ A1 ⊇ A3.
  Admitted.

  Lemma conseq_excluded_middle :
    forall M A, M ⊢ (a_exp (e_true)) ⊇ (A ∨ ¬ A).
  Admitted.

  Lemma eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).
  Admitted.

  Lemma lt_implies_not_eq :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩻ e2)) ⊇ (¬ a_exp (e1 ⩵ e2)).
  Admitted.

  Lemma not_false_is_true :
    forall M, M ⊢ (¬ a_exp (e_false)) ⊇ (a_exp (e_true)).
  Admitted.

  Lemma true_is_not_false :
    forall M, M ⊢ (a_exp (e_true)) ⊇ (¬ a_exp (e_false)).
  Admitted.

  Lemma and_true1 :
    forall M A, M ⊢ (A ∧ (a_exp (e_true))) ⊇ A.
  Admitted.

  Lemma and_true2 :
    forall M A, M ⊢ A ⊇ (A ∧ (a_exp (e_true))).
  Admitted.

  Lemma and_comm :
    forall M A1 A2 A, M ⊢ (A1 ∧ A2) ⊇ A ->
                 M ⊢ (A2 ∧ A1) ⊇ A.
  Admitted.

  Lemma and_assoc1 :
    forall M A A1 A2 A3, M ⊢ (A1 ∧ A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ (A2 ∧ A3)) ⊇ A.
  Admitted.

  Lemma and_assoc2 :
    forall M A A1 A2 A3, M ⊢ A1 ∧ (A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ A2) ∧ A3 ⊇ A.
  Admitted.

  Lemma and_consequence1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                   M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2.
  Admitted.

  Lemma and_consequence2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                   M ⊢ A1 ∧ A2 ⊇ A1 ∧ A2'.
  Admitted.

  Lemma conseq_and1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 ∧ A2 ⊇ A1'.
  Admitted.

  Lemma conseq_and2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                        M ⊢ A1 ∧ A2 ⊇ A2'.
  Admitted.

  Lemma conseq_and :
    forall M A A1 A2,  M ⊢ A ⊇ A1 ->
                  M ⊢ A ⊇ A2 ->
                  M ⊢ A ⊇ A1 ∧ A2.
  Admitted.

  (* (∀ M ⊢ [y / x] \longright)*)
  Lemma conseq_ex1 :
    forall M A1 A2, (forall x, M ⊢ [x /s 0] A1 ⊇ A2) ->
               M ⊢ (∃x.[A1]) ⊇ A2.
  Proof.
    intros.
    apply ent;
      intros.
    inversion H1;
      subst.
    specialize (H x).
    inversion H;
      subst.
    eapply H2;
      eauto.
  Qed.

(*)  Lemma conseq_ex_and1 :
    forall M A1 A2, M ⊢ (∃x.[A1]) ∧ A2 ⊇ (∃x.[A1 ∧ A)])*)

  Lemma conseq_ex_and1 :
    forall M A1 A2 A, (forall x, M ⊢ A1 ∧ ([x /s 0] A2) ⊇ A) ->
                 M ⊢ A1 ∧ (∃x.[A2]) ⊇ A.
  Proof.
    intros.
    apply ent;
      intros.
    a_prop.
    match goal with
    | [H : _ ◎ _ ⊨ ∃x.[_] |- _] =>
      inversion H;
        subst
    end.
    eauto with specw_db.
  Qed.

  Lemma conseq_ex2 :
    forall M A1 A2, (exists x, M ⊢ A1 ⊇ [x /s 0] A2) ->
               M ⊢ A1 ⊇ ∃x.[A2].
  Admitted.

  Lemma subst_eq :
    forall M x y z A1 A2, M ⊢ [y /s z] A1 ⊇ A2 ->
                     M ⊢ [x /s z] (a_exp (e♢ z ⩵ e_val y) ∧ A1) ⊇ A2.
  Admitted.

  Lemma caller_unique :
    forall M v v' a a' m m' β β',
      M ⊢ (av_ v) calls a ◌ m ⟨ β ⟩ ∧ (av_ v') calls a' ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma recv_unique :
    forall M v v' a a' m m' β β',
      M ⊢ a calls (av_ v) ◌ m ⟨ β ⟩ ∧ a' calls (av_ v) ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma param_unique :
    forall M a1 a1' a2 a2' m m' x v v' β β',
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ (av_ v) ⟧ β ⟩ ∧ a1' calls a2' ◌ m' ⟨ ⟦ x ↦ (av_ v') ⟧ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma neg_distr_and_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∧ A2) ⊇ ¬ A1 ∨ ¬ A2.
  Admitted.

  Lemma neg_distr_and_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∨ ¬ A2 ⊇ ¬ (A1 ∧ A2).
  Admitted.

  Lemma neg_distr_or_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∨ A2) ⊇ ¬ A1 ∧ ¬ A2.
  Admitted.

  Lemma neg_distr_or_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∧ ¬ A2 ⊇ ¬ (A1 ∨ A2).
  Admitted.

  Lemma or_l :
    forall M A A1 A2, M ⊢ A ⊇ A1 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_r :
    forall M A A1 A2, M ⊢ A ⊇ A2 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_lr :
    forall M A1 A2 A, M ⊢ A1 ⊇ A ->
                 M ⊢ A2 ⊇ A ->
                 M ⊢ (A1 ∨ A2) ⊇ A.
  Admitted.
 *)
