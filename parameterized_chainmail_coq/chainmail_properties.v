Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import chainmail.
Require Import classical.
Require Import hoare.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module ChainmailProperties(L : LanguageDef).

  Import L.
  Module L_Classical := ClassicalProperties(L).
  Import L_Classical.
  Import L_Chainmail.
  Import L_Semantics.
  Module L_Hoare := Hoare(L).
  Import L_Hoare.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.
  Open Scope list_scope.

  Lemma prop_change_pair_reduction :
    forall M1 M2 σ1 σ2,
      M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
      forall (P : mdl -> mdl -> config -> Prop),
        P M1 M2 σ1 ->
        ~ P M1 M2 σ2 ->
        exists σ σ', M1 ⦂ M2 ⦿ σ ⤳ σ' /\
                P M1 M2 σ /\ ~ P M1 M2 σ' /\
                (σ = σ1 \/ M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ) /\
                (σ' = σ2 \/ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros.

    - repeat eexists;
        eauto.

    - match goal with
      | [P : mdl -> mdl -> config -> Prop,
             _ : ?M1 ⦂ ?M2 ⦿ _ ⤳ ?σ |- _] =>
        destruct (excluded_middle (P M1 M2 σ))
      end.

      + match goal with
        | [P' : mdl -> mdl -> config -> Prop,
                H' : forall _ : mdl -> mdl -> config -> Prop, _ |- _] =>
          specialize (H' P')
        end;
          repeat auto_specialize;
          repeat destruct_exists_loo;
          andDestruct.
        repeat disj_split;
          subst;
          try solve [repeat eexists;
                     eauto with reduce_db].

      + repeat eexists;
          eauto.

  Qed.

  Lemma reduction_stack_append :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall ψ, M ∙ (σ1 ◁ ψ) ⤳ (σ2 ◁ ψ).
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      repeat simpl_crush;
      unfold stack_append in *;
      simpl in *;
      subst;
      try solve [eauto with reduce_db].

    - match goal with
      | [H : _ (cname ?o) = Some ?CDef |- _] =>
        apply r_call with (o:=o)(C:=cname o)(CDef:=CDef);
          auto
      end;
        try solve [visible_stack_append_auto].

      + intros.
        match goal with
        | [Ha : forall (_ : name)(_ : value), ?m _ = Some _ -> _,
             Hb : ?m ?x = Some ?v |- _] =>
          specialize (Ha x v)
        end;
          auto_specialize.
        match goal with
        | [H : visible_r ?M (?χ, ?ψ) ?α ?v
           |- visible_r ?M (?χ, _ :: ?ψ') ?α ?v] =>
          idtac
        end.
        visible_stack_append_auto.

    - apply r_rtrn_1;
        simpl in *.
        visible_stack_append_auto.

    - apply r_rtrn_2;
        simpl in *.
        visible_stack_append_auto.

    - apply r_acc;
        auto;
        try solve [visible_stack_append_auto].

    - apply r_mut;
        auto;
        try solve [visible_stack_append_auto].

    - apply r_new;
        auto;
        try solve [visible_stack_append_auto].

  Qed.

  Hint Rewrite reduction_stack_append : reduce_db.
  Hint Resolve reduction_stack_append : reduce_db.

  Ltac internal_external_stack_append :=
    match goal with
    | [H : is_internal ?M1 ?M2 ?σ
       |- is_internal ?M1 ?M2 (?σ ◁ _) ] =>
      apply is_internal_stack_append;
      auto
    | [H : internal_self ?M1 ?M2 ?σ
       |- internal_self ?M1 ?M2 (?σ ◁ _) ] =>
      apply internal_self_stack_append;
      auto
    | [H : is_external ?M1 ?M2 ?σ
       |- is_external ?M1 ?M2 (?σ ◁ _) ] =>
      apply is_external_stack_append;
      auto
    | [H : external_self ?M1 ?M2 ?σ
       |- external_self ?M1 ?M2 (?σ ◁ _) ] =>
      apply external_self_stack_append;
      auto

    | [H : is_internal ?M1 ?M2 (?χ, ?ϕ :: nil)
       |- is_internal ?M1 ?M2 (?χ, ?ϕ :: ?ψ') ] =>
      apply is_internal_stack_append with (ψ:=ψ') in H;
      auto
    | [H : internal_self ?M1 ?M2 (?χ, ?ϕ :: nil)
       |- internal_self ?M1 ?M2 (?χ, ?ϕ :: ?ψ') ] =>
      apply internal_self_stack_append with (ψ:=ψ') in H;
      auto
    | [H : is_external ?M1 ?M2 (?χ, ?ϕ :: nil)
       |- is_external ?M1 ?M2 (?χ, ?ϕ :: ?ψ') ] =>
      apply is_external_stack_append with (ψ:=ψ') in H;
      auto
    | [H : external_self ?M1 ?M2 (?χ, ?ϕ :: nil)
       |- external_self ?M1 ?M2 (?χ, ?ϕ :: ?ψ') ] =>
      apply external_self_stack_append with (ψ:=ψ') in H;
      auto

    | [H : is_internal ?M1 ?M2 ?σ
       |- is_internal ?M1 ?M2 (fst ?σ, snd ?σ ++ ?ψ') ] =>
      apply is_internal_stack_append with (ψ:=ψ') in H;
      auto
    | [H : internal_self ?M1 ?M2 ?σ
       |- internal_self ?M1 ?M2 (fst ?σ, snd ?σ ++ ?ψ') ] =>
      apply internal_self_stack_append with (ψ:=ψ') in H;
      auto
    | [H : is_external ?M1 ?M2 ?σ
       |- is_external ?M1 ?M2 (fst ?σ, snd ?σ ++ ?ψ') ] =>
      apply is_external_stack_append with (ψ:=ψ') in H;
      auto
    | [H : external_self ?M1 ?M2 ?σ
       |- external_self ?M1 ?M2 (fst ?σ, snd ?σ ++ ?ψ') ] =>
      apply external_self_stack_append with (ψ:=ψ') in H;
      auto
    end.

  Lemma internal_reductions_stack_append :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳… (σ2 ◁ ψ).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      subst.

    - eapply pr_single;
        eauto with reduce_db;
        try solve [internal_external_stack_append].

    - eapply pr_trans;
        eauto with reduce_db;
        try solve [internal_external_stack_append].

  Qed.

  Hint Rewrite internal_reductions_stack_append : reduce_db.
  Hint Resolve internal_reductions_stack_append : reduce_db.

  Lemma pair_reduction_stack_append :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳ (σ2 ◁ ψ).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros.

    - match goal with
      | [Ha : _ ⦂ _ ⦿ ?σ1 ⤳… ?σ,
              Hb : _ ∙ ?σ ⤳ ?σ2,
                   Hc : _ ⋄ _ ≜ ?M
         |- _ ⦂ _ ⦿ (?σ1 ◁ ?ψ) ⤳ (?σ2 ◁ ?ψ)] =>
        apply p_internal with (M:=M)(σ:=σ ◁ ψ)
      end;
        eauto with reduce_db.
      internal_external_stack_append.

    - match goal with
      | [Ha : ?M ∙ ?σ ⤳ ?σ' |- _] =>
        apply p_external with (M:=M)
      end;
        eauto with reduce_db;
        try solve [internal_external_stack_append].

  Qed.

  Hint Rewrite pair_reduction_stack_append : reduce_db.
  Hint Resolve pair_reduction_stack_append : reduce_db.

  Lemma pair_reductions_stack_append :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall ψ, M1 ⦂ M2 ⦿ (σ1 ◁ ψ) ⤳⋆ (σ2 ◁ ψ).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eauto with reduce_db.
  Qed.

  Hint Rewrite pair_reductions_stack_append : reduce_db.
  Hint Resolve pair_reductions_stack_append : reduce_db.

  Lemma constrained_pair_reduction_is_pair_reduction :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⌈⤳⌉ σ2 ->
                   M1 ⦂ M2 ⦿ σ1 ⤳ σ2.
  Proof.
    intros;
      unfold constrained_pair_reduction in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst.
    match goal with
    | [H : _ ⦂ _ ⦿ _ ⤳ _  |- context[_ ◁ ?ψ]] =>
      apply pair_reduction_stack_append with (ψ:=ψ) in H
    end;
      auto.
  Qed.

  Lemma constrained_pair_reductions_is_pair_reductions :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⌈⤳⋆⌉ σ2 ->
                   M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
  Proof.
    intros;
      unfold constrained_pair_reductions in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst.
    match goal with
    | [H : _ ⦂ _ ⦿ _ ⤳⋆ _  |- context[_ ◁ ?ψ]] =>
      apply pair_reductions_stack_append with (ψ:=ψ) in H
    end;
      auto.
  Qed.

  Hint Rewrite
       constrained_pair_reduction_is_pair_reduction
       constrained_pair_reductions_is_pair_reductions : reduce_db.
  Hint Resolve
       constrained_pair_reduction_is_pair_reduction
       constrained_pair_reductions_is_pair_reductions : reduce_db.

  Lemma prop_change_constrained_pair_reduction :
    forall M1 M2 σ1 σ2,
      M1 ⦂ M2 ⦿ σ1 ⌈⤳⋆⌉ σ2 ->
      forall (P : mdl -> mdl -> config -> Prop),
        P M1 M2 σ1 ->
        ~ P M1 M2 σ2 ->
        exists σ σ', M1 ⦂ M2 ⦿ σ ⤳ σ' /\
                P M1 M2 σ /\ ~ P M1 M2 σ' /\
                (σ = σ1 \/ M1 ⦂ M2 ⦿ σ1 ⌈⤳⋆⌉ σ) /\
                (σ' = σ2 \/ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2).
  Proof.
    intros.
    unfold constrained_pair_reductions in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst.
    match goal with
    | [H : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳⋆ ?σ2,
           P : mdl -> mdl -> config -> Prop,
               _ : P ?M1 ?M2 (_, _ :: ?ψ)
       |- _ ] =>
      let σ := fresh "σ" in
      destruct (prop_change_pair_reduction
                  M1 M2
                  σ1 σ2
                  H
                  (fun M1 M2 σ => P M1 M2 (σ ◁ ψ)))
        as [σ];
        auto;
        repeat destruct_exists_loo;
        andDestruct
    end.
    match goal with
    | [_ : ?σ = (_, _ :: nil) \/ _,
           _ : ?σ' = _ \/ _,
               _ : context[_ ◁ ?ψ] |- _] =>
      exists (σ ◁ ψ), (σ' ◁ ψ);
        repeat split;
        auto;
        try solve [apply pair_reduction_stack_append; auto]
    end;
      match goal with
      | [H : ?σ = _ \/ _ |- ?σ ◁ ?ψ = _ \/ _ ] =>
        destruct H;
          subst;
          auto;
          right
      end;
      try solve [apply pair_reductions_stack_append; auto].
    repeat eexists; eauto.
  Qed.

  Lemma method_return_implies_call :
    forall M1 M2 σ0 σ1, M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ1 ->
                   initial σ0 ->
                   is_rtrn σ1 ->
                   exists σ, M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ /\
                        M1 ⦂ M2 ⦿ σ ⌈⤳⋆⌉ σ1 /\
                         exists α1 α m args
                           χ ϕ ψ χ1 ϕ1 ψ1,
                           M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α) calls α1 ◌ m ⟨ args ⟩) /\
                           (σ = (χ, ϕ :: ψ)) ->
                           (σ1 = (χ1, ϕ1 :: ψ1)) ->
                           this ϕ = α.

(**
   This is  a useful property, but it only holds in a deterministic world
   i.e. if satisfaction of an assertion changes over time
   then there is some single step where the change occurs.
   i.e. we want one of the following to be satisfied:
   #<ol>#
   #<li>#
   (1) A ∧ will ⟨ ¬ A ⟩
       ⟶
        will ⟨ ¬ A ∧ prev ⟨ A ⟩ ⟩
   OR
   #</li>#
   #<li>#
   (2) A ∧ was ⟨ ¬ A ⟩
       ⟶
        was ⟨ A ∧ prev ⟨ ¬ A ⟩ ⟩
   #</li>#
   #<li>#
   (3) A ∧ will ⟨ ¬ A ⟩
       ⟶
        will ⟨ A ∧ next ⟨ ¬ A ⟩ ⟩
   OR
   #</li>#
   #<li>#
   (4) A ∧ was ⟨ ¬ A ⟩
       ⟶
        was ⟨ ¬ A ∧ next ⟨ A ⟩ ⟩
   OR
   #</li>#
   #</ol>#

   (3) and (4) don't hold because the change in satisfaction might
   result from a method call, and thus the reduction step is not constrained
   meaning next is not satisfied.

   (1) and (2) only work in a linear world. If reduction were non-linear, then
   different branches might take different routes to the change. For any
   particular branch, the property would hold, but not generally.

   Perhaps an alternative to getting to this property in a non-linear world might be
   to introduce a version of will/next that only constrains reduction once.
   i.e. in will ⟨ A ∧ next ⟨ ¬ A ⟩ ⟩, we constrain reduction twice, once with
   will, and a second time with next. If we only constrain reduction for will
   (i.e. the first temporal operator), but not for next. Thus, the future
   specified by next is still constrained, just not by the specific environment
   where the next lives.
 *)
  Lemma sat_change_will :
    forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will (¬ A) ->
                    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will (¬ A ∧ (a_prev A)).
  Proof.
    intros.
    match goal with
    | [H : _ ⦂ _ ◎ _ … _ ⊨ a_will _ |- _ ] =>
      inversion H;
        subst
    end.
  Abort.

  Close Scope list_scope.
  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End ChainmailProperties.
