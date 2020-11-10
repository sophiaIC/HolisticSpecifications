Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Import partial_maps.
Require Import chainmail.defs.
Require Import chainmail.L_def.
Require Import operational_semantics.
Require Import hoare.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.
Require Import Coq.Logic.FunctionalExtensionality.

Module OperationalSemanticsProperties(L : LanguageDef).

  Module L_Semantics := AbstractOperationalSemantics(L).
  Module L_Hoare := Hoare(L).
  Import L.
  Import L_Semantics.
  Import L_Hoare.

  Open Scope reduce_scope.

  Definition external_step (M1 M2 : mdl)(σ : config) :=
    forall M σ', M1 ⋄ M2 ≜ M ->
            M ∙ σ ⤳ σ' ->
            external_self M1 M2 σ'.

  Definition internal_step (M1 M2 : mdl)(σ : config) :=
    forall M σ', M1 ⋄ M2 ≜ M ->
            M ∙ σ ⤳ σ' ->
            internal_self M1 M2 σ'.

  Lemma internal_reductions_is_internal :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   internal_self M1 M2 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto.
  Qed.

  Lemma reduction_preserves_class :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall α o1 o2,
                 fst σ1 α = Some o1 ->
                 fst σ2 α = Some o2 ->
                 cname o1 = cname o2.
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      simpl in *;
      repeat simpl_crush;
      auto.

    - match goal with
      | [α1 : addr, α2 : addr |- _ ] =>
        destruct (eq_dec α1 α2);
          subst
      end;
        repeat map_rewrite;
        repeat simpl_crush;
        auto.

    - repeat map_rewrite;
        repeat simpl_crush;
        auto.
  Qed.

  Lemma object_persists_over_reduction :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall α o, fst σ1 α = Some o ->
                      exists o', fst σ2 α = Some o'.
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      simpl in *;
      repeat simpl_crush;
      try solve [eexists;
                 repeat map_rewrite;
                 repeat simpl_crush;
                 eauto].

    - match goal with
      | [α1 : addr, α2 : addr |- _ ] =>
        destruct (eq_dec α1 α2);
          subst
      end;
        eexists;
        repeat map_rewrite;
        repeat simpl_crush;
        eauto.
  Qed.

  Lemma reduction_preserves_internal :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall M1 M2 α, M1 ⋄ M2 ≜ M ->
                          is_internal M1 M2 σ1 α ->
                          is_internal M1 M2 σ2 α.
  Proof.
    intros.
    unfold is_internal in *;
      repeat destruct_exists_loo;
      andDestruct.
    match goal with
    | [Ha : ?M ∙ ?σ1 ⤳ ?σ2,
            Hb : fst ?σ1 ?α = Some ?o,
                 Hc : ?M1 (cname ?o) = Some ?defn |- _ ] =>
      let o' := fresh "o" in
      destruct (object_persists_over_reduction M σ1 σ2 Ha α o Hb)
        as [o'];
        exists o', defn
    end.
    split;
      auto.
    erewrite <- reduction_preserves_class;
      eauto.
  Qed.

  Lemma internal_reductions_preserves_internal :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   forall α, is_internal M1 M2 σ1 α ->
                        is_internal M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eapply reduction_preserves_internal; eauto.
  Qed.

  Lemma pair_reduction_preserves_internal :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   forall α, is_internal M1 M2 σ1 α ->
                        is_internal M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eapply reduction_preserves_internal; eauto.
    eapply internal_reductions_preserves_internal; eauto.
  Qed.

  Lemma pair_reductions_preserves_internal :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall α, is_internal M1 M2 σ1 α ->
                        is_internal M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros.

    - eapply pair_reduction_preserves_internal; eauto.

    - match goal with
      | [H : forall _, _ |- _ ] =>
        apply H
      end.
      eapply pair_reduction_preserves_internal; eauto.
  Qed.

  Lemma reduction_preserves_external :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall M1 M2 α, M1 ⋄ M2 ≜ M ->
                          is_external M1 M2 σ1 α ->
                          is_external M1 M2 σ2 α.
  Proof.
    intros.
    unfold is_external in *;
      repeat destruct_exists_loo;
      andDestruct.
    match goal with
    | [Ha : ?M ∙ ?σ1 ⤳ ?σ2,
            Hb : fst ?σ1 ?α = Some ?o,
                 Hc : (cname ?o) ∉ ?M1 |- _ ] =>
      let o' := fresh "o" in
      destruct (object_persists_over_reduction M σ1 σ2 Ha α o Hb)
        as [o'];
        exists o'
    end.
    split;
      auto.
    erewrite <- reduction_preserves_class;
      eauto.
  Qed.

  Lemma internal_reductions_preserves_external :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   forall α, is_external M1 M2 σ1 α ->
                        is_external M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eapply reduction_preserves_external; eauto.
  Qed.

  Lemma pair_reduction_preserves_external :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   forall α, is_external M1 M2 σ1 α ->
                        is_external M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eapply reduction_preserves_external; eauto.
    eapply internal_reductions_preserves_external; eauto.
  Qed.

  Lemma pair_reductions_preserves_external :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall α, is_external M1 M2 σ1 α ->
                        is_external M1 M2 σ2 α.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros.

    - eapply pair_reduction_preserves_external; eauto.

    - match goal with
      | [H : forall _, _ |- _ ] =>
        apply H
      end.
      eapply pair_reduction_preserves_external; eauto.
  Qed.

  Lemma internal_is_not_external :
    forall M1 M2 σ α, is_internal M1 M2 σ α ->
                 ~ is_external M1 M2 σ α.
  Proof.
    intros;
      intro Hcontra;
      unfold is_internal, is_external in *;
      repeat destruct_exists_loo;
      andDestruct;
      repeat simpl_crush.
  Qed.

  Lemma external_is_not_internal :
    forall M1 M2 σ α, is_external M1 M2 σ α ->
                 ~ is_internal M1 M2 σ α.
  Proof.
    intros;
      intro Hcontra;
      unfold is_internal, is_external in *;
      repeat destruct_exists_loo;
      andDestruct;
      repeat simpl_crush.
  Qed.

  Lemma internal_self_is_not_external_self :
    forall M1 M2 σ, internal_self M1 M2 σ ->
               ~ external_self M1 M2 σ.
  Proof.
    intros;
      intro Hcontra;
      unfold internal_self, external_self in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst;
      repeat simpl_crush.
    match goal with
    | [Ha : is_external ?M1 ?M2 ?σ ?α,
            Hb : is_internal ?M1 ?M2 ?σ ?α |- _ ] =>
      contradiction (internal_is_not_external M1 M2 σ α)
    end.
  Qed.

  Lemma external_self_is_not_internal_self :
    forall M1 M2 σ, external_self M1 M2 σ ->
               ~ internal_self M1 M2 σ.
  Proof.
    intros;
      intro Hcontra;
      unfold internal_self, external_self in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst;
      repeat simpl_crush.
    match goal with
    | [Ha : is_external ?M1 ?M2 ?σ ?α,
            Hb : is_internal ?M1 ?M2 ?σ ?α |- _ ] =>
      contradiction (internal_is_not_external M1 M2 σ α)
    end.
  Qed.

  Lemma module_boundary_internal_call_or_rtrn :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall M1 M2, M1 ⋄ M2 ≜ M ->
                        external_self M1 M2 σ1 ->
                        internal_self M1 M2 σ2 ->
                        is_call_to (is_internal M1 M2) σ1 \/
                        is_return_to (internal_self M1 M2) σ1.
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;

      try solve[unfold external_self, internal_self, is_external, is_internal in *;
                repeat destruct_exists_loo;
                andDestruct;
                repeat simpl_crush;
                repeat destruct_exists_loo;
                simpl in *;
                andDestruct;
                repeat simpl_crush].

    - left;
        unfold is_call_to, internal_self in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush.
      eexists;
        split;
        eauto.
      repeat eexists.

    - right;
        unfold is_return_to, is_rtrn, waiting_frame_is;
        split.
      + right;
          repeat eexists.
      + unfold internal_self, is_internal in *;
          repeat destruct_exists_loo;
          andDestruct;
          repeat simpl_crush;
          repeat destruct_exists_loo;
          andDestruct;
          repeat simpl_crush.
        repeat eexists;
          simpl;
          eauto.

    - right;
        unfold is_return_to, is_rtrn, waiting_frame_is;
        split.
      + left;
          repeat eexists.
      + unfold internal_self, is_internal in *;
          repeat destruct_exists_loo;
          andDestruct;
          repeat simpl_crush;
          repeat destruct_exists_loo;
          andDestruct;
          repeat simpl_crush.
        repeat eexists;
          simpl;
          eauto.

    - unfold external_self, internal_self, is_external, is_internal in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush;
        repeat destruct_exists_loo;
        simpl in *;
        andDestruct;
        repeat simpl_crush.

      destruct (eq_dec self α);
        subst;
        repeat map_rewrite;
        repeat simpl_crush.

    - unfold external_self, internal_self, is_external, is_internal in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush;
        repeat destruct_exists_loo;
        simpl in *;
        andDestruct;
        repeat simpl_crush.

      destruct (eq_dec self α);
        subst;
        repeat map_rewrite;
        repeat simpl_crush.

  Qed.

  Lemma call_or_return_to_internal_is_internal_step :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall M1 M2, M1 ⋄ M2 ≜ M ->
                        is_call_to (is_internal M1 M2) σ1 \/
                        is_return_to (internal_self M1 M2) σ1 ->
                        internal_step M1 M2 σ1.
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;

      try solve [unfold is_call_to, is_return_to, is_call, is_rtrn in *;
                 disj_split;
                 andDestruct;
                 repeat destruct_exists_loo;
                 andDestruct;
                 try disj_split;
                 repeat destruct_exists_loo;
                 andDestruct;
                 match goal with
                 | [H : contn_is _ _ |- _] =>
                   inversion H
                 end].

    - unfold internal_step;
        intros;
        link_unique_auto;
        match goal with
        | [H : _ ∙ _ ⤳ _ |- _] =>
          inversion H;
            subst
        end;
        repeat simpl_crush;
        repeat cleanup.
      disj_split;
        try solve [unfold is_return_to, is_rtrn in *;
                   andDestruct;
                   repeat destruct_exists_loo;
                   andDestruct;
                   try disj_split;
                   repeat destruct_exists_loo;
                   andDestruct;
                   match goal with
                   | [H : contn_is _ _ |- _] =>
                     inversion H
                   end].
      unfold is_call_to in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat destruct_exists_loo;
        repeat simpl_crush.
      unfold internal_self.
        eexists; eexists; eexists;
          eauto.

    - unfold internal_step;
        intros;
        link_unique_auto;
        match goal with
        | [H : _ ∙ _ ⤳ _ |- _] =>
          inversion H;
            subst
        end;
        repeat simpl_crush;
        repeat cleanup.
      disj_split;
        try solve [unfold is_call_to, is_call in *;
                   andDestruct;
                   repeat destruct_exists_loo;
                   andDestruct;
                   try disj_split;
                   repeat destruct_exists_loo;
                   andDestruct;
                   match goal with
                   | [H : contn_is _ _ |- _] =>
                     inversion H
                   end].
      unfold is_return_to, waiting_frame_is, is_rtrn in *;
        simpl in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush.
      unfold internal_self.
      eexists; eexists; eexists;
        split;
        eauto.
      unfold internal_self in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush;
        simpl in *.
      auto.

    - unfold internal_step;
        intros;
        link_unique_auto;
        match goal with
        | [H : _ ∙ _ ⤳ _ |- _] =>
          inversion H;
            subst
        end;
        repeat simpl_crush;
        repeat cleanup.
      disj_split;
        try solve [unfold is_call_to, is_call in *;
                   andDestruct;
                   repeat destruct_exists_loo;
                   andDestruct;
                   try disj_split;
                   repeat destruct_exists_loo;
                   andDestruct;
                   match goal with
                   | [H : contn_is _ _ |- _] =>
                     inversion H
                   end].
      unfold is_return_to, waiting_frame_is, is_rtrn in *;
        simpl in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush.
      unfold internal_self.
      eexists; eexists; eexists;
        split;
        eauto.
      unfold internal_self in *;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush;
        simpl in *.
      auto.
  Qed.

  Lemma internal_reductions_is_internal_step :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   internal_step M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto.

    eapply call_or_return_to_internal_is_internal_step;
      eauto.
    eapply module_boundary_internal_call_or_rtrn;
      eauto.
  Qed.

  Lemma external_reduction_implies_external_step :
    forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
               forall M1 M2, M1 ⋄ M2 ≜ M ->
                        external_self M1 M2 σ1 ->
                        external_self M1 M2 σ2 ->
                        external_step M1 M2 σ1.
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      unfold external_step;
      intros;
      link_unique_auto;
      match goal with
      | [H : _ ∙ _ ⤳ _ |- _] =>
        inversion H;
          subst;
          clear H;
          auto
      end;
      repeat simpl_crush;
      repeat cleanup;
      auto.
  Qed.

  Lemma pair_reduction_external_or_internal_step :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   external_step M1 M2 σ1 \/
                   internal_step M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred.

    - right;
        eapply internal_reductions_is_internal_step;
        eauto.

    - left; eapply external_reduction_implies_external_step;
        eauto.
  Qed.

  Lemma internal_reductions_is_from_external_config :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   external_self M1 M2 σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto.
  Qed.

  Lemma pair_reduction_external_configs :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   external_self M1 M2 σ1 /\ external_self M1 M2 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred.
    - split;
        auto;
        eapply internal_reductions_is_from_external_config;
        eauto.

      - split; auto.

  Qed.

  Reserved Notation "M '∙' σ1 '⤳⋆' σ2"(at level 40).

  Inductive reductions_r : mdl -> config -> config -> Prop :=
  | reduce_single : forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                               M ∙ σ1 ⤳⋆ σ2

  | reduce_trans : forall M σ1 σ2 σ3, M ∙ σ1 ⤳⋆ σ2 ->
                                 M ∙ σ2 ⤳ σ3 ->
                                 M ∙ σ1 ⤳⋆ σ3

  where "M '∙' σ1 '⤳⋆' σ2" := (reductions_r M σ1 σ2).

  Hint Constructors reductions_r : L_db.

  (*)Inductive substmt_block : stmt -> block -> Prop :=
  | sub_rtrn : forall v, substmt_block (rtrn v) (b_rtrn v)
  | sub_stmts1 : forall s b, substmt_block s (b_stmt s b)
  | sub_stmts2 : forall s s' b, substmt_block s b ->
                           substmt_block s (b_stmt s' b).

  Inductive substmt : stmt -> continuation -> Prop :=
  | sub_hole : forall s x b, substmt_block s b ->
                        substmt s (x ≔♢ ;; b)
  | sub_block : forall s b, substmt_block s b ->
                       substmt s (c_block b).

  Hint Constructors substmt substmt_block : L_db.*)

  Inductive sub_block : block -> block -> Prop :=
  | sub_refl : forall b, sub_block b b
  | sub_stmt : forall b1 s b2, sub_block b1 b2 ->
                          sub_block b1 (b_stmt s b2)
  | sub_trans : forall b1 b2 b3, sub_block b1 b2 ->
                            sub_block b2 b3 ->
                            sub_block b1 b3.

  Hint Constructors sub_block : L_db.

  Lemma app_cons_1 :
    forall {A : Type} {l1 l2 l3} {a1 a2 : A},
      l1 ++ a1 :: l2 = a2 :: l3  ->
      (l1 = nil) \/ (exists l4, l1 = a2 :: l4).
  Proof.
    intros A l1;
      induction l1;
      intros.

    - auto.

    - simpl in *.
      repeat simpl_crush.
      eauto.
  Qed.

  Ltac unfold_existentials :=
    repeat destruct_exists_loo;
    andDestruct;
    subst;
    simpl in *;
    repeat simpl_crush.

  Lemma frame_implies_call :
    forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
               initial σ1 ->
               forall χ2 ϕa ϕb ψa ψb,
                 σ2 = (χ2, ψa ++ ϕa :: ϕb :: ψb) ->
                 exists χ ϕ ψ, ((χ, ϕ :: ψ) = σ1 \/ M ∙ σ1 ⤳⋆ (χ, ϕ :: ψ)) /\
                          M ∙ (χ, ϕ :: ψ) ⤳⋆ σ2 /\
                          exists m, (exists x args b2, contn ϕb = (x ≔♢ ;; b2) /\
                                             this ϕ = this ϕb /\
                                             local ϕ = local ϕb /\
                                             contn ϕ = c_ (x ≔m (this ϕa) ▸ m ⟨ args ⟩) ;; b2) /\
                               (exists b o defn body, ((contn ϕa = (c_ b) /\ ψa = nil) \/
                                                  (exists y, contn ϕa = (y ≔♢ ;; b) /\ ψa <> nil)) /\
                                                 χ (this ϕa) = Some o /\
                                                 M (cname o) = Some defn /\
                                                 c_meths defn m = Some body /\
                                                 sub_block b body).
  Proof.
    intros M σ1 σ2 Hred;
      induction Hred;
      intros;
      subst.

    - unfold initial in *;
        repeat unfold_existentials.

      destruct ψa; simpl in *.

      + match goal with
        | [H : _ ∙ _ ⤳ _ |- _ ] =>
          inversion H;
            subst
        end.
        eexists; eexists; eexists;
          split;
          eauto.
        split;
          eauto with L_db.
        simpl in *.
        repeat eexists;
          eauto with L_db.

      + match goal with
        | [H : _ ∙ _ ⤳ _ |- _ ] =>
          inversion H;
            subst
        end;
          repeat simpl_crush.

    -  auto_specialize.
       match goal with
       | [H : _ ∙ _ ⤳ _ |- _ ] =>
         inversion H;
           subst
       end;

         try solve [match goal with
                    | [H : _ :: _ = _ ++ _ :: _ :: _ |- _] =>
                      symmetry in H;
                      destruct (app_cons_1 H);
                      subst;
                      simpl in *
                    end;
                    [repeat simpl_crush;
                     match goal with
                     | [Ha : forall χ ϕa ϕb ψa ψb, _,
                          Hb : _ ∙ (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ) ⤳ _
                          |- _] =>
                       specialize (Ha χ ϕ1 ϕ2 nil ψ)
                     end;
                     simpl in *;
                     auto_specialize;
                     repeat unfold_existentials;
                     repeat simpl_crush;
                     match goal with
                     | [H : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
                       exists χ, ϕ, ψ;
                       repeat split;
                       auto
                     end;
                     [eapply reduce_trans;
                      eauto with L_db
                     |repeat eexists;
                      eauto;
                      disj_split;
                      andDestruct;
                      repeat destruct_exists_loo;
                      andDestruct;
                      repeat simpl_crush;
                      eauto with L_db]

                    | repeat destruct_exists_loo;
                      subst;
                      simpl in *;
                      repeat simpl_crush;
                      match goal with
                      | [Ha : forall χ ϕa ϕb ψa ψb, _,
                           Hb : _ ∙ (?χ, ?ϕ :: ?ψ1 ++ ?ϕ1 :: ?ϕ2 :: ?ψ2) ⤳ _
                           |- _] =>
                        specialize (Ha χ ϕ1 ϕ2 (ϕ :: ψ1) ψ2)
                      end;
                      simpl in *;
                      auto_specialize;
                      repeat unfold_existentials;
                      match goal with
                      | [H : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
                        exists χ, ϕ, ψ;
                        repeat split;
                        auto
                      end;
                      [eapply reduce_trans;
                       eauto with L_db
                      |repeat eexists;
                       eauto;
                       disj_split;
                       andDestruct;
                       repeat destruct_exists_loo;
                       andDestruct;
                       repeat simpl_crush;
                       eauto with L_db];
                      right;
                      repeat eexists;
                      eauto;
                      crush]].

       + match goal with
         | [H : _ :: _ = _ ++ _ :: _ :: _ |- _] =>
           symmetry in H;
             destruct (app_cons_1 H);
             subst;
             simpl in *
         end;
           repeat simpl_crush.

         * eexists;
             eexists;
             eexists;
             repeat split;
             eauto with L_db;
             simpl in *.
           repeat eexists;
             eauto with L_db.

         * repeat unfold_existentials.
           match goal with
           | [H : _ ++ _ ::  _ :: _ = _ :: _ |- _] =>
             destruct (app_cons_1 H);
               subst;
               simpl in *
           end;
             repeat simpl_crush.

           **  match goal with
               | [H : forall _ _ _ _ _, (?χ, ?ϕa :: ?ϕb :: ?ψb) = _ -> _ |- _ ] =>
                 specialize (H χ ϕa ϕb nil ψb)
               end;
                 simpl in *.
               simpl in *.
               match goal with
               | [H : ?x = ?y -> _ |- _] =>
                 specialize (H eq_refl)
               end.
               repeat unfold_existentials.

               match goal with
               | [H : _ ∙ (?χ, ?ϕ :: ?ψ) ⤳⋆ _ |- exists _ _ _, _ ] =>
                 exists χ, ϕ, ψ
               end;
                 repeat split;
                 eauto with L_db;
                 simpl in *.

               exists m0;
                 split.
               *** repeat eexists; eauto.
               *** disj_split;
                     repeat unfold_existentials.
                   match goal with
                   | [|- context[_ ≔♢ ;; ?b = _ ]] =>
                     exists b
                   end.
                   match goal with
                   | [_ : ?χ ?α = Some ?o
                      |- context[?χ ?α = Some _] ] =>
                     exists o
                   end.
                   match goal with
                   | [_ : ?M (cname ?o) = Some ?defn,
                          _ : c_meths ?defn _ = Some ?b
                      |- context[?M (cname ?o) = Some _] ] =>
                     exists defn, b
                   end.
                   repeat split;
                     auto.
                   right.
                   eexists; split; eauto with L_db.
                   crush.
                   eauto with L_db.

           ** repeat unfold_existentials.
              match goal with
              | [H : forall _ _ _ _ _, (?χ, ?ϕ1 :: ?ψ1 ++ ?ϕ2 :: ?ϕ3 :: ?ψ2) = _ -> _
                                  |- _] =>
                specialize (H χ ϕ2 ϕ3 (ϕ1 :: ψ1) ψ2)
              end.
              match goal with
              | [H : ?x = ?y -> _ |- _] =>
                specialize (H eq_refl)
              end.
              repeat unfold_existentials.

              match goal with
              | [_ : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
                exists χ, ϕ, ψ
              end;
                repeat split;
                eauto with L_db.

              disj_split;
                repeat unfold_existentials.

              repeat eexists;
                eauto with L_db.
              right; eauto with L_db.
              eexists;
                split;
                eauto with L_db.
              crush.

       + match goal with
         | [H : _ :: _ = _ ++ _ :: _ :: _ |- _] =>
           symmetry in H;
             destruct (app_cons_1 H);
             subst;
             simpl in *
         end;
           repeat unfold_existentials.

         * match goal with
           | [H : forall _ _ _ _ _, (?χ, ?ϕ1 :: ?ϕ2 :: ?ϕ3 :: ?ψ) = _ -> _ |- _ ] =>
             specialize (H χ ϕ2 ϕ3 (ϕ1 :: nil) ψ)
           end.
           simpl in *.
           match goal with
           | [H : ?x = ?y -> _ |- _] =>
             specialize (H eq_refl)
           end.
           repeat unfold_existentials.
           match goal with
           | [_ : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
             exists χ, ϕ, ψ
           end;
             repeat split;
             eauto with L_db.
           match goal with
           | [m : mth |- _ ] =>
             exists m
           end.
           split;
             repeat eexists;
             eauto with L_db.
           disj_split;
             repeat unfold_existentials;
             auto.

         * match goal with
           | [H : forall _ _ _ _ _, (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ1 ++ ?ϕa :: ?ϕb :: ?ψ2) = _ -> _ |- _ ] =>
             specialize (H χ ϕa ϕb (ϕ1 :: ϕ2 :: ψ1) ψ2)
           end.
           simpl in *.
           match goal with
           | [H : ?x = ?y -> _ |- _] =>
             specialize (H eq_refl)
           end.
           repeat unfold_existentials.
           match goal with
           | [_ : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
             exists χ, ϕ, ψ
           end;
             repeat split;
             eauto with L_db.
           match goal with
           | [m : mth |- _ ] =>
             exists m
           end.
           split;
             try solve [repeat eexists;
                        eauto with L_db].
           disj_split;
             repeat unfold_existentials.
           eexists;
             eexists;
             eexists;
             eexists;
             split;
             eauto with L_db.
           right;
             eexists;
             split;
             eauto;
             crush.

       + match goal with
         | [H : _ :: _ = _ ++ _ :: _ :: _ |- _] =>
           symmetry in H;
             destruct (app_cons_1 H);
             subst;
             simpl in *
         end;
           repeat unfold_existentials.

         * match goal with
           | [H : forall _ _ _ _ _, (?χ, ?ϕ1 :: ?ϕ2 :: ?ϕ3 :: ?ψ) = _ -> _ |- _ ] =>
             specialize (H χ ϕ2 ϕ3 (ϕ1 :: nil) ψ)
           end.
           simpl in *.
           match goal with
           | [H : ?x = ?y -> _ |- _] =>
             specialize (H eq_refl)
           end.
           repeat unfold_existentials.
           match goal with
           | [_ : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
             exists χ, ϕ, ψ
           end;
             repeat split;
             eauto with L_db.
           match goal with
           | [m : mth |- _ ] =>
             exists m
           end.
           split;
             repeat eexists;
             eauto with L_db.
           disj_split;
             repeat unfold_existentials;
             auto.

         * match goal with
           | [H : forall _ _ _ _ _, (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ1 ++ ?ϕa :: ?ϕb :: ?ψ2) = _ -> _ |- _ ] =>
             specialize (H χ ϕa ϕb (ϕ1 :: ϕ2 :: ψ1) ψ2)
           end.
           simpl in *.
           match goal with
           | [H : ?x = ?y -> _ |- _] =>
             specialize (H eq_refl)
           end.
           repeat unfold_existentials.
           match goal with
           | [_ : (?χ, ?ϕ :: ?ψ) = _ \/ _ |- _ ] =>
             exists χ, ϕ, ψ
           end;
             repeat split;
             eauto with L_db.
           match goal with
           | [m : mth |- _ ] =>
             exists m
           end.
           split;
             try solve [repeat eexists;
                        eauto with L_db].
           disj_split;
             repeat unfold_existentials.
           eexists;
             eexists;
             eexists;
             eexists;
             split;
             eauto with L_db.
           right;
             eexists;
             split;
             eauto;
             crush.
  Qed.

  Definition internal_frame (M1 M2 : mdl)(σ : config)(ϕ : frame) :=
    is_internal M1 M2 σ (this ϕ).

  Definition external_frame (M1 M2 : mdl)(σ : config)(ϕ : frame) :=
    is_external M1 M2 σ (this ϕ).

  Definition forall_in {A : Type} (l : list A)(P : A -> Prop) :=
    forall a, In a l -> P a.

  Definition rtrns (σ : config)(v : value) :=
    contn_is (c_rtrn v) σ \/
    exists b, contn_is (c_ (rtrn v ;; b)) σ.

  Lemma internal_reductions_is_call_or_rtrn :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   is_call σ1 \/ is_rtrn σ1.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      auto.

    - match goal with
      | [H : _ ∙ _ ⤳ _ |- _ ] =>
        inversion H;
          subst;
          clear H
      end;
        try solve [unfold is_call, is_rtrn; eauto with L_db];

        try solve [match goal with
                   | [H : internal_self _ _ _ |- _ ] =>
                     apply internal_self_is_not_external_self in H;
                     contradiction H
                   end;
                   unfold external_self, is_external in *;
                   repeat unfold_existentials;
                   repeat eexists;
                   simpl in *;
                   repeat simpl_crush;
                   repeat map_rewrite;
                   eauto with L_db].

      + left; unfold is_call;
          repeat eexists;
          eauto with L_db.

      + match goal with
        | [H : internal_self _ _ _ |- _ ] =>
          apply internal_self_is_not_external_self in H;
            contradiction H
        end;
          unfold external_self, is_external in *;
          repeat unfold_existentials;
          simpl in *.
        match goal with
        | [|- exists _ _ _, (?χ, ?ϕ :: ?ψ) = _ /\ _] =>
          exists χ, ϕ, ψ;
            split;
            auto;
            simpl in *
        end.
        match goal with
        | [|- exists _, ([?α1 ↦ ?o ] ?χ) ?α2 = _ /\ _ ] =>
          destruct (eq_dec α1 α2);
            subst;
            [exists o;
               simpl;
               split;
               repeat simpl_crush;
               auto;
               repeat map_rewrite
              |eexists;
               split;
               eauto;
               repeat map_rewrite]
        end.

  Qed.

  Lemma linking_commutative :
    forall M1 M2 Ma, M1 ⋄ M2 ≜ Ma ->
                forall Mb, M2 ⋄ M1 ≜ Mb ->
                      Ma = Mb.
  Proof.
    intros.
    repeat match goal with
           | [Hlink : _ ⋄ _ ≜ _ |- _ ] =>
             inversion Hlink;
               subst;
               clear Hlink
           end.

    apply functional_extensionality;
      intro x.
    destruct (eq_dec x Object);
      subst.

    - unfold extend.
      repeat match goal with
             | [H : ?x = _ |- context[?x]] =>
               rewrite H
             end;
        auto.

    - unfold extend.
      match goal with
      | [|- context[?M1 ?x]] =>
        destruct (partial_map_dec x M1)
      end;
        unfold_existentials;
        repeat simpl_crush;
        repeat match goal with
             | [H : ?x = _ |- context[?x]] =>
               rewrite H
             end;
        auto.

      + match goal with
        | [Ha : forall _ _, _ -> ?M1 _ = Some _ -> _ ∉ ?M2,
             Hb : ?M1 ?x = Some ?defn |- context[?M2 ?x]] =>
          specialize (Ha x defn);
            repeat auto_specialize;
            rewrite Ha
        end.
        auto.

      + match goal with
        | [|- context[?M ?x]] =>
          destruct (M x);
            auto
        end.

  Qed.

  Lemma cons_forall_in :
    forall {A : Type}(l : list A)(a : A) P,
      forall_in (a :: l) P ->
      P a /\ forall_in l P.
  Proof.
    intros A l;
      induction l;
      intros;
      unfold forall_in in *;
      intros;
      crush.
  Qed.

  Lemma forall_in_cons :
    forall {A : Type}(l : list A)(a : A) (P : A -> Prop),
      P a ->
      forall_in l P ->
      forall_in (a :: l) P.
  Proof.
    intros A l;
      induction l;
      intros;
      unfold forall_in in *;
      intros;
      crush.
  Qed.

  Ltac forall_in_auto :=
    match goal with
    | [|- forall_in (_ :: _) _] =>
      apply forall_in_cons
    | [H : forall_in (_ :: _) _ |- _] =>
      apply cons_forall_in in H;
      andDestruct
    end.

  Lemma external_self_is_external :
    forall M1 M2 χ self lcl c ψ, external_self M1 M2 (χ, frm self lcl c :: ψ) ->
                            is_external M1 M2 (χ, frm self lcl c :: ψ) self.
  Proof.
    intros.
    unfold external_self in *;
      unfold_existentials;
      auto.
  Qed.

  Lemma internal_self_is_internal :
    forall M1 M2 χ self lcl c ψ, internal_self M1 M2 (χ, frm self lcl c :: ψ) ->
                            is_internal M1 M2 (χ, frm self lcl c :: ψ) self.
  Proof.
    intros.
    unfold internal_self in *;
      unfold_existentials;
      auto.
  Qed.

  Ltac external_internal_auto :=
    match goal with
    | [H : ?M1 ⦂ ?M2 ⦿ ?σa ⤳… ?σb |- _ ] =>
      notHyp (external_self M1 M2 σa);
      let Ha := fresh in
      assert (H' : external_self M1 M2 σa);
      [apply internal_reductions_is_from_external_config with (σ2:=σb); auto|]
    | [H : ?M1 ⦂ ?M2 ⦿ ?σa ⤳… ?σb |- _ ] =>
      notHyp (internal_self M1 M2 σa);
      let Ha := fresh in
      assert (H' : internal_self M1 M2 σb);
      [apply internal_reductions_is_internal with (σ1:=σa); auto|]

    | [H : internal_self ?M1 ?M2 (?χ, frm ?self ?lcl ?c :: ?ψ) |- _ ] =>
      notHyp (is_internal M1 M2 (χ, frm self lcl c :: ψ) self);
      let H' := fresh in
      assert (H' : is_internal M1 M2 (χ, frm self lcl c :: ψ) self);
      [eapply internal_self_is_internal; eauto|]
    | [H : external_self ?M1 ?M2 (?χ, frm ?self ?lcl ?c :: ?ψ) |- _ ] =>
      notHyp (is_external M1 M2 (χ, frm self lcl c :: ψ) self);
      let H' := fresh in
      assert (H' : is_external M1 M2 (χ, frm self lcl c :: ψ) self);
      [eapply external_self_is_external; eauto|]

    | [Hred : ?M ∙ ?σ1 ⤳ ?σ2,
              Hlink : ?M1 ⋄ ?M2 ≜ ?M,
                      Ha : is_internal ?M1 ?M2 ?σ1 ?α |- _ ] =>
      notHyp (is_internal M1 M2 σ2 α);
      let H' := fresh in
      assert (H' : is_internal M1 M2 σ2 α);
      [eapply reduction_preserves_internal; eauto|]
    | [Hred : ?M ∙ ?σ1 ⤳ ?σ2,
              Hlink : ?M1 ⋄ ?M2 ≜ ?M,
                      Ha : is_external ?M1 ?M2 ?σ1 ?α |- _ ] =>
      notHyp (is_external M1 M2 σ2 α);
      let H' := fresh in
      assert (H' : is_external M1 M2 σ2 α);
      [eapply reduction_preserves_external; eauto|]

    | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳… ?σ2,
              Ha : is_internal ?M1 ?M2 ?σ1 ?α |- _ ] =>
      notHyp (is_internal M1 M2 σ2 α);
      let H' := fresh in
      assert (H' : is_internal M1 M2 σ2 α);
      [eapply internal_reductions_preserves_internal; eauto|]
    | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳… ?σ2,
              Ha : is_external ?M1 ?M2 ?σ1 ?α |- _ ] =>
      notHyp (is_external M1 M2 σ2 α);
      let H' := fresh in
      assert (H' : is_external M1 M2 σ2 α);
      [eapply internal_reductions_preserves_external; eauto|]

    | [Ha : is_internal ?M1 ?M2 ?σ ?α,
            Hb : is_external ?M1 ?M2 ?σ ?α |- _ ] =>
      notHyp (~ is_external M1 M2 σ α);
      apply internal_is_not_external in Ha;
      contradiction Ha; auto

    end.

  Lemma internal_reduction_is_call_or_rtrn :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   (exists χ1 self lcl x α m args b ψ1
                      χ2 ψ2, σ1 = (χ1, frm self lcl (c_ (x ≔m α ▸ m ⟨ args ⟩) ;; b) :: ψ1) /\
                             σ2 = (χ2, ψ2 ++ frm self lcl (x ≔♢ ;; b) :: ψ1) /\
                             length ψ2 > 0 /\
                             forall_in ψ2 (internal_frame M1 M2 σ2)) \/
                   (exists χ1 v ϕ ψ ψ1
                      χ2 ψ2, σ1 = (χ1, ϕ :: ψ1 ++ ψ) /\
                             σ2 = (χ2, ψ2 ++ ψ) /\
                             rtrns σ1 v /\
                             length ψ1 > 0 /\
                             length ψ2 > 0 /\
                             forall_in ψ1 (internal_frame M1 M2 σ1) /\
                             forall_in ψ2 (internal_frame M1 M2 σ2)).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred.

    - match goal with
      | [_ : _ ∙ ?σ1 ⤳ ?σ2 |- _ ] =>
        let χ1 := fresh "χ" in
        let ψ1 := fresh "ψ" in
        destruct σ1 as [χ1 ψ1];
        let χ2 := fresh "χ" in
        let ψ2 := fresh "ψ" in
        destruct σ2 as [χ2 ψ2]
      end.
      match goal with
      | [H : _ ∙ (?χ1, ?ψ1) ⤳ (?χ2, ?ψ2) |- _ ] =>
        assert (exists ϕ ψ, ψ1 = ϕ :: ψ);
          [destruct ψ1 ;
           [inversion H
           |eauto]
          |repeat destruct_exists_loo;
           subst];
        assert (exists ϕ ψ, ψ2 = ϕ :: ψ);
          [destruct ψ2 ;
           [inversion H
           |eauto]
          |repeat destruct_exists_loo;
           subst]
      end.
      match goal with
      | [Hlink : ?M1 ⋄ ?M2 ≜ ?M,
                 Hred : ?M ∙ ?σ1 ⤳ ?σ2 |- _] =>
        destruct (internal_reductions_is_call_or_rtrn M1 M2 σ1 σ2);
          [eauto with reduce_db|unfold is_call in *|unfold is_rtrn in *];
          repeat unfold_existentials
      end.

      + left.
        match goal with
        | [H : _ ∙ _ ⤳ _ |- _ ] =>
          inversion H;
            subst
        end.
        match goal with
        | [|- exists _ _ _ _ _ _ _ _ _ _ _,
              (?χ, {| this := ?self1; local := ?lcl1; contn := (c_ ?b) |} :: ?ψ1) = _
              /\ (_, ?ϕ :: _) = _ /\ _] =>
          exists χ, self1, lcl1;
            eexists;
            eexists;
            eexists;
            eexists;
            eexists;
            exists ψ1, χ, (ϕ :: nil)
        end;
          repeat split;
          auto;
          unfold forall_in;
          intros.
        match goal with
        | [Hin : In _ _ |- _ ] =>
          inversion Hin;
            subst;
            [|crush]
        end.
        unfold internal_frame;
          simpl.
        unfold internal_self in *;
          repeat unfold_existentials.
        auto.

      + right.
        disj_split;
          repeat unfold_existentials;
          match goal with
          | [H : _ ∙ _ ⤳ _ |- _] =>
            inversion H;
              subst
          end;

          try solve [match goal with
                     | [|- exists _ _ _ _ _ _ _, (?χ1, ?ϕ1 :: ?ϕ2 :: ?ψ) = _ /\ (_, ?ϕ3 :: _) = _ /\ _ ] =>
                       match goal with
                       | [|- context[rtrn ?v]] =>
                         exists χ1, v, ϕ1, ψ, (ϕ2 :: nil), χ1, (ϕ3 :: nil)
                       | [|- context[c_rtrn ?v]] =>
                         exists χ1, v, ϕ1, ψ, (ϕ2 :: nil), χ1, (ϕ3 :: nil)
                       end
                     end;
                     simpl;
                     repeat split;
                     auto;
                     try solve [unfold forall_in;
                                intros;
                                repeat match goal with
                                       | [Hin : In _ _ |- _ ] =>
                                         inversion Hin;
                                         subst;
                                         clear Hin
                                       end;
                                unfold internal_frame, internal_self, is_internal in *;
                                simpl in *;
                                repeat unfold_existentials;
                                repeat eexists; eauto];
                     unfold rtrns;
                     try solve [right;
                                repeat eexists];
                     try solve [left;
                                repeat eexists]].

    - disj_split;
        repeat unfold_existentials.

      + left.
        match goal with
        | [Hred : _ ∙ (_, ?ψ ++ _) ⤳ _ |-_ ] =>
          let ϕ' := fresh "ϕ" in
          let ψ' := fresh "ψ" in
          destruct ψ as [|ϕ' ψ'];
            simpl in *;
            [crush|]
        end.

        match goal with
        | [|- exists _ _ _ _ _ _ _ _ _ _ _,
              (?χ, {| this := ?self; local := ?lcl; contn := (c_ (?x ≔m ?α ▸ ?m ⟨ ?args ⟩) ;; ?b) |} :: ?ψ) = _ /\
              ?σ = _ /\ _ ] =>
          exists χ, self, lcl, x, α, m, args, b, ψ;
            let χ' := fresh "χ" in
            let ψ' := fresh "ψ" in
            destruct σ as [χ' ψ'];
              exists χ'
        end.

        match goal with
        | [H : _ ∙ _ ⤳ _ |- _ ] =>
          inversion H;
            subst
        end;
          try solve [match goal with
                     | [H : _ ∙ _ ⤳ (_, ?ϕ :: ?ψ ++ _ :: _) |- _ ] =>
                       exists (ϕ :: ψ)
                     end;
                     repeat split;
                     auto;
                     repeat forall_in_auto;
                     auto];
          try solve [match goal with
                     | [H : _ :: _ = _ ++ _ :: _ |- _ ] =>
                       symmetry in H;
                       destruct (app_cons_1 H);
                       subst;
                       simpl in *;
                       repeat simpl_crush
                     end;
                     [repeat forall_in_auto;
                      unfold internal_frame in *;
                      simpl in *;
                      repeat external_internal_auto
                     |unfold_existentials;
                      match goal with
                      | [H : _ ∙ _ ⤳ (_, ?ϕ :: ?ψ ++ _ :: _) |- _ ] =>
                        exists (ϕ :: ψ)
                      end;
                      repeat split;
                      simpl;
                      auto;
                      try solve [crush];
                      unfold internal_frame in *;
                      repeat forall_in_auto;
                      auto]].

        * match goal with
          | [H : _ ∙ _ ⤳ (_, ?ϕ1 :: ?ϕ2 :: ?ψ ++ _ :: _) |- _ ] =>
            exists (ϕ1 :: ϕ2 :: ψ)
          end;
            repeat split;
            simpl in *;
            auto;
            repeat forall_in_auto;
            auto.
          unfold internal_frame;
            simpl.
          unfold internal_self in *;
            unfold_existentials;
            auto.

        *


  Qed.

  Definition is_call_call (M1 M2 : mdl)(σ1 σ2 : config) :=
    M1 ⦂ M2 ⦿ σ1 ⤳ σ2 /\
    internal_step M1 M2 σ1 /\
    exists χ1 self lcl x α m args b ψ1 χ2 ϕ ψ2,
      σ1 = (χ1, frm self lcl (c_ (x ≔m α ▸ m ⟨ args ⟩) ;; b) :: ψ1) /\
      σ2 = (χ2, ϕ :: ψ2 ++ frm self lcl (x ≔♢ ;; b) :: ψ1) /\
      length ψ2 > 0 /\
      forall_in ψ2 (internal_frame M1 M2 σ2).

  Definition is_call_rtrn (M1 M2 : mdl)(σ1 σ2 : config) :=
    M1 ⦂ M2 ⦿ σ1 ⤳ σ2 /\
    internal_step M1 M2 σ1 /\
    exists χ1 self lcl x α m args b ψ χ2 v,
      σ1 = (χ1, frm self lcl (c_ (x ≔m α ▸ m ⟨ args ⟩) ;; b) :: ψ) /\
      σ2 = (χ2, frm self ([x ↦ v] lcl) (c_ b) :: ψ).

  Definition is_rtrn_call (M1 M2 : mdl)(σ1 σ2 : config) :=
    M1 ⦂ M2 ⦿ σ1 ⤳ σ2 /\
    internal_step M1 M2 σ1 /\
    exists χ1 ϕ1 ϕ2 ψ1 ψ2 ψ χ2 v,
      σ1 = (χ1, ϕ1 :: ψ1 ++ ψ) /\
      rtrns σ1 v /\
      σ2 = (χ2, ϕ2 :: ψ2 ++ ψ) /\
      length ψ1 > 0 /\
      length ψ2 > 0 /\
      forall_in ψ1 (internal_frame M1 M2 σ2) /\
      forall_in ψ2 (internal_frame M1 M2 σ2).

  Definition is_rtrn_rtrn (M1 M2 : mdl)(σ1 σ2 : config) :=
    M1 ⦂ M2 ⦿ σ1 ⤳ σ2 /\
    internal_step M1 M2 σ1 /\
    exists χ1 ϕ self lcl x b v ψ1 ψ2 χ2,
      σ1 = (χ1, ϕ :: ψ1 ++ (frm self lcl (x ≔♢ ;; b))  :: ψ2) /\
      rtrns σ1 v /\
      σ2 = (χ2, frm self ([x ↦ v] lcl) (c_ b) :: ψ2) /\
      length ψ1 > 0 /\
      forall_in ψ1 (internal_frame M1 M2 σ2).

  Lemma internal_reductions_ :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   internal_step M1 M2 σ1 ->
                   is_call_call M1 M2 σ1 σ2 \/
                   is_call_rtrn M1 M2 σ1 σ2 \/
                   is_rtrn_call M1 M2 σ1 σ2 \/
                   is_rtrn_rtrn M1 M2 σ1 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred.
  Qed.

  Close Scope reduce_scope.

End OperationalSemanticsProperties.
