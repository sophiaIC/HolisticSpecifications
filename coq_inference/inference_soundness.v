Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import List.
Require Import chainmail.
Require Import hoare.
Require Import inference.

Module Soundness(L : LanguageDef).

  Export L.
  Module L_Inference := Inference(L).
  Import L_Inference.

  Open Scope chainmail_scope.
  Open Scope reduce_scope.

  Definition encapsulated (M : mdl)(A A' : asrt) :=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ⦂ M' ⦿ σ1 ⤳ σ2 ->
                M ⦂ M' ◎ σ1  ⊨ A ->
                M ⦂ M' ◎ σ1 ⊨ A' ->
                M ⦂ M' ◎ σ2 ⊨ ¬ A' ->
                exists α1 α2 m β, M ⦂ M' ◎ σ1 ⊨ (α1 calls α2 ◌ m ⟨ β ⟩ ∧
                                            α1 external ∧
                                            α2 internal).

  Ltac encap_intros :=
    match goal with
    | [|- encapsulated _ _ _] =>
      unfold encapsulated;
      let M := fresh "M" in
      let σ1 := fresh "σ" in
      let σ2 := fresh "σ" in
      let H := fresh in
      intros M σ1 σ2 H;
      intros
    end.

  Ltac chainmail_auto :=
    match goal with
    | [H : _ ⦂ _ ◎ _ ⊨ (a_exp (e_int _)) |-_] =>
      inversion H;
      subst;
      clear H

    | [H : ~ exp_satisfaction _ _ _ (e_true) |- _] =>
      contradiction H;
      auto

    | [H : exp_satisfaction _ _ _ _ |- _] =>
      inversion H;
      clear H

    | [H : _ ⦂ _ ◎ _ ⊨ ¬ _ |-_] =>
      inversion H;
      subst;
      clear H

    | [H : _ ⦂ _ ◎ _ ⊭ (a_exp (e_true)) |-_] =>
      inversion H;
      subst;
      clear H
    end.

  Ltac eval_auto :=
    match goal with
    | [H : evaluate _ _ (e_int _) (v_true)  |- _] =>
      inversion H;
      subst
    end.

  Lemma pair_reduction_external_self :
    forall M1 M2 σ1 σ2,
      M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
      external_self M1 M2 σ2.
    intros.
    match goal with
    | [H : _ ⦂ _ ⦿ _ ⤳ _ |- _ ] =>
      inversion H; auto
    end.
  Qed.

  Lemma pair_reductions_external_self :
    forall M1 M2 σ1 σ2,
      M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
      external_self M1 M2 σ1 ->
      external_self M1 M2 σ2.
  Proof.
    intros M1 M2 σ1 σ2 Hred Hext;
      induction Hred; auto.

    apply IHHred.
    eapply pair_reduction_external_self; eauto.
  Qed.

  Parameter initial_external_self :
    forall σ, initial σ ->
         forall M1 M2, external_self M1 M2 σ.

  Lemma arising_external_self :
    forall M1 M2 σ, arising M1 M2 σ ->
               external_self M1 M2 σ.
  Proof.
    intros.
    unfold arising in *;
      destruct_exists_loo;
      andDestruct.
    match goal with
    | [H : initial _ |- external_self ?M ?M' _ ] =>
      apply initial_external_self with (M1:=M)(M2:=M') in H
    end.
    eapply pair_reductions_external_self; eauto.
  Qed.

  Parameter no_external_calls :
    forall M1 M2 M σ1 σ2, M1 ⋄ M2 ≜ M ->
                     M ∙ σ1 ⤳ σ2 ->
                     (exists χ ϕ ψ x, σ1 = (χ, ϕ :: ψ) /\
                                 ((exists s, contn ϕ = c_ (rtrn x ;; s)) \/
                                  contn ϕ = (c_rtrn x))) ->
                     external_self M1 M2 σ1 ->
                     external_self M1 M2 σ2.


  Lemma internal_reductions_is_call :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                   exists α1 α2 m β, M1 ⦂ M2 ◎ σ1 ⊨ (α1 calls α2 ◌ m ⟨ β ⟩ ∧
                                                α1 external ∧
                                                α2 internal).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred.

    - unfold external_self, internal_self in *;
        repeat destruct_exists_loo;
        andDestruct;
        subst.
      unfold is_external, is_internal in *;
        repeat destruct_exists_loo;
        andDestruct;
        subst.
      match goal with
      | [H : _ ∙ _ ⤳ _ |- _ ] =>
        inversion H;
          subst
      end;
        repeat map_rewrite.
      + crush.
      + admit.
      + admit.
      + eapply no_external_calls in H0;
          eauto.

  Admitted.

  Lemma intrnl_field_is_encapsulated :
    forall M A e f, intrnl M A e ->
               encapsulated M A (a_exp (e_acc_f e f)).
  Proof.
    intros.
    encap_intros.
    match goal with
    | [H : _ ⦂ _ ⦿ _ ⤳ _ |- _] =>
      inversion H;
        subst
    end.

    Admitted.

  Theorem internal_is_encapsulated :
    forall M A e, intrnl M A e ->
             encapsulated M A (a_exp e).
  Proof.
    intros M A e Hint;
      induction Hint;

      try solve [encap_intros;
                 match goal with
                 | [H1 : _ ⦂ _ ◎ _ ⊨ (a_exp _),
                         H2 : _ ⦂ _ ◎ _ ⊨ ¬ _|- _] =>
                   inversion H1;
                   subst
                 end;
                 match goal with
                 | [H : exp_satisfaction _ _ _ _ |- _ ] =>
                   inversion H;
                   subst
                 end;
                 match goal with
                 | [H : evaluate _ _ _ _ |- _ ] =>
                   inversion H;
                   subst
                 end].

    - encap_intros.
      match goal with
      | [H : _ ⦂ _ ◎ _ ⊨ (a_exp (e_true)) |- _] =>
        inversion H;
          subst;
          clear H
      end.
      repeat chainmail_auto.
      eauto with chainmail_db.

    - encap_intros.
      admit.

    - encap_intros.
      admit.

  Admitted.

  Theorem encapsulation_soundness :
    forall M A A', enc M A A' ->
              encapsulated M A A'.
  Proof.
    intros M A A' Henc;
      induction Henc.

    - apply internal_is_encapsulated;
        auto.

    - admit.

    - admit.

    - admit.

    - admit.

    - encap_intros.
      match goal with
      | [Hent : M ⊢ ?A1 ⊇ ?A2,
                Har : arising _ _ _,
                      Hsat : _ ⦂ _ ◎ _ ⊨ ?A1 |- _] =>
        apply (entails_implies Hent Har) in Hsat
      end.
      eauto.
  Admitted.

  Definition onlythrough (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ⦂ M' ◎ σ1 ⊨ A1 ->
                M ⦂ M' ◎ σ2 ⊨ A2 ->
                M ⦂ M' ⦿ σ1 ⤳⋆ σ2 ->
                exists σ, (σ = σ1 \/ M ⦂ M' ⦿ σ1 ⤳⋆ σ) /\
                     (σ = σ2 \/ M ⦂ M' ⦿ σ ⤳⋆ σ2) /\
                     M ⦂ M' ◎ σ ⊨ A.

  Definition onlyif (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ⦂ M' ◎ σ1 ⊨ A1 ->
                M ⦂ M' ◎ σ2 ⊨ A2 ->
                M ⦂ M' ⦿ σ1 ⤳⋆ σ2 ->
                M ⦂ M' ◎ σ1 ⊨ A.

  Definition onlyif1 (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ⦂ M' ◎ σ1 ⊨ A1 ->
                M ⦂ M' ◎ σ2 ⊨ A2 ->
                M ⦂ M' ⦿ σ1 ⤳ σ2 ->
                M ⦂ M' ◎ σ1 ⊨ A.

  Lemma arising_trans :
    forall M1 M2 σ1 σ2, arising M1 M2 σ1 ->
                   M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   arising M1 M2 σ2.
  Proof.
    intros.
    unfold arising in *;
      repeat destruct_exists_loo;
      andDestruct.
    exists σ;
      split;
      auto.
    eapply pair_reductions_transitive;
      eauto.
  Qed.

  Ltac auto_entails :=
    repeat match goal with
           | [H : ?Ma ⦂ ?Mb ◎ ?σa ⊨ ?Aa,
                  Hent : ?Ma ⊢ ?Aa ⊇ ?Ab,
                         Harr : arising _ _ _ |- _ ] =>
             notHyp (Ma ⦂ Mb ◎ σa ⊨ Ab);
             let H := fresh in
             assert (H : Ma ⦂ Mb ◎ σa ⊨ Ab);
             [apply (entails_implies Hent Harr); auto|]
           end.

  Ltac auto_arising :=
    repeat
      match goal with
      | [Har : arising ?M1' ?M2' ?σ1',
                Hred : ?M1' ⦂ ?M2' ⦿ ?σ1' ⤳⋆ ?σ2' |- _] =>
        notHyp (arising M1' M2' σ2');
        let H := fresh in
        assert (H : arising M1' M2' σ2');
        [solve [apply (arising_trans M1' M2' σ1' σ2' Har); eauto]|]
      end.

  Ltac apply_necessity :=
    repeat (
        match goal with
        | [Hoi : onlyif ?Ma ?Aa ?Ab ?A,
                 Har : arising ?Ma ?Mb ?σa,
                       Hsat1 : ?Ma ⦂ ?Mb ◎ ?σa ⊨ ?Aa,
                               Hsat2 : ?Ma ⦂ ?Mb ◎ ?σb ⊨ ?Ab,
                                       Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳⋆ ?σb |- _] =>
          notHyp (Ma ⦂ Mb ◎ σa ⊨ A);
          assert (Ma ⦂ Mb ◎ σa ⊨ A);
          [apply (Hoi Mb σa σb Har); auto|]
        end);
    repeat (
        match goal with
        | [Hoi1 : onlyif1 ?Ma ?Aa ?Ab ?A,
                  Har : arising ?Ma ?Mb ?σa,
                        Hsat1 : ?Ma ⦂ ?Mb ◎ ?σa ⊨ ?Aa,
                                Hsat2 : ?Ma ⦂ ?Mb ◎ ?σb ⊨ ?Ab,
                                        Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳ ?σb |- _] =>
          notHyp (Ma ⦂ Mb ◎ σa ⊨ A);
          assert (Ma ⦂ Mb ◎ σa ⊨ A);
          [apply (Hoi1 Mb σa σb Har); auto|]
        end);
    repeat (
        match goal with
        | [Hot : onlythrough ?Ma ?Aa ?Ab ?A,
                 Har : arising ?Ma ?Mb ?σa,
                       Hsat1 : ?Ma ⦂ ?Mb ◎ ?σa ⊨ ?Aa,
                               Hsat2 : ?Ma ⦂ ?Mb ◎ ?σb ⊨ ?Ab,
                                       Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳⋆ ?σb |- _] =>
          notHyp (exists σ, (σ = σa \/ Ma ⦂ Mb ⦿ σa ⤳⋆ σ) /\
                       (σ = σb \/ Ma ⦂ Mb ⦿ σ ⤳⋆ σb) /\
                       Ma ⦂ Mb ◎ σ ⊨ A);
          assert (exists σ, (σ = σa \/ Ma ⦂ Mb ⦿ σa ⤳⋆ σ) /\
                       (σ = σb \/ Ma ⦂ Mb ⦿ σ ⤳⋆ σb) /\
                       Ma ⦂ Mb ◎ σ ⊨ A);
          [apply (Hot Mb σa σb Har); auto|]
        end).

  Ltac necessity_soundness_simpl :=
    unfold onlythrough, onlyif, onlyif1;
    intros;
    auto_arising;
    auto_entails;
    repeat apply_necessity;
    repeat auto_arising;
    repeat (a_prop);
    repeat (disj_split);
    repeat auto_entails;
    repeat auto_specialize;
    repeat (destruct_exists_loo);
    repeat (andDestruct);
    repeat disj_split;
    subst;
    repeat apply_necessity;
    try solve[match goal with
              | [Hred : _ ⦂ _ ⦿ ?σa ⤳⋆ ?σb |- _] =>
                exists σa; eauto;
                repeat split;
                repeat auto_entails;
                repeat a_prop;
                repeat disj_split;
                repeat auto_specialize;
                repeat destruct_exists_loo;
                repeat andDestruct;
                repeat disj_split;
                repeat a_prop;
                auto
              end];
    try solve[match goal with
              | [Hred : _ ⦂ _ ⦿ ?σa ⤳⋆ ?σb |- _] =>
                exists σb; eauto;
                repeat split;
                repeat auto_entails;
                repeat a_prop;
                repeat disj_split;
                repeat auto_specialize;
                repeat destruct_exists_loo;
                repeat andDestruct;
                repeat disj_split;
                repeat a_prop;
                auto
              end];
    try solve[match goal with
              | [Hred1 : _ ⦂ _ ⦿ ?σa ⤳⋆ ?σb,
                 Hred2 : _ ⦂ _ ⦿ ?σb ⤳⋆ ?σc |- _] =>
                exists σb; eauto;
                repeat split;
                auto_arising;
                auto_entails;
                repeat a_prop;
                repeat disj_split;
                repeat auto_specialize;
                repeat destruct_exists_loo;
                repeat andDestruct;
                repeat disj_split;
                repeat a_prop;
                auto
              end].

  Theorem necessity_triple_soundness :
    (forall M A1 A2 A3, M ⊢ A1 to A2 onlyThrough A3 ->
                   onlythrough M A1 A2 A3) /\
    (forall M A1 A2 A3, M ⊢ A1 to A2 onlyIf A3 ->
                   onlyif M A1 A2 A3) /\
    (forall M A1 A2 A3, M ⊢ A1 to1 A2 onlyIf A3 ->
                   onlyif1 M A1 A2 A3).
  Proof.
    apply necessity_mutind;
      intros.

    - necessity_soundness_simpl.

    - necessity_soundness_simpl.

    - necessity_soundness_simpl.

    - necessity_soundness_simpl;
        necessity_soundness_simpl.

    - necessity_soundness_simpl;
        necessity_soundness_simpl.

    - necessity_soundness_simpl;
        try solve [match goal with
                   | [Hred : _ ⦂ _ ⦿ _ ⤳⋆ ?σ' |- _] =>
                     exists σ'
                   end;
                   repeat split;
                   auto;
                   a_prop;
                   disj_split;
                   auto;
                   apply_necessity;
                   repeat destruct_exists_loo;
                   andDestruct;
                   a_prop];
        try solve [match goal with
                   | [Hred : _ ⦂ _ ⦿ ?σ' ⤳⋆ _ |- _] =>
                     exists σ'
                   end;
                   repeat split;
                   auto;
                   a_prop;
                   disj_split;
                   auto;
                   apply_necessity;
                   repeat destruct_exists_loo;
                   andDestruct;
                   a_prop].

    - necessity_soundness_simpl.
      + a_prop;
          repeat disj_split.
        * eexists;
            eauto.
        * apply_necessity;
            repeat destruct_exists_loo;
            andDestruct;
            a_prop.
      + a_prop;
          repeat disj_split.
        * eexists;
            eauto.
        * auto_arising.
          apply_necessity;
            repeat destruct_exists_loo;
            andDestruct;
            a_prop.

    - necessity_soundness_simpl;
        try solve [repeat destruct_exists_loo;
                   andDestruct;
                   repeat disj_split;
                   subst;
                   eauto].
      + 


  Qed.


End Soundness.
