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
                M ◎ σ1  ⊨ A ->
                M ◎ σ1 ⊨ A' ->
                M ◎ σ2 ⊨ ¬ A' ->
                exists α1 α2 m β, M ◎ σ1 ⊨ (α1 calls α2 ◌ m ⟨ β ⟩ ∧
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
    | [H : _ ◎ _ ⊨ (a_exp (e_int _)) |-_] =>
      inversion H;
      subst;
      clear H

    | [H : ~ exp_satisfaction _ _ (e_true) |- _] =>
      contradiction H;
      auto

    | [H : exp_satisfaction _ _ _ |- _] =>
      inversion H;
      clear H

    | [H : _ ◎ _ ⊨ ¬ _ |-_] =>
      inversion H;
      subst;
      clear H

    | [H : _ ◎ _ ⊭ (a_exp (e_true)) |-_] =>
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
    forall M M' σ1 σ2, M ⦂ M' ⦿ σ1 ⤳… σ2 ->
                  exists α1 α2 m β, M ◎ σ1 ⊨ (α1 calls α2 ◌ m ⟨ β ⟩ ∧
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

  Axiom internal_is_encapsulated :
    forall M A e, intrnl M A e ->
             encapsulated M A (a_exp e).
  (*Proof.
    intros M A e Hint;
      induction Hint;

      try solve [encap_intros;
                 match goal with
                 | [H1 : _ ◎ _ ⊨ (a_exp _),
                         H2 : _ ◎ _ ⊨ ¬ _|- _] =>
                   inversion H1;
                   subst
                 end;
                 match goal with
                 | [H : exp_satisfaction _ _ _ |- _ ] =>
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
      | [H : _ ◎ _ ⊨ (a_exp (e_true)) |- _] =>
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

  Admitted.*)

  Axiom encapsulation_soundness :
    forall M A A', enc M A A' ->
              encapsulated M A A'.
(*  Proof.
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
                      Hsat : _ ◎ _ ⊨ ?A1 |- _] =>
        apply (entails_implies Hent Har) in Hsat
      end.
      eauto.
  Admitted.*)

  Definition onlythrough (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ◎ σ1 ⊨ A1 ->
                M ◎ σ2 ⊨ A2 ->
                M ⦂ M'  ⦿ σ1 ⤳⋆ σ2 ->
                exists σ, (M ⦂ M' ⦿ σ1 ⤳⋆ σ) /\
                     (M ⦂ M' ⦿ σ ⤳⋆ σ2) /\
                     M ◎ σ ⊨ A.

  Definition onlyif (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ◎ σ1 ⊨ A1 ->
                M ◎ σ2 ⊨ A2 ->
                M ⦂ M' ⦿ σ1 ⤳⋆ σ2 ->
                M ◎ σ1 ⊨ A.

  Definition onlyif1 (M : mdl)(A1 A2 A : asrt):=
    forall M' σ1 σ2, arising M M' σ1 ->
                M ◎ σ1 ⊨ A1 ->
                M ◎ σ2 ⊨ A2 ->
                M ⦂ M' ⦿ σ1 ⤳ σ2 ->
                M ◎ σ1 ⊨ A.

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
           | [H : ?Ma ◎ ?σa ⊨ ?Aa,
                  Hent : ?Ma ⊢ ?Aa ⊇ ?Ab,
                         Harr : arising _ _ _ |- _ ] =>
             notHyp (Ma ◎ σa ⊨ Ab);
             let H := fresh in
             assert (H : Ma ◎ σa ⊨ Ab);
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
                       Hsat1 : ?Ma ◎ ?σa ⊨ ?Aa,
                               Hsat2 : ?Ma ◎ ?σb ⊨ ?Ab,
                                       Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳⋆ ?σb |- _] =>
          notHyp (Ma ◎ σa ⊨ A);
          assert (Ma ◎ σa ⊨ A);
          [apply (Hoi Mb σa σb Har); auto|]
        end);
    repeat (
        match goal with
        | [Hoi1 : onlyif1 ?Ma ?Aa ?Ab ?A,
                  Har : arising ?Ma ?Mb ?σa,
                        Hsat1 : ?Ma ◎ ?σa ⊨ ?Aa,
                                Hsat2 : ?Ma ◎ ?σb ⊨ ?Ab,
                                        Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳ ?σb |- _] =>
          notHyp (Ma ◎ σa ⊨ A);
          assert (Ma ◎ σa ⊨ A);
          [apply (Hoi1 Mb σa σb Har); auto|]
        end);
    repeat (
        match goal with
        | [Hot : onlythrough ?Ma ?Aa ?Ab ?A,
                 Har : arising ?Ma ?Mb ?σa,
                       Hsat1 : ?Ma ◎ ?σa ⊨ ?Aa,
                               Hsat2 : ?Ma ◎ ?σb ⊨ ?Ab,
                                       Hred :  ?Ma ⦂ ?Mb ⦿ ?σa ⤳⋆ ?σb |- _] =>
          notHyp (exists σ, (σ = σa \/ Ma ⦂ Mb ⦿ σa ⤳⋆ σ) /\
                       (σ = σb \/ Ma ⦂ Mb ⦿ σ ⤳⋆ σb) /\
                       Ma ◎ σ ⊨ A);
          assert (exists σ, (σ = σa \/ Ma ⦂ Mb ⦿ σa ⤳⋆ σ) /\
                       (σ = σb \/ Ma ⦂ Mb ⦿ σ ⤳⋆ σb) /\
                       Ma ◎ σ ⊨ A);
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

  Lemma pair_reduction_is_pair_reductions :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
  Proof.
    intros; eapply prs_trans;
      eauto with reduce_db.
  Qed.

  Hint Resolve pair_reduction_is_pair_reductions : reduce_db.

  Lemma changes_soundness_helper1 :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall A, M1 ◎ σ1 ⊨ A ->
                        M1 ◎ σ2 ⊨ ¬ A ->
                        exists σ σ', M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ /\
                                M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2 /\
                                M1 ⦂ M2 ⦿ σ ⤳ σ' /\
                                M1 ◎ σ ⊨ A /\
                                M1 ◎ σ' ⊨ ¬ A.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros.

    - a_prop.

    - destruct (sat_excluded_middle M1 σ A).
      + match goal with
        | [H : forall _, _,
             A' : asrt |- _ ] =>
          specialize (H A')
        end;
          repeat auto_specialize.
        repeat destruct_exists_loo;
          andDestruct.
        exists σ0, σ3;
          repeat split;
          auto with reduce_db.
        eapply prs_trans; eauto.
      + exists σ1, σ;
          repeat split;
          auto with reduce_db chainmail_db.
  Qed.

  (*  Lemma if1_classical*)

  (*  Lemma if1_wrapped*)

  (*  Lemma if1_internal*)

  Theorem necessity_triple_soundness :
    (forall M A1 A2 A3, M ⊢ A1 to A2 onlyThrough A3 ->
                   onlythrough M A1 A2 A3) /\
    (forall M A1 A2 A3, M ⊢ A1 to A2 onlyIf A3 ->
                   onlyif M A1 A2 A3) /\
    (forall M A1 A2 A3, M ⊢ A1 to1 A2 onlyIf A3 ->
                   onlyif1 M A1 A2 A3).
  Proof.
    apply necessity_mutind;
      intros;
      try solve [necessity_soundness_simpl; auto].

    - necessity_soundness_simpl.
      match goal with
      | [_ : _ ⦂ _ ⦿ _ ⤳⋆ ?σ2' |- _] =>
        exists σ2'; repeat split; auto
      end.
      apply prs_refl.

    - necessity_soundness_simpl.
      match goal with
      | [Hred : ?M1' ⦂ ?M2' ⦿ ?σ1' ⤳⋆ ?σ2',
                Hsat : ?M1' ◎ ?σ1' ⊨ ?A1' |-_] =>
        destruct (changes_soundness_helper1 M1' M2' σ1' σ2' Hred A1');
          auto
      end;
        repeat destruct_exists_loo;
        andDestruct.
      necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ ?σa ⊨ ?A2' |- context[_ ◎ _ ⊨ ?A2']] =>
        exists σa
      end;
        repeat split; eauto with reduce_db.

    - necessity_soundness_simpl.
      eauto with reduce_db.

    - necessity_soundness_simpl.
      apply H in H3;
        auto.
      destruct_exists_loo;
        andDestruct.
      necessity_soundness_simpl.

    - necessity_soundness_simpl.
      + apply H in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.

      + apply H0 in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.

    - necessity_soundness_simpl.
      + apply H in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.

      + apply H0 in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      disj_split; eauto.
      apply H0 in Ha;
        auto;
        destruct_exists_loo;
        andDestruct.
      a_prop.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      disj_split; eauto.
      necessity_soundness_simpl.
      apply H0 in Ha0;
        auto;
        destruct_exists_loo;
        andDestruct.
      a_prop.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl.
      apply H0 in Ha;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl.
      exists σ0; repeat split;
        auto with reduce_db.
      apply pair_reductions_transitive with (σ2 := σ);
        auto.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl.
      apply H0 in Ha0;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl.
      exists σ0; repeat split;
        auto with reduce_db.
      apply pair_reductions_transitive with (σ2 := σ);
        auto.

    - necessity_soundness_simpl;
        auto.
      a_prop;
        disj_split;
        auto.
      apply H0 in H4;
        auto;
        destruct_exists_loo;
        andDestruct.
      a_prop.

    - necessity_soundness_simpl;
        auto.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct.
      apply H0 in Ha;
        auto.

    - admit.

    - admit.

    - admit.

    - necessity_soundness_simpl.
      unfold onlyif in *.
      apply H with (M':=M')(σ2:=σ2);
        auto with reduce_db.

    - necessity_soundness_simpl.
      apply H in H3;
        auto;
        necessity_soundness_simpl;
        auto.
      apply pair_reduction_is_pair_reductions in H3.
      necessity_soundness_simpl.
      eapply entails_implies;
        eauto.

    - necessity_soundness_simpl.

      + apply pair_reduction_is_pair_reductions in H4.
        necessity_soundness_simpl.
        auto.
      + apply pair_reduction_is_pair_reductions in H4.
        necessity_soundness_simpl.
        auto.

    - necessity_soundness_simpl;
        a_prop.
      + apply pair_reduction_is_pair_reductions in H4.
        necessity_soundness_simpl;
          auto.
      + apply pair_reduction_is_pair_reductions in H4.
        necessity_soundness_simpl;
          necessity_soundness_simpl;
          auto.
        apply H0 in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        a_prop.

  Qed.


End Soundness.
