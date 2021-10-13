Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import List.
Require Import specw.
Require Import hoare.
Require Import inference.

(***
In this file we present the soundness argument. The final soundness proof of
SpecX as described in the paper can be found at the bottom of this file as

===> Theorem necessity_triple_soundness

We make several assumptions:
(1) there exists some encapsulation algorithm that is sound. While this is wired into a rudimentary one defined in inference.v
    that mirrors the rudimentary encapsulation system as defined in the paper, we do not use any results from there here.
(2) there is a sound underlying Hoare logic
(3) there is a sound proof system for deriving proofs of SpecW specifications of the form: M ⊢ A
(4) there are several minor assumptions to do with variable substitution and renaming that are prohibitively
    complex for work in Coq, but would not be problematic in a paper proof.
(5) to avoid tedious, but already well trod ground, we avoid proofs about
    the underlying hoare logic, specifically that if {P} C {Q}, then ¬ P is a necessary precondition for {¬ Q}
 ***)

Module Soundness(L : LanguageDef).

  Export L.
  Module L_Inference := Inference(L).
  Import L_Inference.

  Open Scope specw_scope.
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

  Parameter class_cannot_change :
    forall M M' σ1 σ2, M ⦂ M' ⦿ σ1 ⤳⋆ σ2 ->
                  forall x C, M ◎ σ1 ⊨ a_class (e_ x) C ->
                         M ◎ σ2 ⊨ a_class (e_ x) C.

  Parameter no_external_calls :
    forall M1 M2 M σ1 σ2, M1 ⋄ M2 ≜ M ->
                     M ∙ σ1 ⤳ σ2 ->
                     (exists χ ϕ ψ x, σ1 = (χ, ϕ :: ψ) /\
                                 ((exists s, contn ϕ = c_ (rtrn x ;; s)) \/
                                  contn ϕ = (c_rtrn x))) ->
                     external_self M1 M2 σ1 ->
                     external_self M1 M2 σ2.

  Axiom internal_is_encapsulated :
    forall M A e, intrnl M A e ->
             encapsulated M A (a_exp e).

  Axiom encapsulation_soundness :
    forall M A A', enc M A A' ->
              encapsulated M A A'.

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
    apply prs_refl.
    eapply pair_reduction_end_external_self;
      eauto.
  Qed.

  Hint Resolve pair_reduction_is_pair_reductions : reduce_db.

(*)  Lemma classical_to_necessary :
    forall M P Q C, M ⊢ {pre: P} C {post: Q} ->
               forall M' σ σ', is_call .*)

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
          auto with reduce_db specw_db.
        apply prs_refl.
        eapply pair_reduction_start_external_self;
          eauto.
  Qed.

  (*  Lemma if1_classical*)

  Lemma func_equality :
    forall {A B : Type} (f g : A -> B), f = g ->
                                  forall a, f a = g a.
  Proof.
    intros;
      auto.
    rewrite H;
      auto.
  Qed.

  Lemma calls_is_call :
    forall M σ α m β, (M ◎ σ ⊨ ∃x.[ a♢ 0 calls a_ α ◌ m ⟨ (fun v : value => Some (av_ v)) ∘ β ⟩]) ->
                 exists y, is_call σ y (m_call α m β).
  Proof.
    intros M σ α m β Hsat;
      inversion Hsat;
      subst.
    subst_simpl.
    subst_simpl.
    simpl in H2.
    inversion H2;
      subst.
    inversion H3;
      subst.
    exists x0;
      eapply is_meth_call
        with (ϕ:={| this := α1; local := lcl; contn := c_ (x0 ≔m y ▸ m ⟨ args ⟩);; b |})
             (y:=y);
      simpl;
      auto.
    apply functional_extensionality;
      intros x.
    apply func_equality with (a:=x) in H4;
      simpl in H4.
    destruct (args x) eqn : Ha;
      destruct (β x) eqn : Hb;
      auto.
    - destruct (lcl n) eqn : Hc;
        auto.
      + inversion H4;
          subst;
          auto.
      + inversion H4;
          subst;
          auto.
    - destruct (lcl n) eqn : Hc;
        auto.
      + inversion H4;
          subst;
          auto.
    - inversion H4;
        subst;
        auto.
  Qed.

  Definition no_free (A : asrt) :=
    forall (x : value) (n : nat), ([x /s n] A) = A.

  Lemma classical_with_calls :
    forall M P α m β Q, M ⊢ {pre: P} (m_call α m β) {post: Q} ->
                   no_free Q ->
                   forall σ, M ◎ σ ⊨ (∃x.[ a♢ 0 calls a_ α ◌ m ⟨ (fun v : value => Some (av_ v)) ∘ β ⟩]) ->
                        forall M' σ', M ⦂ M' ⦿ σ ⤳ σ' ->
                                 M ◎ σ ⊨ P ->
                                 M ◎ σ' ⊨ Q.
  Proof.
    intros.
    destruct (calls_is_call M σ α m β H1).
    apply hoare_soundness in H.
    inversion H;
      subst.
    specialize (H11 M' x σ σ').
    repeat auto_specialize.
    repeat destruct_exists_loo;
      andDestruct.
    rewrite H0 in Hb0;
      auto.
  Qed.

  Parameter sat_implies_no_free_variables :
    forall M σ A, M ◎ σ ⊨ A ->
             no_free A.

  Parameter neg_no_free :
    forall A, no_free A -> no_free (¬ A).

  Lemma classical_to_necessary :
    forall M P1 P2 α m β Q, M ⊢ {pre: P1 ∧ ¬ P2} (m_call α m β) {post: ¬ Q} ->
                       onlyif1 M (P1 ∧ (∃x.[ a♢ 0 calls a_ α ◌ m ⟨ (fun v : value => Some (av_ v)) ∘ β ⟩])) Q P2.
  Proof.
    intros.
    necessity_soundness_simpl.
    destruct (sat_excluded_middle M σ1 (P1 ∧ ¬ P2)).
    - apply classical_with_calls with (α:=α)(m:=m)(β:=β)(Q:=¬ Q)(P:=P1 ∧ ¬ P2)(M':=M')(σ':=σ2) in H4;
        auto;
      [| eapply neg_no_free, sat_implies_no_free_variables; eauto].
      destruct (sat_excluded_middle M σ1 P2);
        auto.
      apply sat_not in H6.
      a_prop.
    - inversion H5;
        subst.
      + apply sat_not in H9;
          a_prop.
      + inversion H9;
          auto.
  Qed.

  (*  Lemma if1_wrapped*)

  Parameter wrapped_necessary_condition :
    forall M α C m β α' P P',  M ⊢ {pre: P' ∧ (a_class (e_ α) C) ∧ ¬ P} (m_call α m β) {post: ¬ (a_exp (e♢ 0 ⩵ (e_addr α')))} ->
                          onlyif1 M (P' ∧ a_class (e_ α) C ∧
                                     (∃x.[ a♢ 0 calls a_ α ◌ m ⟨ (fun v : value => Some (av_ v)) ∘ β ⟩]) ∧
                                     wrapped (a_ α')) (¬ wrapped (a_ α')) P.

  (*  Lemma if1_internal*)

  Lemma internal_call :
    forall M A1 A2, encapsulated M A1 A2 ->
               forall M' σ σ', arising M M' σ ->
                          M ⦂ M' ⦿ σ ⤳ σ' ->
                          M ◎ σ ⊨ A1 ->
                          M ◎ σ ⊨ A2 ->
                          M ◎ σ' ⊨ ¬ A2 ->
                          exists α C, C ∈ M /\
                                 M ◎ σ ⊨ (a_class (e_ α) C) /\
                                 exists α' m β, M ◎ σ ⊨ (a_ α') calls (a_ α) ◌ m ⟨ β ⟩.
  Proof.
    intros.
    unfold encapsulated in *.
    specialize (H M' σ σ');
      repeat auto_specialize.
    repeat destruct_exists_loo.
    a_prop.
    assert (exists α α', x = (a_ α) /\ x0 = (a_ α')).

    - inversion H;
        subst.
      inversion H10;
        subst;
        eauto.

    - repeat destruct_exists_loo;
        andDestruct;
        subst.
      inversion H5;
        subst.
      inversion H10;
        subst.
      exists α0, (cname o);
        repeat split;
        auto.
      + apply sat_class, has_cls with (α:=α0); auto.
        apply v_value.
      + exists α, m, f;
          auto.

  Qed.

  Lemma internal_reductions_implies_reduction :
    forall M M' σ σ', M ⦂ M' ⦿ σ ⤳… σ' ->
                 exists M'' σ'', M ⋄ M' ≜ M'' /\
                            M'' ∙ σ ⤳ σ''.
  Proof.
    intros M M' σ σ' Hred;
      induction Hred;
      eauto.
  Qed.

  Lemma pair_reduction_implies_reduction :
    forall M M' σ σ', M ⦂ M' ⦿ σ ⤳ σ' ->
                 exists M'' σ'', M ⋄ M' ≜ M'' /\
                            M'' ∙ σ ⤳ σ''.
  Proof.
    intros M M' σ σ' Hred;
      induction Hred;
      eauto.
    eapply internal_reductions_implies_reduction;
      eauto.
  Qed.

  Lemma calls_method_exists :
    forall M σ α1 α2 m β, M ◎ σ ⊨ ((a_ α1) calls (a_ α2) ◌ m ⟨ β ⟩) ->
                     forall C, M ◎ σ ⊨ (a_class (e_ α2) C) ->
                          forall CDef, ⟦ C ↦ CDef ⟧_∈ M ->
                                  forall M' σ', M ⦂ M' ⦿ σ ⤳ σ' ->
                                           m ∈ (CDef.(c_meths)).
  Proof.
    intros.
    inversion H;
      subst.
    inversion H6;
      subst.
    apply pair_reduction_implies_reduction in H2.
    repeat destruct_exists_loo;
      andDestruct.
    inversion Hb;
      subst.
    inversion H0;
      subst.
    inversion H5;
      subst.
    inversion H8;
      subst.
    rewrite H7 in H15;
      inversion H15;
      subst.
    rewrite H11 in H16;
      inversion H16;
      subst.
    inversion Ha;
      subst.
    destruct (eq_dec (cname o) Object).

    - rewrite e in H18.
      unfold extend in H18.
      rewrite H2 in H18.
      inversion H18;
        subst.
      simpl in H19.
      inversion H19.

    - destruct (partial_maps.partial_map_dec (cname o) M).
      + destruct_exists_loo.
        unfold extend in H18;
          rewrite H10 in H18.
        inversion H18;
          subst.
        rewrite H10 in H1;
          inversion H1;
          subst.
        eauto.
      + rewrite e in H1.
        crush.
  Qed.

  Parameter exists_subst :
    forall {A B C}`{Subst A B C} (a : A)(b : B)(c : C),
      exists a', a = ([c /s b] a').

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
      eapply pair_reductions_end_external_self;
        eauto.

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
      exists σ1;
        split;
        auto.
      apply prs_refl.
      eapply pair_reductions_start_external_self;
        eauto.

    - necessity_soundness_simpl.
      apply H in H3;
        auto.
      * destruct_exists_loo;
          andDestruct.
        necessity_soundness_simpl.
        exists σ;
          repeat split;
          auto.
        eapply entails_implies;
          [ apply entails_inf_soundness
           |
           |apply Hb0];
          eauto.
      * eapply entails_implies;
          [ apply entails_inf_soundness
           |
           |apply H1];
          eauto.
      * eapply entails_implies;
          [ apply entails_inf_soundness
           |
           |apply H2];
          eauto.

    - necessity_soundness_simpl.
      + apply H in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.
        disj_split;
          auto.
        necessity_soundness_simpl.
        apply (H0 M' σ1 σ)
          in H1;
          auto.
        destruct_exists_loo.
        andDestruct.
        a_prop.

    - necessity_soundness_simpl.
      + apply H in H4;
          auto;
          destruct_exists_loo;
          andDestruct.
        exists σ; repeat split; auto.
        a_prop; auto.
        disj_split;
          auto.
        necessity_soundness_simpl.
        apply (H0 M' σ σ2)
          in H6;
          auto.
        destruct_exists_loo.
        andDestruct.
        a_prop.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      necessity_soundness_simpl.
      apply H0 in Ha;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      eexists;
        repeat split;
        eauto with reduce_db.
      eapply pair_reductions_transitive;
        eauto.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      necessity_soundness_simpl.
      apply H0 in Ha0;
        auto;
        destruct_exists_loo;
        andDestruct;
        a_prop.
      exists σ0;
        repeat split;
        eauto with reduce_db.
      eapply pair_reductions_transitive;
        eauto.

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ ∃x.[ _ ] |- _] =>
        inversion H;
          subst
      end.
      specialize (H x).
      apply H in H3;
        auto.

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ ∃x.[ _ ] |- _] =>
        inversion H;
          subst
      end.
      specialize (H x).
      apply H in H3;
        auto.

    - necessity_soundness_simpl.
      unfold onlyif in H.
      specialize (H M' σ1 σ2).
      eapply entails_implies;
        [apply entails_inf_soundness, e1
        |apply H0
        |].
      apply H;
        auto.
      * eapply entails_implies;
          [apply entails_inf_soundness
          |
          |apply H1];
          eauto.
      * eapply entails_implies;
          [apply entails_inf_soundness
          |
          |apply H2];
          eauto.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl.
      eapply H0 in H4;
        auto;
        repeat destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl;
        auto.

    - necessity_soundness_simpl.
      apply H in H4;
        auto;
        destruct_exists_loo;
        andDestruct;
        necessity_soundness_simpl;
        auto.

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ (∃x.[ _ ]) |- _ ] =>
        inversion H;
          subst
      end.
      specialize (H x).
      necessity_soundness_simpl;
        auto.

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ (∃x.[ _ ]) |- _ ] =>
        inversion H;
          subst
      end.
      specialize (H x).
      necessity_soundness_simpl;
        auto.

    - necessity_soundness_simpl.
      apply nsat_implies_not_sat in H1.
      contradiction.
      apply nsat_not.
      eapply class_cannot_change;
        eauto.

    - necessity_soundness_simpl.
      apply classical_to_necessary in h.
      unfold onlyif1 in *.
      specialize (h M' σ1 σ2);
        repeat auto_specialize.
      apply h;
        auto.
      a_prop;
        auto.

    - necessity_soundness_simpl.
      apply wrapped_necessary_condition in h.
      unfold onlyif1 in *.
      specialize (h M' σ1 σ2);
        auto_specialize.
      apply h;
        auto.
      a_prop;
        auto.

    -  necessity_soundness_simpl.
        assert (Ha : encapsulated M A1 (¬ A2));
         [apply encapsulation_soundness; auto|].
       unfold encapsulated in Ha.
       specialize (Ha M' σ1 σ2);
         repeat auto_specialize.
       assert (Hdup : M ◎ σ1 ⊨ A1);
         [auto|].
       eapply entails_implies in H1;
         [
         |apply entails_inf_soundness, e0
         |apply H0].
       apply nsat_not, sat_not in H2;
         auto_specialize;
         repeat destruct_exists_loo;
         a_prop.

       destruct internal_call
         with (M:=M)(A1:=A1)(A2:=¬ A2)
              (M':=M')(σ:=σ1)(σ':=σ2);
         auto.

       + apply encapsulation_soundness;
           auto.

       + destruct H4 as [C].
         andDestruct.
         destruct Hb0 as [a1].
         destruct H4 as [m].
         destruct H4 as [β].
         inversion Ha0;
           subst.
         destruct (exists_subst β 0 (v_ a1)) as [β' Hex].
         specialize (H C x0 m x β').
         auto_specialize.
         assert (m ∈ c_meths x0).

         * inversion H4;
             subst.
           inversion H9;
             subst.
           apply pair_reduction_implies_reduction in
               H3.
           repeat destruct_exists_loo;
             andDestruct.
           inversion Hb;
             subst.
           rewrite H12 in H20;
             inversion H20;
             subst.
           simpl_crush.
           inversion Ha1;
             subst.
           inversion H11;
             subst.
           simpl_crush.
           inversion H13;
             subst.
           simpl_crush.
           assert (Hrewrite : M (cname o1) = M0 (cname o1));
             [|].
           ** inversion Ha0;
                subst.
              unfold extend.
              destruct (partial_maps.partial_map_dec (cname o1) M) as [Hz|Hz];
                auto.
              *** destruct Hz as [Cz Hz];
                    rewrite Hz;
                    auto.

              *** simpl_crush.

           ** rewrite <- Hrewrite in *.
              rewrite H5 in H23.
              inversion H23;
                subst.
              eauto.

         * auto_specialize.
           apply H in H3;
             auto.
           a_prop;
             auto.
           apply sat_ex with (x:=v_ a1).
           subst_simpl;
             subst;
             auto.
           inversion H2;
             subst.
           inversion H10;
             subst.
           auto.

    - necessity_soundness_simpl.
      unfold onlyif in *.
      apply H with (M':=M')(σ2:=σ2);
        auto with reduce_db.

    - necessity_soundness_simpl.
      apply H in H3;
        auto;
        necessity_soundness_simpl;
        auto.
      * eapply entails_implies;
          [apply entails_inf_soundness, e1
          |eauto
          |apply H3].
      * eapply entails_implies;
          [apply entails_inf_soundness, e
          |eauto
          |apply H1].
      * eapply entails_implies;
          [apply entails_inf_soundness, e0
          |eauto
          |apply H2].
        eapply arising_trans.
        eauto.
        apply pair_reduction_is_pair_reductions in H3.
        auto.

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

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ (∃x.[ _ ]) |- _ ] =>
        inversion H;
          subst
      end.
      specialize (H x).
      necessity_soundness_simpl;
        auto.

    - necessity_soundness_simpl.
      match goal with
      | [H : _ ◎ _ ⊨ (∃x.[ _ ]) |- _ ] =>
        inversion H;
          subst
      end.
      specialize (H x).
      necessity_soundness_simpl;
        auto.

  Qed.




End Soundness.
