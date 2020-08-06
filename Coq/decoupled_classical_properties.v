Require Import common.
Require Import loo_def.
Require Import decoupling.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import function_operations.
Require Import sbst_decoupled.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Theorem prop_and_if_sat_and :
  (forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_and A1 A2) ->
                       M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 /\
                       M1 ⦂ M2 ◎ σ0 … σ ⊨ A2).
Proof.
  intros M1 M2 σ0 σ A1 A2 Hsat;
    inversion Hsat;
    auto.
Qed.

Theorem prop_or_if_nsat_and :
  (forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_and A1 A2) ->
                       M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 \/
                       M1 ⦂ M2 ◎ σ0 … σ ⊭ A2).
Proof.
  intros M1 M2 σ0 σ A1 A2 Hnsat;
    inversion Hnsat;
    auto.
Qed.

(** Lemma 5: Classical (4) *)
(** This is yet to be proven. *)
Theorem sat_implies_not_nsat_mutind :
  (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                   ~ M1 ⦂ M2 ◎ σ0 … σ ⊭ A) /\

  (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                   ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ A).
Proof.
  apply sat_mutind;
    intros;
    intros Hcontra;
    eauto with chainmail_db;
    try solve [inversion Hcontra; auto].

  - (* sat_name *)
    inversion Hcontra;
      subst;
      crush.

  - (* sat_exp *)
    inversion Hcontra; subst.
    unique_loo_exp.
    link_unique_auto.
    eval_rewrite; crush.

  - (* Case 3: sat_class *)
    inversion Hcontra; subst; 
      [eval_rewrite;
       crush|crush; eauto].

  - (* Case 11: sat_all *)
    inversion Hcontra; subst;
      contradiction (H x);
      auto.

  - (* Case 14: sat_access2 *)
    inversion Hcontra; subst.
    match goal with
    | [Ha : forall o' f' α', mapp ?σ ?α1 = Some o' ->
                        flds o' f' = Some (v_addr α') ->
                        ?α2 <> α',
         Hb : mapp ?σ ?α1 = Some ?o,
         Hc : flds ?o ?f = Some (v_addr ?α2)  |- _] => 
      specialize (Ha o f α2 Hb Hc)
    end.
    crush.

  - (* Case 15: sat_access3 *)
    inversion Hcontra; subst.
    assert (Htmp : (χ, ϕ::ψ) = (χ, ϕ::ψ));
      [auto|].
    specialize (H7 x i i0 ψ ϕ χ s Htmp e0).
    crush.

  - (* Case 16: sat_call_1 *)
    inversion Hcontra; subst.
    + match goal with
      | [H : mapp ?σ this <> Some ?v,
             Hint : ⌊this⌋ ?σ ≜ ?v  |- _] =>
        contradiction H;
        inversion Hint; subst
      end.
      auto.
    + unfold snd in *; simpl_crush.
      match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst
      end.
      match goal with
      | [H : mapp ?σ ?x <> Some ?v,
             Hint : ⌊?x⌋ ?σ ≜ ?v  |- _] =>
        contradiction H;
        inversion Hint; subst
      end.
      auto.
    + unfold snd in *; simpl_crush.
      match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst
      end.
      crush.

  - (* external *)
    inversion Hcontra;
      interpretation_rewrite;
      subst;
      crush.

  - (* internal *)
    inversion Hcontra;
      interpretation_rewrite;
      subst;
      crush.

  - (* next *)
    inversion Hcontra;
      subst.
    unique_reduction_auto.
    auto.

(*  - (* will *)
    inversion Hcontra; subst.
    match goal with
    | [H : forall σ'', ?M1 ⦂ ?M2 ⦿ ?σ ⤳⋆ σ'' -> _,
         Ha : ?M1 ⦂ ?M2 ⦿ ?σ ⤳⋆ ?σ' |- _] =>
      specialize (H σ')
    end;
      auto_specialize;
      auto.*)

  - (* prev 1 *)
    inversion Hcontra; subst.
    + assert (Heq : σ'0 = σ');
        [eapply pair_reductions_unique_prev; eauto|subst].
      auto.
    + admit. (* contradiction: cyclic reduction *)

  - (* prev 2*)
    inversion Hcontra; subst; auto.
    admit. (* contradiction: cyclic reduction *)

  - (* nsat_exp*)
    inversion Hcontra; subst.
    link_unique_auto.
    unique_loo_exp.
    eval_rewrite; crush.

  - admit.

  - (* nsat_name *)
    inversion Hcontra;
      subst;
      crush.

  - admit.

  - (* nsat_class1 *)
    inversion Hcontra; subst.
    match goal with
    | [Ha : mapp ?σ ?α = Some _,
            Hb : mapp ?σ ?α = Some _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    auto.

  - (* nsat_class2 *)
    inversion Hcontra; subst;
      crush.

  - (* nsat_all *)
    inversion Hcontra; subst.
    match goal with
    | [Ha : forall x, has_type ?m x ?T  -> _,
         Hb : has_type ?m ?x ?T |- _] =>
      specialize (Ha x Hb)
    end.
    auto.

  - (* nsat_access1 *)
    inversion Hcontra; subst; auto.
    + match goal with
      | [Ha : forall o' f' α', ?m ?α1 = Some o' ->
                          flds o' f' = Some (v_addr α') ->
                          ?α2 <> α',
           Hb : flds ?o ?f = Some _ |- _] =>
        specialize (Ha o f α2);
          repeat auto_specialize
      end.
      auto.
    + specialize (n1 x);
        repeat auto_specialize.
      assert (Htmp : (χ, ϕ::ψ) = (χ, ϕ::ψ));
        [auto|].
      specialize (n1 ψ ϕ χ s Htmp);
        auto_specialize;
        auto.

  - (* nsat_call1 *)
    inversion Hcontra; subst; auto.
      match goal with
      | [H : mapp ?σ ?x <> Some ?v,
             Hint : ⌊?x⌋ ?σ ≜ ?v  |- _] =>
        contradiction H;
        inversion Hint; subst
      end.
      auto.

  - (* nsat_call2 *)
    inversion Hcontra; subst;
      unfold snd in *;
      simpl_crush.
      match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst
      end.
      match goal with
      | [H : mapp ?σ ?x <> Some ?v,
             Hint : ⌊?x⌋ ?σ ≜ ?v  |- _] =>
        contradiction H;
        inversion Hint; subst
      end.
      auto.

  - (* nsat_call3 *)
    inversion Hcontra; subst;
      unfold snd in *;
      simpl_crush.
      match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst
      end.
      contradiction n; auto.

  - (* nsat_extrn1 *)
    inversion Hcontra; subst.
    crush.

  - (* nsat_extrn2 *)
    inversion Hcontra; subst.
    crush.

  - (* nsat_intrn1 *)
    inversion Hcontra; subst.
    crush.

  - (* nsat_intrn2 *)
    inversion Hcontra; subst.
    crush.

  - (* nsat_next *)
    inversion Hcontra; subst.
    unique_reduction_auto.
    auto.

  - (* nsat_will *)
    inversion Hcontra; subst.
    match goal with
    | [H : forall σ'', ?M1 ⦂ ?M2 ⦿ ?σ ⌈⤳⋆⌉ σ'' -> ~ _,
         Ha : ?M1 ⦂ ?M2 ⦿ ?σ ⌈⤳⋆⌉ ?σ' |- _] =>
      specialize (H σ')
    end;
      auto_specialize;
      auto.
    

  - (* nsat_prev 1*)
    inversion Hcontra; subst.
    + assert (Heq : σ'0 = σ');
        [eapply pair_reductions_unique_prev; eauto|subst; auto].
    + admit. (* contradiction: cyclic reduction *)

  - (* nsat_prev 2 *)
    inversion Hcontra; subst; auto.
    admit. (* contradiction: cyclic reduction *)
    

  - (* nsat_was *)
    inversion Hcontra; subst; auto.
    specialize (H σ');
      repeat auto_specialize;
      auto.

Admitted.

Theorem sat_implies_not_nsat :
  (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                   ~ M1 ⦂ M2 ◎ σ0 … σ ⊭ A).
Proof.
  destruct sat_implies_not_nsat_mutind; crush.
Qed.

Theorem nsat_implies_not_sat :
  (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                   ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ A).
Proof.
  destruct sat_implies_not_nsat_mutind; crush.
Qed.

(** Lemma 5: Classical (1) *)
(** Yet to be proven *)
Lemma sat_excluded_middle :
  forall M1 M2 σ0 σ A, (M1 ⦂ M2 ◎ σ0 … σ ⊨ A) \/ (M1 ⦂ M2 ◎ σ0 … σ ⊭ A).
Proof.
Admitted.

Theorem not_sat_implies_nsat :
  (forall M1 M2 σ0 σ A, ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A).
Proof.
  intros.
  destruct (sat_excluded_middle M1 M2 σ0 σ A);
    crush.
Qed.


(** Lemma 5: Classical (5) *)
Lemma arr_true :
  forall M1 M2 σ0 σ A1 A2,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ A2.
Proof.
  intros M1 M2 σ0 σ A1 A2 Hsat;
    inversion Hsat;
    subst;
    intros;
    auto.

  apply sat_implies_not_nsat_mutind in H;
    crush.
Qed.

Lemma arr_false :
  forall M1 M2 σ0 σ A1 A2,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ A1.
Proof.
  intros M1 M2 σ0 σ A1 A2 Hsat;
    inversion Hsat;
    subst;
    intros;
    auto.

  apply sat_implies_not_nsat_mutind in H;
    crush.
Qed.

Lemma arr_prop1 :
  forall M1 M2 σ0 σ A1 A2,
    (M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ0 … σ ⊨ A2) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2).
Proof.
  intros.
  destruct sat_excluded_middle
    with (M1:=M1)(M2:=M2)
         (σ0:=σ0)(σ:=σ)(A:=A1);
    auto with chainmail_db.
Qed.

Lemma arr_prop2 :
  forall M1 M2 σ0 σ A1 A2,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2) ->
    (M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ0 … σ ⊨ A2).
Proof.
  intros.
  eapply arr_true; eauto.
Qed.

Lemma arr_prop :
  forall M1 M2 σ0 σ A1 A2,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2) <->
    (M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ0 … σ ⊨ A2).
Proof.
  intros;
    split;
    [apply arr_prop2|apply arr_prop1].
Qed.

Lemma all_prop :
  forall M1 M2 σ0 σ T A,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀[x⦂ T]∙A) <->
    (forall x, has_type σ x T ->
          M1 ⦂ M2 ◎ σ0 … σ ⊨ ([x /s 0]A)).
Proof.
  intros; split; eauto with chainmail_db; intros.
  inversion H;
    subst;
    eauto.
Qed.

Lemma ex_prop :
  forall M1 M2 σ0 σ T A,
    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ T]∙ A)) <->
    (exists x, has_type σ x T /\
          M1 ⦂ M2 ◎ σ0 … σ ⊨ ([x /s 0] A)).
Proof.
  intros; split; eauto with chainmail_db; intros.
  inversion H;
    subst.
  - eexists; eauto.
  - repeat destruct_exists_loo;
      andDestruct;
      eauto with chainmail_db.
Qed.

(** Lemma 5: Classical (2) *)
Lemma and_iff :
  forall M1 M2 σ0 σ A1 A2, (M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)) <->
                      (M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 /\ M1 ⦂ M2 ◎ σ0 … σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto with chainmail_db.
Qed.

(** Lemma 5: Classical (3) *)
Lemma or_iff :
  forall M1 M2 σ0 σ A1 A2, (M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)) <->
                      (M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 \/ M1 ⦂ M2 ◎ σ0 … σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto with chainmail_db.
Qed.

Lemma negate_elim_sat :
  (forall A M1 M2 σ0 σ, M1 ⦂ M2 ◎ σ0 … σ ⊨ (¬ ¬ A) ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A).
Proof.
  intros;
    auto.
  inversion H;
    subst.
  inversion H5;
    auto.
Qed.

Lemma negate_elim_nsat :
  (forall A M1 M2 σ0 σ, M1 ⦂ M2 ◎ σ0 … σ ⊭ (¬ ¬ A) ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A).
Proof.
  intros;
    auto.
  inversion H;
    subst.
  inversion H5;
    auto.
Qed.

Lemma negate_intro_sat :
  (forall A M1 M2 σ0 σ, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ (¬ ¬ A)).
Proof.
  intros;
    auto with chainmail_db.
Qed.

Lemma negate_intro_nsat :
  (forall A M1 M2 σ0 σ, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (¬ ¬ A)).
Proof.
  intros;
    auto with chainmail_db.
Qed.

Lemma will_arr :
  forall M1 M2 σ0 σ A1 A2,
    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will(A1 ⟶ A2 ∧ A1) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will(A2).
Proof.
  intros.
  inversion H;
    subst.
  inversion H6;
    subst;
    eauto.
  apply sat_will
    with (σ':=σ');
    auto.
  eapply arr_true;
    eauto.
Qed.

Lemma sat_and_nsat_entails_false :
  forall {A}, entails (A ∧ ¬ A) (a_expr (ex_val v_false)).
Proof.
  intros.
  apply ent;
    intros.

  apply and_iff in H;
    andDestruct.
  inversion Hb;
    subst.

  apply sat_implies_not_nsat in Ha;
    crush.
Qed.

Hint Resolve sat_and_nsat_entails_false : chainmail_db.

Lemma false_entails_sat_and_nsat :
  forall {A}, entails (a_expr (ex_false)) (A ∧ ¬ A).
Proof.
  intros.
  apply ent;
    intros.

  inversion H;
    subst.
  inversion H1;
    subst.
  inversion H7.
Qed.

Hint Resolve false_entails_sat_and_nsat : chainmail_db.

(** Lemma 6: (1) *)
Lemma sat_and_nsat_equiv_false :
  forall {A}, equiv_a (A ∧ ¬ A) (a_expr (ex_false)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Lemma or_commutative' :
  forall {A1 A2}, entails (A1 ∨ A2) (A2 ∨ A1).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    eauto with chainmail_db.
Qed.

Hint Resolve or_commutative' : chainmail_db.

(** Lemma 6: (4) *)
Lemma or_commutative :
  forall {A1 A2}, equiv_a (A1 ∨ A2) (A2 ∨ A1).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve or_commutative : chainmail_db.

Lemma and_commutative' :
  forall {A1 A2}, entails (A1 ∧ A2) (A2 ∧ A1).
Proof.
  intros;
    eapply ent;
    intros;
    eauto.
  inversion H;
    eauto with chainmail_db.
Qed.

Hint Resolve and_commutative' : chainmail_db.

(** Lemma 6: (3) *)
Lemma and_commutative :
  forall {A1 A2}, equiv_a (A1 ∧ A2) (A2 ∧ A1).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve and_commutative : chainmail_db.

Lemma or_associative_1:
  forall {A1 A2 A3}, entails ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve or_associative_1 : chainmail_db.

Lemma or_associative_2:
  forall {A1 A2 A3}, entails (A1 ∨ (A2 ∨ A3)) ((A1 ∨ A2) ∨ A3).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve or_associative_2 : chainmail_db.

(** Lemma 6: (5) *)
Lemma or_associative:
  forall {A1 A2 A3}, equiv_a ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve or_associative : chainmail_db.

Lemma and_distributive_1:
  forall {A1 A2 A3}, entails ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H6;
    eauto with chainmail_db.
Qed.

Hint Resolve and_distributive_1 : chainmail_db.

Lemma and_distributive_2:
  forall {A1 A2 A3}, entails ((A1 ∧ A3) ∨ (A2 ∧ A3)) ((A1 ∨ A2) ∧ A3).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve and_distributive_2 : chainmail_db.

(** Lemma 6: (6) *)
Lemma and_distributive:
  forall {A1 A2 A3}, equiv_a ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve and_distributive : chainmail_db.

Lemma or_distributive_1:
  forall {A1 A2 A3}, entails ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto with chainmail_db;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve or_distributive_1 : chainmail_db.

Lemma or_distributive_2:
  forall {A1 A2 A3}, entails ((A1 ∨ A3) ∧ (A2 ∨ A3)) ((A1 ∧ A2) ∨ A3).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H6;
    inversion H7;
    eauto with chainmail_db.
Qed.

Hint Resolve or_distributive_2 : chainmail_db.

(** Lemma 6: (7) *)
Lemma or_distributive:
  forall {A1 A2 A3}, equiv_a ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve or_distributive : chainmail_db.

Lemma neg_distributive_and_1:
  forall {A1 A2}, entails (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_and_1 : chainmail_db.

Lemma neg_distributive_and_2:
  forall {A1 A2}, entails (¬A1 ∨ ¬A2) (¬(A1 ∧ A2)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_and_2 : chainmail_db.

(** Lemma 6: (8) *)
Lemma neg_distributive_and:
  forall {A1 A2}, equiv_a (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_and : chainmail_db.

Lemma neg_distributive_or_1:
  forall {A1 A2}, entails (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H5;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_or_1 : chainmail_db.

Lemma neg_distributive_or_2:
  forall {A1 A2}, entails (¬A1 ∧ ¬A2) (¬(A1 ∨ A2)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H6;
    inversion H7;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_or_2 : chainmail_db.

(** Lemma 6: (9) *)
Lemma neg_distributive_or:
  forall {A1 A2}, equiv_a (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve neg_distributive_or : chainmail_db.

Lemma not_ex_all_not_1 : 
  forall {T A}, entails (¬(∃[x⦂ T]∙A)) (∀[x⦂ T]∙¬A).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.
  inversion H5;
    subst.

  apply sat_all;
    intros.
  apply sat_not.
  eapply H6; eauto with chainmail_db.
Qed.

Hint Resolve not_ex_all_not_1 : chainmail_db.

Lemma not_ex_all_not_2 : 
  forall {A T}, entails (∀[x⦂ T]∙¬A) (¬(∃[x⦂ T]∙A)).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.

  apply sat_not.
  apply nsat_ex;
    intros.
  eapply H5 in H0;
    eauto with chainmail_db.

  inversion H0;
    eauto with chainmail_db.
Qed.

Hint Resolve not_ex_all_not_2 : chainmail_db.

(** Lemma 6: (10) *)
Lemma not_ex_all_not : 
  forall {A T}, equiv_a (¬(∃[x⦂ T]∙A)) (∀[x⦂ T]∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_ex_all_not : chainmail_db.

Lemma not_ex_all :
  forall {A T}, entails (¬ ∃[x⦂ T]∙ (¬ A)) (∀[x⦂ T]∙A).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  inversion H5;
    subst.
  apply sat_all;
    intros.
  specialize (H6 x);
    auto_specialize.
  inversion H6;
    subst.
  auto.
Qed.

Lemma ex_not_all :
  forall {A T}, entails (∃[x⦂ T]∙ A) (¬ ∀[x⦂ T]∙ (¬ A)).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  apply sat_not.
  apply nsat_all with (x:=x);
    auto with chainmail_db;
    sbst_simpl.
  simpl in *.
  apply nsat_not;
    auto.
Qed.

Lemma not_all_ex_not_1 : 
  forall {A T}, entails (¬(∀[x⦂ T]∙A)) (∃[x⦂ T]∙¬A).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.
  inversion H5;
    subst.

  apply sat_ex with (x:=x);
    auto with chainmail_db;
    sbst_simpl.
  
  apply sat_not; auto.
Qed.

Hint Resolve not_all_ex_not_1 : chainmail_db.

Lemma not_all_ex_not_2 : 
  forall {A T}, entails (∃[x⦂ T]∙¬A) (¬(∀[x⦂ T]∙A)).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.

  apply sat_not.
  sbst_simpl.
  apply nsat_all with (x:=x);
    auto with chainmail_db;
    sbst_simpl.
  inversion H7; subst; auto.
Qed.

Hint Resolve not_all_ex_not_2 : chainmail_db.

Lemma not_all_ex_not : 
  forall {A T}, equiv_a (¬(∀[x⦂ T]∙A)) (∃[x⦂ T]∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_all_ex_not : chainmail_db.

Lemma not_all_ex :
  forall {A T}, entails (¬ ∀[x⦂ T]∙ (¬ A)) (∃[x⦂ T]∙A).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  inversion H5;
    subst.
  simpl in *.
  eapply sat_ex;
    eauto.
  simpl in *.
  inversion H8;
    subst.
  auto.
Qed.

Lemma all_not_ex :
  forall {A T}, entails (∀[x⦂ T]∙ A) (¬ ∃[x⦂ T]∙ (¬ A)).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  apply sat_not.
  apply nsat_ex; intros.
  simpl in *;
    apply nsat_not.
  eapply H5;
    eauto.
Qed.

Lemma entails_implies :
  forall {M1 M2 σ0 σ A1 A2}, entails A1 A2 ->
                        M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                        M1 ⦂ M2 ◎ σ0 … σ ⊨ A2.
Proof.
  intros.
  inversion H;
    auto.
Qed.

Hint Resolve entails_implies : chainmail_db.
(*Hint Rewrite entails_implies : chainmail_db.*)

Ltac a_contradiction :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (¬ _)] =>
    apply sat_not;
    apply not_sat_implies_nsat;
    let Hcontra := fresh "Hcontra" in
    intro Hcontra
  | [|- _ ⦂ _ ◎ _ … _ ⊭ _] =>
    apply not_sat_implies_nsat;
    let Hcontra := fresh "Hcontra" in
    intro Hcontra
  end.

Ltac a_contradiction_neg :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊨ _] =>
    apply negate_elim_sat;
    a_contradiction
  end.

Lemma entails_implies_neg :
  forall {M1 M2 σ0 σ A1 A2}, entails A1 A2 ->
                        M1 ⦂ M2 ◎ σ0 … σ ⊨ (¬ A2) ->
                        M1 ⦂ M2 ◎ σ0 … σ ⊨ ¬ A1.
Proof.
  intros.
  a_contradiction.
  apply (entails_implies H) in Hcontra.
  apply sat_implies_not_nsat in Hcontra.
  inversion H0;
    auto.
Qed.

Lemma a_name_unique :
  forall {M1 M2 σ0 σ a1 x}, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_name a1 x) ->
                       forall {a2}, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_name a2 x) ->
                               a1 = a2.
Proof.
  intros.
  repeat match goal with
         | [H : _ ⦂  _ ◎ _ … _ ⊨ a_name _ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  crush.
Qed.

Lemma is_private_a_private :
  forall {a1 a2 x}, entails (is_private a1 x ∧ a_name a2 x)
                       (a_private a1 a2).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  unfold is_private in *.
  assert (exists α2, a2 = a_ α2);
    [inversion H7;
     subst;
     eauto
    |destruct_exists_loo; subst].
  assert (exists α1, a1 = a_ α1);
    [|destruct_exists_loo; subst; simpl in *].

  - destruct a1; simpl in *.
    + inversion H6;
        subst.
      simpl in *.
      inversion H9;
        subst.
      inversion H11;
        subst.
      destruct x0;
        crush.
    + inversion H6;
        subst;
        simpl in *.
      inversion H9;
        subst.
      destruct v;
        simpl in *;
        eauto;
        try solve [inversion H11].

  - inversion H6;
      subst;
      simpl in *.
    inversion H9;
      subst;
      auto.
    destruct x0;
      [|inversion H10|inversion H10].
    inversion H10;
      subst.
    apply a_name_unique with (a2:=a_ α1) in H7;
      crush.
Qed.

Lemma a_private_is_private :
  forall {a1 a2 x}, entails (a_private a1 a2 ∧ a_name a2 x)
                       (is_private a1 x).
Proof.
  intros.
  apply ent;
    intros.
  inversion H;
    subst.
  unfold is_private in *.
  
  assert (exists α2, a2 = a_ α2);
    [inversion H7;
     subst;
     eauto
    |destruct_exists_loo; subst].
  assert (exists α1, a1 = a_ α1);
    [|destruct_exists_loo; subst; simpl in *].

  - destruct a1.
    + simpl in *.
      inversion H6;
        subst.
    + inversion H6;
        eauto.

  - inversion H7;
      subst.
    apply sat_ex with (x:=(ax_val (v_ α)));
      eauto with chainmail_db;
      simpl.
    apply sat_and;
      auto.
Qed.

Lemma has_type_val :
  forall {σ x}, has_type σ x a_Val ->
           exists v, x = ax_val v.
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end.
  eauto.
Qed.

Lemma has_type_obj :
  forall {σ x}, has_type σ x a_Obj ->
           exists α o, x = (ax_val (v_ α)) /\
                  ⟦ α ↦ o ⟧ ∈ σ.
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end.
  eauto.
Qed.

Lemma has_type_bool :
  forall {σ x}, has_type σ x a_Bool ->
           exists v, x = (ax_val v) /\
                (v = v_true \/
                 v = v_false).
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end;
  eauto.
Qed.

Lemma has_type_int :
  forall {σ x}, has_type σ x a_Int ->
           exists i, x = (ax_val (v_int i)).
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end;
  eauto.
Qed.

Lemma has_type_mth :
  forall {σ x}, has_type σ x a_Mth ->
           exists m, x = (ax_mth m).
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end;
  eauto.
Qed.

Lemma has_type_set :
  forall {σ x}, has_type σ x a_Set ->
           exists Σ, x = (ax_set Σ).
Proof.
  intros.
  match goal with
  | [H : has_type _ _ _ |- _ ] =>
    inversion H
  end;
  eauto.
Qed.

Ltac has_type_decompose :=
  match goal with
  | [H : has_type _ _ a_Val |- _] =>
    apply has_type_val in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_Obj |- _] =>
    apply has_type_obj in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_Bool |- _] =>
    apply has_type_bool in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_Int |- _] =>
    apply has_type_int in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_mth |- _] =>
    apply has_type_mth in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_set |- _] =>
    apply has_type_set in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  end.

Ltac sat_destruct :=
  match goal with
  | [Hand : _ ⦂ _ ◎ _ … _ ⊨ (_ ∧ _) |- _] => apply and_iff in Hand;
                                           destruct Hand
  end.

Ltac a_intro :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∀[x⦂ _]∙ _)] => apply sat_all; intros; simpl in *
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ⟶ _)] => apply arr_prop1; intros; simpl in *
  end.

Ltac a_intros :=
  repeat a_intro.

Ltac a_prop :=
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ∧ _) |- _] => apply -> and_iff in H;
                                           destruct H
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ∨ _) |- _] => apply -> or_iff in H
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ⟶ _) |- _] => rewrite -> arr_prop in H
         | [H : context[_ ⦂ _ ◎ _ … _ ⊨ (_ ⟶ _)] |- _] => rewrite -> arr_prop in H
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (∀[x⦂ _ ]∙_) |- _] => rewrite all_prop in H; sbst_simpl
         | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ∧ _)] => apply sat_and
         | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ∨ _)] => apply <- or_iff

         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ (_ ∧ _)) |- _ ] =>
           eapply entails_implies in H;
           [|apply neg_distributive_and]
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ (_ ∨ _)) |- _ ] =>
           eapply entails_implies in H;
           [|apply neg_distributive_or]

         | [|- _ ⦂ _ ◎ _ … _ ⊨ (¬ (_ ∧ _))] =>
           eapply entails_implies;
           [|apply neg_distributive_and_2]
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ (_ ∨ _)) |- _ ] =>
           eapply entails_implies;
           [|apply neg_distributive_or_2]

         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ (∃[x⦂ _ ]∙ _)) |- _ ] =>
           eapply entails_implies in H;
           [|apply not_ex_all_not]
         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ (∀[x⦂ _ ]∙ _)) |- _ ] =>
           eapply entails_implies in H;
           [|apply not_all_ex_not]

         | [|- _ ⦂ _ ◎ _ … _ ⊨ (¬ (∃[x⦂ _ ]∙ _)) ] =>
           eapply entails_implies;
           [|apply not_ex_all_not_2]
         | [|- _ ⦂ _ ◎ _ … _ ⊨ (¬ (∀[x⦂ _ ]∙ _)) ] =>
           eapply entails_implies;
           [|apply not_all_ex_not_2]


         | [H : entails ?A1 ?A2,
                Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ?A1 |- _] =>
           notHyp (M1 ⦂ M2 ◎ σ0 … σ  ⊨ A2);
           let H' := fresh in 
           assert (H' : M1 ⦂ M2 ◎ σ0 … σ ⊨ A2);
           [apply (entails_implies M1 M2 σ0 σ A1 Ha A2 H); eauto|]
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ?A,
                 Hb : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ¬ ?A |- _] =>
           apply sat_implies_not_nsat in Ha;
           auto
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ?A,
                 Hb : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊭ ?A |- _] =>
           apply sat_implies_not_nsat in Ha;
           auto
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ¬ ?A,
                 Hb : ~ ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊭ ?A |- _] =>
           inversion Ha; subst; crush

         | [H : _ ⦂ _ ◎ _ … _ ⊨ (¬ ¬ _) |- _] =>
           apply negate_elim_sat in H
         | [H : _ ⦂ _ ◎ _ … _ ⊭ (¬ ¬ _) |- _] =>
           apply negate_elim_nsat in H

         | [|- _ ⦂ _ ◎ _ … _ ⊨ (¬ ¬ _) ] =>
           apply negate_intro_sat
         | [|- _ ⦂ _ ◎ _ … _ ⊭ (¬ ¬ _) ] =>
           apply negate_intro_nsat

         | [H : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_private ?a1 ?a2 ∧ a_name ?a2 ?x)
            |- ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ is_private ?a1 ?x] =>
           apply (entails_implies (@a_private_is_private a1 a2 x))
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_private ?a1 ?a2),
                 Hb : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_name ?a2 ?x)
            |- ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (is_private ?a1 ?x)] =>
           apply (entails_implies (@a_private_is_private a1 a2 x))
         end;
  repeat has_type_decompose.

Ltac a_destruct H :=
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ _ ]∙_) |- _] =>
    apply -> ex_prop in H;
    destruct_exists_loo
  | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ∨ _) |- _] =>
    apply -> or_iff in H;
    destruct H
  end.

(*Lemma and_forall_x_entails_1 :
  forall A1 A2, entails (A1 ∧ (∀x∙A2))
                   (∀x∙(A1 ↑ 0 ∧ A2)).
Proof.
  intros.
  apply ent;
    intros.

  apply and_iff in H;
    andDestruct.
  rewrite all_x_prop; intros.
  repeat a_intros; a_prop.

  - admit. (* sbst n (raise n) A = A, and weakening with fresh var .... is this going to be very difficult ...  *)

  - admit. (* construct inversion lemmas for fresh_x and fresh_x_σ *)
  
Admitted.

Lemma and_forall_x_entails_2 :
  forall A1 A2, entails (∀x∙(A1 ↑ 0 ∧ A2))
                   (A1 ∧ (∀x∙A2)).
Proof.
  intros.
  apply ent;
    intros.

  repeat (a_intros; a_prop).
  (* variable map may not be empty because the vMap must always provide a mapping for `this` *)

  - admit. (* create fresh variable *)

  - admit.
  
Admitted.

Hint Resolve and_forall_x_entails_1 and_forall_x_entails_2 : chainmail_db.

Lemma and_forall_x_equiv :
  forall A1 A2, equiv_a (A1 ∧ (∀x∙A2))
                   (∀x∙(A1 ↑ 0 ∧ A2)).
Proof.
  split; eauto with chainmail_db.
Qed.

Hint Resolve and_forall_x_equiv : chainmail_db.

Lemma and_exists_x_entails_1 :
  forall A1 A2, entails (A1 ∧ (∃x∙A2))
                   (∃x∙(A1 ↑ 0 ∧ A2)).
Proof.
  intros.
  apply ent;
    intros.

  apply and_iff in H;
    andDestruct.  rewrite ex_x_prop; intros.
  inversion Hb; subst.
  eexists; eexists; eexists; repeat split;
    eauto with chainmail_db;
    repeat sbst_simpl;
    repeat (a_intros;
            a_prop).

  - admit. (* introduce new fresh variable, show equivalence *)

  - admit. (* subst on raise and weakening *)

  - admit. (* follows directly from introducing an alternative fresh variable *)
  
Admitted.

Lemma and_exists_x_entails_2 :
  forall A1 A2, entails (∃x∙(A1 ↑ 0 ∧ A2))
                   (A1 ∧ (∃x∙A2)).
Proof.
  intros.
  apply ent;
    intros.

  repeat (a_intros; a_prop).

  - apply ex_x_prop in H;
      repeat destruct_exists_loo;
      andDestruct;
      repeat sbst_simpl;
      repeat (a_intros; a_prop). (* x1 is fresh in A, and subst/raise with weakening gives the desired result *)
    admit.

  - apply ex_x_prop in H;
      repeat destruct_exists_loo;
      andDestruct;
      repeat sbst_simpl;
      repeat (a_intros; a_prop).
    eapply sat_ex_x; eauto. (* fresh inversion lemmas *)
    admit.
  
Admitted.

Hint Resolve and_exists_x_entails_1 and_exists_x_entails_2 : chainmail_db.

Lemma or_forall_x_entails_1 :
  forall A1 A2, entails (A1 ∨ (∀x∙A2))
                   (∀x∙(A1 ↑ 0 ∨ A2)).
Proof.
  intros.
  apply ent;
    intros.

  apply or_iff in H;
    andDestruct.
  rewrite all_x_prop; intros.
  repeat sbst_simpl.
  repeat a_intros; a_prop.
  match goal with
  | [H : _ \/ _ |- _] => destruct H
  end.

  - left. admit. (* sbst n (raise n) A = A, and weakening with fresh var .... is this going to be very difficult???? ...  *)

  - right. admit. (* construct inversion lemmas for fresh_x and fresh_x_σ *)
  
Admitted.

Lemma or_forall_x_entails_2 :
  forall A1 A2, entails (∀x∙(A1 ↑ 0 ∨ A2))
                   (A1 ∨ (∀x∙A2)).
Proof.
  intros.
  apply ent;
    intros.

  repeat (a_intros; a_prop).

  - admit. (* create fresh variable *)
  
Admitted.

Hint Resolve or_forall_x_entails_1 or_forall_x_entails_2 : chainmail_db.

Lemma or_forall_x_equiv :
  forall A1 A2, equiv_a (A1 ∨ (∀x∙A2))
                   (∀x∙(A1 ↑ 0 ∨ A2)).
Proof.
  split; eauto with chainmail_db.
Qed.

Hint Resolve or_forall_x_equiv : chainmail_db.

Lemma or_exists_x_entails_1 :
  forall A1 A2, entails (A1 ∨ (∃x∙A2))
                   (∃x∙(A1 ↑ 0 ∨ A2)).
Proof.
  intros.
  apply ent;
    intros.

  admit.
  
Admitted.

Lemma or_exists_x_entails_2 :
  forall A1 A2, entails (∃x∙(A1 ↑ 0 ∨ A2))
                   (A1 ∨ (∃x∙A2)).
Proof.
  intros.
  apply ent;
    intros.

  admit.
  
Admitted.

Hint Resolve or_exists_x_entails_1 or_exists_x_entails_2 : chainmail_db.

Lemma or_exists_x_equiv :
  forall A1 A2, equiv_a (A1 ∨ (∃x∙A2))
                   (∃x∙(A1 ↑ 0 ∨ A2)).
Proof.
  split; eauto with chainmail_db.
Qed.

Hint Resolve or_exists_x_equiv : chainmail_db.

Lemma arr_cnf_1 :
  forall A1 A2, entails (A1 ⇒ A2)
                   ((A1 ∧ A2) ∨ (¬ A1)).
Proof.
  intros.
  apply ent; intros.
  repeat (a_intros; a_prop).
  destruct sat_excluded_middle
    with (M1:=M1)(M2:=M2)
         (σ:=(χ, ϕ::ψ))(A:=A1);
    eauto with chainmail_db.
Qed.

Lemma arr_cnf_2 :
  forall A1 A2, entails ((A1 ∧ A2) ∨ (¬ A1))
                   (A1 ⇒ A2).
Proof.
  intros.
  apply ent; intros.
  repeat (a_intros; a_prop).
  destruct H; repeat a_prop; auto.
Qed.

Hint Resolve arr_cnf_1 arr_cnf_2 : chainmail_db.

Lemma arr_cnf_equiv :
  forall A1 A2, equiv_a ((A1 ∧ A2) ∨ (¬ A1))
                   (A1 ⇒ A2).
Proof.
  split; auto with chainmail_db.
Qed.

Hint Resolve arr_cnf_equiv : chainmail_db.

Lemma and_entails :
  forall A1 A2, entails A1 A2 ->
           forall A, entails (A1 ∧ A) (A2 ∧ A).
Proof.
  intros.
  apply ent; intros;
    repeat a_prop;
    auto with chainmail_db.
Qed.

Lemma or_entails :
  forall A1 A2, entails A1 A2 ->
           forall A, entails (A1 ∨ A) (A2 ∨ A).
Proof.
  intros.
  apply ent; intros;
    repeat a_prop;
    match goal with
    | [H : _ \/ _ |- _] => destruct H
    end;
    repeat a_prop;
    auto with chainmail_db.
Qed.

Lemma neg_entails :
  forall A1 A2, equiv_a A1 A2 ->
           entails (¬ A1) (¬ A2).
Proof.
  intros.
  apply ent; intros;
    repeat a_prop;
    auto with chainmail_db.
  destruct (sat_excluded_middle M1 M2 (χ, ϕ::ψ) A2);
    auto with chainmail_db.

  - unfold equiv_a in *;
      andDestruct.
    match goal with
    | [Ha : entails _ _,
            Hb : entails _ _ |- _] => inversion Ha; inversion Hb; subst
    end.
    apply H4 in H1.
    apply sat_implies_not_nsat in H1.
    inversion H0; crush.
Qed.

(*Ltac a_exists y' v' :=
  match goal with
  | [|- _ ⦂ _ ◎ _ ⊨ (∃x∙_)] => eapply sat_ex_x with (y:=y')(v:=v')
  end.*)

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.

Ltac a_exists_base y' v' z' :=
  match type of z' with
  | ltac_No_arg =>
    match type of v' with
    | ltac_No_arg =>
      match goal with
      | [|- _ ⦂ _ ◎ _ ⊨ (∃x∙_)] => eapply sat_ex_x with (y:=y')
      end
    | _ => match goal with
          | [|- _ ⦂ _ ◎ _ ⊨ (∃x∙_)] => eapply sat_ex_x with (y:=y')(v:=v')
          end
    end
  | _ => match goal with
        | [|- _ ⦂ _ ◎ _ ⊨ (∃x∙_)] => eapply sat_ex_x with (y:=y')(v:=v')(z:=z')
        end
  end.

Tactic Notation "a_exists" constr(x) :=
  a_exists_base x ltac_no_arg ltac_no_arg.
Tactic Notation "a_exists" constr(x) constr(y) :=
  a_exists_base x y ltac_no_arg.
Tactic Notation "a_exists" constr(x) constr(y) constr(z) :=
  a_exists_base x y z.

Lemma a_contradiction_1 :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ A -> False) ->
               (M1 ⦂ M2 ◎ σ ⊨ ¬ A).
Proof.
  intros.
  destruct (sat_excluded_middle M1 M2 σ A);
    auto with chainmail_db;
    crush.
Qed.

Lemma a_contradiction_2 :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ A -> False) ->
               (M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
  intros.
  destruct (sat_excluded_middle M1 M2 σ A);
    auto with chainmail_db;
    crush.
Qed.

Lemma a_contradiction_3 :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ (¬ A) -> False) ->
               (M1 ⦂ M2 ◎ σ ⊨ A).
Proof.
  intros.
  destruct (sat_excluded_middle M1 M2 σ A);
    auto with chainmail_db;
    crush.
Qed.

Lemma not_implies_nsat :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ (¬ A) ->
               M1 ⦂ M2 ◎ σ ⊭ A.
Proof.
  intros.
  inversion H;
    subst;
    auto.
Qed.

Ltac a_contra_base H :=
  match type of H with
  | ltac_No_arg => match goal with
                  | [|- _ ⦂ _ ◎ _ ⊨ ¬ _] => apply a_contradiction_1; intros
                  | [|- _ ⦂ _ ◎ _ ⊭ _] => apply a_contradiction_2; intros
                  | [|- _ ⦂ _ ◎ _ ⊨ _] => apply a_contradiction_3; intros
                  end
  | _ => match goal with
        | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ¬ ?A |- _] =>
          apply not_implies_nsat, nsat_implies_not_sat in H;
          contradiction H
        | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊭ ?A |- _] =>
          apply nsat_implies_not_sat in H;
          contradiction H
        end
  end.

Tactic Notation "a_contra" :=
  a_contra_base ltac_no_arg.
Tactic Notation "a_contra" constr(H) :=
  a_contra_base H.

Lemma next_neg :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ (¬ a_next A) ->
               forall χ ϕ ψ, σ = (χ, ϕ::ψ) ->
                        (forall σ' σ'', M1 ⦂ M2 ⦿ (χ, ϕ::nil) ⤳ σ' ->
                                   σ ◁ σ' ≜ σ'' ->
                                   M1 ⦂ M2 ◎ σ'' ⊨ (¬ A)).
Proof.
  intros.
  a_contra.
  a_contra H; eauto with chainmail_db.
Qed.

Lemma will_neg :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ (¬ a_will A) ->
               forall χ ϕ ψ, σ = (χ, ϕ::ψ) ->
                        (forall σ' σ'', M1 ⦂ M2 ⦿ (χ, ϕ::nil) ⤳⋆ σ' ->
                                   σ ◁ σ' ≜ σ'' ->
                                   M1 ⦂ M2 ◎ σ'' ⊨ (¬ A)).
Proof.
  intros.
  a_contra.
  match goal with
  | [H : _ ⦂ _ ◎ _ ⊨ (¬ a_will _) |- _] => inversion H; subst
  end.
  a_contra H; eauto with chainmail_db.
Qed.

Lemma next_disj_1 :
  forall A1 A2, entails (a_next (A1 ∨ A2))
                   ((a_next A1) ∨ (a_next A2)).
Proof.
  intros.
  apply ent;
    intros.
  destruct (sat_excluded_middle M1 M2 (χ, ϕ::ψ) (a_next A1));
    auto with chainmail_db.
  inversion H; inversion H0; subst.
  repeat match goal with
         | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
         end.
  apply pair_reduction_unique with (σ1:=σ'0) in H3; auto; subst.
  a_prop.
  destruct H8.

  - left; eauto with chainmail_db.
  - right; eauto with chainmail_db.

Qed.

Lemma next_disj_2 :
  forall A1 A2, entails ((a_next A1) ∨ (a_next A2))
                   (a_next (A1 ∨ A2)).
Proof.
  intros.
  apply ent;
    intros.
  a_prop.
  destruct H.
  - inversion H; subst.
    match goal with
    | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
    end.
    apply sat_next with (ϕ:=ϕ0)(ψ:=ψ0)(χ:=χ0)(σ':=σ')(σ'':=σ''); auto with chainmail_db.
  - inversion H; subst.
    match goal with
    | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
    end.
    apply sat_next with (ϕ:=ϕ0)(ψ:=ψ0)(χ:=χ0)(σ':=σ')(σ'':=σ''); auto with chainmail_db.
Qed.

Hint Resolve next_disj_1 next_disj_2 : chainmail_db.

Lemma next_disj_equiv :
  forall A1 A2, equiv_a ((a_next A1) ∨ (a_next A2))
                   (a_next (A1 ∨ A2)).
Proof.
  intros; split; auto with chainmail_db.
Qed.

Hint Resolve next_disj_equiv : chainmail_db.

Lemma will_not_disj :
  forall A1 A2, entails (a_will (A1 ∨ A2) ∧ (¬ (a_will A1)))
                   (a_will A2).
Proof.
  intros;
    apply ent;
    intros.

  a_prop.
  inversion H; subst.
  match goal with
  | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
  end.
  a_prop.
  destruct H8; eauto with chainmail_db.
  a_contra H0; eauto with chainmail_db.
Qed.

Hint Resolve will_not_disj : chainmail_db.

Lemma will_disj_1 :
  forall A1 A2, entails (a_will (A1 ∨ A2))
                   ((a_will A1) ∨ (a_will A2)).
Proof.
  intros.
  apply ent;
    intros.
  destruct (sat_excluded_middle M1 M2 (χ, ϕ::ψ) (a_will A1));
    auto with chainmail_db.
  repeat a_prop.
  assert (Hasrt : M1 ⦂ M2 ◎ (χ, ϕ :: ψ) ⊨ a_will A2);
    [apply (entails_implies) with (A1:=(a_will (A1 ∨ A2) ∧ (¬ a_will A1)));
     eauto with chainmail_db|].
  a_prop; auto.
Qed.

Lemma will_disj_2 :
  forall A1 A2, entails ((a_will A1) ∨ (a_will A2))
                   (a_will (A1 ∨ A2)).
Proof.
  intros.
  apply ent;
    intros.
  a_prop.
  destruct H.
  - inversion H; subst.
    match goal with
    | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
    end.
    apply sat_will with (ϕ:=ϕ0)(ψ:=ψ0)(χ:=χ0)(σ':=σ')(σ'':=σ''); auto with chainmail_db.
  - inversion H; subst.
    match goal with
    | [H : (_, _) = (_, _)|- _] => inversion H; subst; clear H
    end.
    apply sat_will with (ϕ:=ϕ0)(ψ:=ψ0)(χ:=χ0)(σ':=σ')(σ'':=σ''); auto with chainmail_db.
Qed.

Hint Resolve will_disj_1 will_disj_2 : chainmail_db.

Lemma will_disj_equiv :
  forall A1 A2, equiv_a ((a_will A1) ∨ (a_will A2))
                   (a_will (A1 ∨ A2)).
Proof.
  intros; split; auto with chainmail_db.
Qed.

Hint Resolve will_disj_equiv : chainmail_db.

 *)

Lemma eval_head :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                      M ∙ (χ, ϕ :: nil) ⊢ e ↪ v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    subst;
    eauto with loo_db.
  eapply v_f_ghost; eauto.
  repeat map_rewrite.
  eauto.
Qed.

Lemma sat_head_exp :
  forall M1 M2 σ0 σ e, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_expr e) ->
                  forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
                           M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: nil) ⊨ (a_expr e).
Proof.
  intros M1 M2 σ0 σ e Hsat;
    intros;
    subst;
    inversion Hsat;
    subst.
  eapply sat_exp; eauto.
  eapply eval_head; eauto.
Qed.

Lemma sat_initial_exp :
  forall M1 M2 σ0 σ e, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_expr e) ->
                  forall σ', M1 ⦂ M2 ◎ σ' … σ ⊨ (a_expr e).
Proof.
  intros M1 M2 σ0 σ e Hsat;
    intros;
    subst;
    inversion Hsat;
    subst.
  eapply sat_exp; eauto.
Qed.

Lemma will_entails :
  forall {A1 A2}, entails A1 A2 ->
             forall {M1 M2 σ0 σ}, M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will A1 ->
                             M1 ⦂ M2 ◎ σ0 … σ ⊨ a_will A2.
Proof.
  intros.
  inversion H0;
    subst.
  apply sat_will with (σ':=σ');
    auto.
  eapply (entails_implies);
    eauto.
Qed.

