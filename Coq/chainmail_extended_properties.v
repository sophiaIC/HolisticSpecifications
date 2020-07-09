Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import chainmail_properties.
Require Import function_operations.
Require Import sbst.
Require Import classical_properties.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma prev_neg :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ (¬ a_prev A) ->
               (exists σ0 σ' σ'', initial σ0 ->
                             M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                             M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                             σ ◁ σ' ≜ σ'' ->
                             M1 ⦂ M2 ◎ σ'' ⊨ (¬ A)).
Proof.
  intros.
Admitted.

Lemma was_neg :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ (¬ a_was A) ->
               (exists σ0 σ' σ'', initial σ0 ->
                             M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                             M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                             σ ◁ σ' ≜ σ'' ->
                             M1 ⦂ M2 ◎ σ'' ⊨ (¬ A)).
Proof.
Admitted.

Lemma prev_not_disj :
  forall A1 A2, entails (a_prev (A1 ∨ A2) ∧ (a_prev (¬ A1)))
                   (a_prev A2).
Proof.
  intros;
    apply ent;
    intros;
    a_prop.

  inversion H; subst.
  apply sat_prev; intros.
  specialize (H5 σ0 σ' σ'' H1 H2 H3 H4);
    a_prop.
  destruct H5; auto.
  inversion H0; subst.
  specialize (H10 σ0 σ' σ'' H1 H2 H3 H4);
    a_prop.
Qed.

Lemma prev_disj :
  forall A1 A2, entails ((a_prev A1) ∨ (a_prev A2))
                   (a_prev (A1 ∨ A2)).
Proof.
  intros.
  apply ent;
    intros.
  a_prop.
  destruct H.
  - apply sat_prev; intros.
    inversion H; subst.
    specialize (H8 σ0 σ' σ'' H0 H1 H2 H3);
      a_prop; auto.
  - apply sat_prev; intros.
    inversion H; subst.
    specialize (H8 σ0 σ' σ'' H0 H1 H2 H3);
      a_prop; auto.
Qed.

Hint Resolve prev_disj : chainmail_db.

Lemma will_was_1 :
  forall A, entails (a_will (a_was A))
               ((a_was A) ∨ A ∨ (a_will A)).
Proof.
Admitted. (* is this even true? future is deterministic, past is non-deterministic *)

Lemma will_was_2 :
  forall A, entails ((a_was A) ∨ A ∨ (a_will A))
               (a_will (a_was A)).
Proof.
Admitted.

Lemma was_will :
  forall A, entails (a_was (a_will A))
               (a_will (a_was A)).
Proof.
  intros.
  apply ent;
    intros.
  
Admitted.

Lemma was_change_pair_reduction :
  forall M1 M2 σ' σ, M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                σ_wf σ' ->
                forall A, M1 ⦂ M2 ◎ σ ⊨ A ->
                     forall σ'', σ ◁ σ' ≜ σ'' ->
                            M1 ⦂ M2 ◎ σ'' ⊨ (¬ A) ->
                            (exists σ1 σ1' σ2 σ2', M1 ⦂ M2 ⦿ σ' ⤳⋆ σ1 /\
                                              M1 ⦂ M2 ⦿ σ1 ⤳ σ2 /\
                                              M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ /\
                                              σ ◁ σ1 ≜ σ1' /\
                                              σ ◁ σ2 ≜ σ2' /\
                                              M1 ⦂ M2 ◎ σ1' ⊨ (¬ A) /\
                                              M1 ⦂ M2 ◎ σ2' ⊨ A) \/
                            (exists σa σb, M1 ⦂ M2 ⦿ σ' ⤳⋆ σa /\
                                      M1 ⦂ M2 ⦿ σa ⤳ σ /\
                                      σ ◁ σa ≜ σb /\
                                      M1 ⦂ M2 ◎ σb ⊨ (¬ A)) \/
                            (exists σa σb, M1 ⦂ M2 ⦿ σ' ⤳ σa /\
                                      M1 ⦂ M2 ⦿ σa ⤳⋆ σ /\
                                      σ ◁ σa ≜ σb /\
                                      M1 ⦂ M2 ◎ σb ⊨ A) \/
                            (M1 ⦂ M2 ⦿ σ' ⤳ σ).
Proof.
  intros M1 M2 σ' σ Hred;
    induction Hred;
    intros;
    auto.

  - specialize (IHHred (pair_reduction_preserves_config_wf M1 M2 σ1 σ H H0) A H1).
    let someσ := fresh "σ" in
    destruct (adaptation_exists_wf σ2 σ) as [someσ];
      eauto with loo_db.
    destruct (sat_excluded_middle M1 M2 σ0 A).
    + right; right; left.
      eexists; eauto with loo_db.
    + apply sat_not in H5.
      specialize (IHHred σ0 H4 H5).
      destruct IHHred as [IH|IH];
        [|destruct IH as [IH|IH];
          [|destruct IH as [IH|IH]]].
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         let someσ3 := fresh "σ" in
         let someσ4 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           destruct Htmp as [someσ3 Htmp];
           destruct Htmp as [someσ4];
           andDestruct;
           left;
           exists someσ1, someσ2, someσ3, someσ4;
           repeat split; eauto with loo_db.
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           andDestruct;
           right;
           left;
           exists σ3, σ4;
           repeat split; eauto with loo_db.
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           andDestruct;
           left;
           exists σ, σ0, someσ1, someσ2;
           repeat split; eauto with loo_db.
      * right; left;
          exists σ, σ0;
          eauto with loo_db.
Qed.

Inductive pair_reductions_alt : mdl -> mdl -> config -> config -> Prop :=
| prs_single' : forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                               pair_reductions_alt M1 M2 σ1 σ2
| prs_trans'  : forall M1 M2 σ1 σ σ2, pair_reductions_alt M1 M2 σ1 σ ->
                                 M1 ⦂ M2 ⦿ σ ⤳ σ2 ->
                                 pair_reductions_alt M1 M2 σ1 σ2.

Hint Constructors pair_reductions_alt : loo_db.

Lemma pair_reductions_alt_implies_pair_reductions :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    eauto with loo_db.
  apply pair_reductions_transitive with (σ2:=σ); auto with loo_db.
Qed.

Hint Resolve pair_reductions_alt_implies_pair_reductions : loo_db.
Hint Rewrite pair_reductions_alt_implies_pair_reductions : loo_db.

Lemma pair_reductions_alt_extend :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 forall σ, M1 ⦂ M2 ⦿ σ ⤳ σ1 ->
                      pair_reductions_alt M1 M2 σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Lemma pair_reductions_implies_pair_reductions_alt :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 pair_reductions_alt M1 M2 σ1 σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    eauto with loo_db.
  apply pair_reductions_alt_extend with (σ1:=σ); auto with loo_db.
Qed.

Hint Resolve pair_reductions_implies_pair_reductions_alt : loo_db.
Hint Rewrite pair_reductions_implies_pair_reductions_alt : loo_db.

Lemma pair_reductions_alt_definition :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 <->
                 (M1 ⦂ M2 ⦿ σ1 ⤳ σ2) \/
                 (exists σ, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ /\
                       M1 ⦂ M2 ⦿ σ ⤳⋆ σ2).
Proof.
  intros M1 M2 σ1 σ2;
    split;
    [intro Hred;
     induction Hred;
     eauto with loo_db
    |intro Hred;
     destruct Hred;
     eauto with loo_db].

  - repeat destruct_exists_loo;
      andDestruct;
      eauto with loo_db.
    eapply pair_reductions_transitive; eauto.

Qed.

Lemma adaptation_satisfaction :
  forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
               forall σ1 σ2 σ', σ1 ◁ σ2 ≜ σ ->
                           σ1 ◁ σ2 ≜ σ' ->
                           M1 ⦂ M2 ◎ σ' ⊨ A.
Proof.
Admitted.

Lemma will_change_pair_reduction :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ, σ_wf σ ->
                      σ_wf σ1 ->
                      forall σ1' σ2', σ ◁ σ1 ≜ σ1' ->
                                 σ ◁ σ2 ≜ σ2' ->
                                 forall A, M1 ⦂ M2 ◎ σ1' ⊨ A ->
                                      M1 ⦂ M2 ◎ σ2' ⊨ (¬ A) ->
                                      (exists σa σb, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σa /\
                                                σ ◁ σa ≜ σb /\
                                                M1 ⦂ M2 ◎ σb ⊨ (¬ A) /\
                                                (forall σa' σb', M1 ⦂ M2 ⦿ σ1 ⤳⋆ σa' ->
                                                            M1 ⦂ M2 ⦿ σa' ⤳⋆ σa ->
                                                            σ ◁ σa' ≜ σb' ->
                                                            M1 ⦂ M2 ◎ σb' ⊨ A)) \/
                                      (M1 ⦂ M2 ⦿ σ1 ⤳ σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.

  - assert (Hwf : σ_wf σ);
      [eauto with loo_db|].
    let someσ := fresh "σ" in
    let Hadapt := fresh "H" in
    destruct (adaptation_exists_wf σ0 σ) as [someσ Hadapt];
      auto;
      destruct (sat_excluded_middle M1 M2 σ3 A) as [Hsat|Hnsat];
      specialize (IHHred σ0);
      repeat auto_specialize;
      specialize (IHHred someσ σ2');
      repeat auto_specialize.

    + specialize (IHHred A);
        repeat auto_specialize.
      destruct IHHred as [IH|IH].

      * repeat destruct_exists_loo;
          andDestruct.
        left.
        exists σ4, σ5;
          repeat split;
          eauto with loo_db;
          intros.
        specialize (Hb σa' σb').
        inversion H7; subst.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           eapply adaptation_satisfaction; eauto.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           apply Hb; auto.

      * left.
        exists σ2, σ2';
          repeat split;
          eauto with loo_db;
          intros.
        inversion H7; inversion H8; subst.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           eapply adaptation_satisfaction; eauto.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           apply pair_reduction_unique with (σ2:=σ2) in H15;
             auto;
             subst.
           eapply adaptation_satisfaction; eauto.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           apply pair_reductions_path_unique with (σ:=σa') in IH;
             crush.
        ** apply pair_reduction_unique with (σ2:=σ) in H10;
             auto;
             subst.
           apply pair_reductions_path_unique with (σ:=σa') in IH;
             crush.

    + left; exists σ, σ3;
        repeat split;
        eauto with loo_db;
        [apply sat_not; auto|intros].
      apply pair_reductions_path_unique with (σ:=σa') in H;
        crush.
Qed.

(*Lemma will_change_pair_reduction :
  forall M1 M2 σ σ', pair_reductions_alt M1 M2 σ σ' ->
                σ_wf σ ->
                forall A, M1 ⦂ M2 ◎ σ ⊨ A ->
                     forall σ'', σ ◁ σ' ≜ σ'' ->
                            M1 ⦂ M2 ◎ σ'' ⊨ (¬ A) ->
                            (forall σa' σb', pair_reductions_alt M1 M2 σ σa' /\
                                        pair_reductions_alt M1 M2 σa' σ' /\
                                        σ ◁ σa' ≜ σb' /\
                                        M1 ⦂ M2 ◎ σb' ⊨ A) \/
                            (exists σa σb, pair_reductions_alt M1 M2 σ σa /\
                                      σ ◁ σa ≜ σb /\
                                      M1 ⦂ M2 ◎ σb ⊨ (¬ A) /\
                                      (forall σa' σb', pair_reductions_alt M1 M2 σ σa' /\
                                                  pair_reductions_alt M1 M2 σa' σa /\
                                                  σ ◁ σa' ≜ σb' /\
                                                  M1 ⦂ M2 ◎ σb' ⊨ A)) \/
                            (exists σa σb, M1 ⦂ M2 ⦿ σ ⤳ σa /\
                                      σ ◁ σa ≜ σb /\
                                      M1 ⦂ M2 ◎ σb ⊨ (¬ A)).
Proof.
  intros M1 M2 σ σ' Hred;
    induction Hred;
    intros.

  - right; right; eauto with loo_db.

  - let someσ := fresh "σ" in
    let Hadapt := fresh "H" in
    destruct (exists_adaptation σ1 σ) as [someσ Hadapt];
      eauto with loo_db;
      specialize (IHHred H0 A H1 someσ Hadapt).
    destruct (sat_excluded_middle M1 M2 σ0 A).
    + 

      
    (pair_reduction_preserves_config_wf M1 M2 σ1 σ H H0) A H1).
    let someσ := fresh "σ" in
    destruct (exists_adaptation σ2 σ) as [someσ];
      eauto with loo_db.
    destruct (sat_excluded_middle M1 M2 σ0 A).
    + right; right; left.
      eexists; eauto with loo_db.
    + apply sat_not in H5.
      specialize (IHHred σ0 H4 H5).
      destruct IHHred as [IH|IH];
        [|destruct IH as [IH|IH];
          [|destruct IH as [IH|IH]]].
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         let someσ3 := fresh "σ" in
         let someσ4 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           destruct Htmp as [someσ3 Htmp];
           destruct Htmp as [someσ4];
           andDestruct;
           left;
           exists someσ1, someσ2, someσ3, someσ4;
           repeat split; eauto with loo_db.
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           andDestruct;
           right;
           left;
           exists σ3, σ4;
           repeat split; eauto with loo_db.
      * let someσ1 := fresh "σ" in
         let someσ2 := fresh "σ" in
         destruct IH as [someσ1 Htmp];
           destruct Htmp as [someσ2 Htmp];
           andDestruct;
           left;
           exists σ, σ0, someσ1, someσ2;
           repeat split; eauto with loo_db.
      * right; left;
          exists σ, σ0;
          eauto with loo_db.
Qed.*)

Lemma interpret_update :
  forall x σ y v v', ⌊ x ⌋ (update_σ_map σ y v) ≜ v' ->
                x <> y ->
                ⌊ x ⌋ σ ≜ v'.
Proof.
  intros.
  inversion H; subst.
  destruct σ as [χ ψ'];
    destruct ψ' as [|ϕ0 ψ0];
    simpl in *;
    subst.
  - repeat map_rewrite;
      crush.

  - repeat map_rewrite;
      simpl in *;
      repeat map_rewrite.
    crush.
Qed.

Hint Resolve interpret_update : loo_db.

Lemma class_of_update :
  forall x σ y v C, classOf x (update_σ_map σ y v) C ->
               x <> y ->
               classOf x σ C.
Proof.
  intros.
  inversion H; subst.
  apply interpret_update in H1;
    auto.
  eapply cls_of;
    eauto.
Qed.

Hint Resolve class_of_update : loo_db.

Lemma interpret_update_vMap :
  forall x χ ϕ ψ v, ⌊ x ⌋ (χ, ϕ::ψ) ≜ v ->
               forall ϕ' y v', vMap ϕ = update y v' (vMap ϕ') ->
                         x <> y ->
                         ⌊ x ⌋ (χ, ϕ'::ψ) ≜ v.
Proof.
  intros.
  inversion H; subst.
  simpl in *;
    subst.
  unfold update, t_update in H0.
  apply equal_f with (x0:=x) in H0.
  eq_auto.
  apply int_x;
    simpl;
    repeat map_rewrite;
    crush.
Qed.

Hint Resolve interpret_update_vMap : loo_db.

Lemma class_of_update_vMap :
  forall x χ ϕ ψ C, classOf x (χ, ϕ::ψ) C ->
               forall ϕ' y v, vMap ϕ = update y v (vMap ϕ') ->
                         x <> y ->
                         classOf x (χ, ϕ'::ψ) C.
Proof.
  intros.
  inversion H; subst.
  apply interpret_update_vMap with (ϕ':=ϕ')(y:=y)(v':=v) in H2;
    auto.
  eapply cls_of;
    eauto.
Qed.

Hint Resolve class_of_update_vMap : loo_db.

Lemma class_of_unique :
  forall x σ C C', classOf x σ C ->
              classOf x σ C' ->
              C' = C.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  interpretation_rewrite.
  match goal with
  | [H : v_addr ?α1 = v_addr ?α2,
         Ha : ?f ?α1 = Some ?o1,
         Hb : ?f ?α2 = Some ?o2 |- _] =>
    inversion H;
      subst;
      rewrite Ha in Hb;
      inversion Hb;
      subst
  end;
    auto.
Qed.

Hint Resolve class_of_unique : loo_db.

Lemma interpretation_same_variable_map :
  forall x σ v, ⌊ x ⌋ σ ≜ v ->
           forall χ ϕ ψ χ' ϕ' ψ',
             σ = (χ, ϕ::ψ) ->
             vMap ϕ' = vMap ϕ ->
             ⌊ x ⌋ (χ', ϕ'::ψ') ≜ v.
Proof.
  intros;
    subst.

  inversion H; subst;
    simpl in *.
  eapply int_x;
    simpl;
    eauto with loo_db.
  repeat map_rewrite;
    crush.
Qed.

Hint Resolve interpretation_same_variable_map : loo_db.
Hint Rewrite interpretation_same_variable_map : loo_db.

Lemma class_of_same_variable_map :
  forall x σ C, classOf x σ C ->
           forall χ ϕ ψ ϕ' ψ',
             σ = (χ, ϕ::ψ) ->
             vMap ϕ' = vMap ϕ ->
             classOf x (χ, ϕ'::ψ') C.
Proof.
  intros;
    subst.
  inversion H; subst.
  eapply cls_of;
    eauto with loo_db.
Qed.

Hint Resolve interpretation_same_variable_map : loo_db.
Hint Rewrite interpretation_same_variable_map : loo_db.

Lemma interpret_x_update_heap_fresh :
  forall x α vα χ ψ v, ⌊ x ⌋ (χ, ψ) ≜ v ->
                  forall v', ⌊ x ⌋ (update α vα χ, ψ) ≜ v' ->
                        fresh_χ χ α ->
                        v' = v.
Proof.
  intros.
  inversion H;
    subst.
  inversion H0;
    subst.
  simpl in *; subst.
  repeat map_rewrite;
    crush.
Qed.

Hint Resolve interpret_x_update_heap_fresh : loo_db.
Hint Rewrite interpret_x_update_heap_fresh : loo_db.

Lemma class_of_update_heap_fresh :
  forall x α v χ ψ C, classOf x (χ, ψ) C ->
                 forall C', classOf x (update α v χ, ψ) C' ->
                       fresh_χ χ α ->
                       C' = C.
Proof.
  intros.
  inversion H;
    subst.
  inversion H0;
    subst.
  simpl in *.
  match goal with
  | [Ha : ⌊ ?x ⌋ (?χ, ?ψ) ≜ ?v1,
          Hb : ⌊ ?x ⌋ (?χ', ?ψ) ≜ ?v2 |- _] =>
    eapply interpret_x_update_heap_fresh in Ha;
      eauto;
      inversion Ha;
      subst
  end.
  destruct (eq_dec α α0);
    subst.
  apply fresh_heap_none in H1;
    crush.
  repeat map_rewrite; crush.
Qed.

Hint Resolve class_of_update_heap_fresh : loo_db.
Hint Rewrite class_of_update_heap_fresh : loo_db.

Lemma class_of_update_same_cname :
  forall x σ C, classOf x σ C ->
           forall χ ψ, σ = (χ, ψ) ->
                  forall α o o', χ α = Some o ->
                            cname o' = cname o ->
                            forall C', classOf x (update α o' χ, ψ) C' ->
                                  C' = C.
Proof.

  Admitted.

Lemma reduction_different_classes_implies_method_call_or_rtrn :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall C1 C2, classOf this σ1 C1 ->
                      classOf this σ2 C2 ->
                      C1 <> C2 ->
                      (exists χ1 ϕ1 ψ1 x0 y0 m ps s, σ1 = (χ1, ϕ1::ψ1) /\
                                                contn ϕ1 = (c_stmt (s_stmts (s_meth x0 y0 m ps) s))) \/
                      (exists χ1 ϕ1 ψ1 x0, σ1 = (χ1, ϕ1::ψ1) /\
                                      contn ϕ1 = (c_stmt (s_rtrn x0))) \/
                      (exists χ1 ϕ1 ψ1 x0 s, σ1 = (χ1, ϕ1::ψ1) /\
                                        contn ϕ1 = (c_stmt (s_stmts (s_rtrn x0) s))).
Proof.
  intros M σ1 σ2 Hred.
    induction Hred;
    intros;
    try solve [left; repeat eexists; eauto with loo_db];
    try solve [right; left; repeat eexists; eauto with loo_db];
    try solve [right; right; repeat eexists; eauto with loo_db].

  - apply class_of_same_variable_map
      with
        (χ:=χ)(ϕ:=frm (update x v (vMap ϕ)) (c_stmt s))
        (ψ:=ψ)(ϕ':=update_ϕ_map ϕ x v)(ψ':=ψ)
      in H4;
      auto.
    assert (Htmp : (χ, update_ϕ_map ϕ x v :: ψ) = update_σ_map (χ, ϕ::ψ) x v);
      [auto|rewrite Htmp in H4].
    match goal with
    | [H : classOf ?x (update_σ_map _ ?y _) _,
       Hneq : ?y <> ?x |- _] =>
      apply class_of_update in H;
        auto
    end.
    match goal with
    |[C1 : cls, C2 : cls, H : C1 <> C2 |- _] =>
     contradiction H; subst
    end.
    eauto with loo_db.
  - subst.
    apply class_of_same_variable_map
      with
        (χ:=χ)(ϕ:=frm (update x v (vMap ϕ)) (c_stmt s))
        (ψ:=ψ)(ϕ':=update_ϕ_map ϕ x v)(ψ':=ψ)
      in H9;
      auto.
    assert (Htmp : (@pair heap (list frame) χ (update_ϕ_map ϕ x v :: ψ)) = update_σ_map (χ, ϕ::ψ) x v). { auto. }
      rewrite -> Htmp in H9.
    match goal with
    | [H : classOf ?x (update_σ_map _ ?y _) _,
       Hneq : ?y <> ?x |- _] =>
      apply class_of_update in H;
        auto
    end.
    match goal with
    |[C1 : cls, C2 : cls, H : C1 <> C2 |- _] =>
     contradiction H; subst
    end.
    eauto with loo_db.

  -  match goal with
     |[C1 : cls, C2 : cls, H : C1 <> C2 |- _] =>
      contradiction H; subst
     end.
     eapply class_of_same_variable_map with (ϕ':=ϕ)(ψ':=ψ) in H12; eauto.
     eapply class_of_update_same_cname in H12; eauto.

  - match goal with
    |[C1 : cls, C2 : cls, H : C1 <> C2 |- _] =>
     contradiction H; subst
    end.
    apply (class_of_update_vMap this) with (ϕ':=ϕ)(y:=x)(v:=v_addr α) in H10;
      auto.
    apply class_of_update_heap_fresh with (C:=C1) in H10; eauto.

  - inversion H1; inversion H2;
      subst;
      simpl in *.
    inversion H4; inversion H11;
      subst;
      simpl in *.
    repeat map_rewrite;
    repeat simpl_crush;
      simpl in *.
    crush.

  - inversion H1; inversion H2;
      subst;
      simpl in *.
    inversion H4; inversion H11;
      subst;
      simpl in *.
    repeat map_rewrite.
    repeat simpl_crush;
      simpl in *.
    crush.
  
Qed.

Lemma wf_config_this_has_class :
  forall σ, σ_wf σ ->
       exists C, classOf this σ C.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  destruct H2 as [ϕ Htmp];
    destruct Htmp as [ψ'];
    simpl in *;
    andDestruct;
    subst.
  specialize (H4 ϕ (in_eq ϕ ψ')).
  inversion H4; subst.
  destruct H2 as [α Htmp];
    destruct Htmp as [o];
    andDestruct.
  exists (cname o).
  eapply cls_of; eauto.
  eapply int_x; simpl; eauto.
Qed.

Lemma reductions_implies_method_call_or_rtrn :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 σ_wf σ1 ->
                 (exists χ1 ϕ1 ψ1 x0 y0 m ps s, σ1 = (χ1, ϕ1::ψ1) /\
                                           contn ϕ1 = (c_stmt (s_stmts (s_meth x0 y0 m ps) s))) \/
                 (exists χ1 ϕ1 ψ1 x0, σ1 = (χ1, ϕ1::ψ1) /\
                                 contn ϕ1 = (c_stmt (s_rtrn x0))) \/
                 (exists χ1 ϕ1 ψ1 x0 s, σ1 = (χ1, ϕ1::ψ1) /\
                                   contn ϕ1 = (c_stmt (s_stmts (s_rtrn x0) s))).
Proof.
  intros.
  induction H; subst; auto.

  unfold external_self, internal_self, is_external, is_internal in *.
  repeat (destruct_exists_loo;
          andDestruct).
  destruct (wf_config_this_has_class σ H0) as [C].
  assert (Hwf : σ_wf σ');
    [eapply reduction_preserves_config_wf; eauto|].
  destruct (wf_config_this_has_class σ' Hwf) as [C'].
  eapply reduction_different_classes_implies_method_call_or_rtrn; eauto.
  intro Hcontra;
    subst;
    crush.
  repeat match goal with
         | [Hclass : classOf this _ _ |- _] =>
           inversion Hclass;
             subst;
             clear Hclass
         end.
  destruct σ as [χ ψ];
    destruct σ' as [χ' ψ'];
    simpl in *.
  destruct ψ as [|ϕ ψ];
    [repeat map_rewrite; crush|].
  destruct ψ' as [|ϕ' ψ'];
    [repeat map_rewrite; crush|].
  repeat map_rewrite.
  repeat match goal with
         | [Hint : ⌊ this ⌋ _ ≜ _ |- _] =>
           inversion Hint;
             subst;
             clear Hint
         end.
  simpl in *;
    repeat map_rewrite;
    repeat simpl_crush.
  crush.
Qed.

(*Lemma pair_reduction_change_implies_method_call :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 σ_wf σ1 ->
                 (exists χ1 ϕ1 ψ1 x0 y0 m ps s, σ1 = (χ1, ϕ1::ψ1) /\
                                           contn ϕ1 = (c_stmt (s_stmts (s_meth x0 y0 m ps) s))) \/
                 (exists χ1 ϕ1 ψ1 x0, σ1 = (χ1, ϕ1::ψ1) /\
                                 contn ϕ1 = (c_stmt (s_rtrn x0))) \/
                 (exists χ1 ϕ1 ψ1 x0 s, σ1 = (χ1, ϕ1::ψ1) /\
                                   contn ϕ1 = (c_stmt (s_stmts (s_rtrn x0) s))).
Proof.
  intros.
  induction H;
    subst.
  eapply reductions_implies_method_call_or_rtrn; eauto.
Qed.*)

Lemma was_change :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                M1 ⦂ M2 ◎ σ ⊨ (a_was (¬ A)) ->
                M1 ⦂ M2 ◎ σ ⊨ (a_was (¬ A ∧ (a_next A)))) /\
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                M1 ⦂ M2 ◎ σ ⊭ (a_was (¬ A)) ->
                M1 ⦂ M2 ◎ σ ⊭ (a_was (¬ A ∧ (a_next A)))).
Proof.
Admitted.

Lemma was_conjunction :
  forall A1 A2, entails (a_was (A1 ∧ A2))
                   ((a_was A1) ∧ (a_was A2)).
Proof.
  intros.
  apply ent;
    intros;
    repeat (a_prop).

  - match goal with
    | [H : _ ⦂ _ ◎ _ ⊨ (a_was (_ ∧ _)) |- _] =>
      inversion H; subst
    end.
    apply sat_was;
      intros.
    match goal with
    | [ Ha : initial ?σ0,
             Hb : ?M1 ⦂ ?M2 ⦿ ?σ0 ⤳⋆ ?σ',
                  Hc : forall σ, initial σ ->
                            ?M1 ⦂ ?M2 ⦿ σ ⤳⋆ ?σ' ->  _ |- exists _ : config, _ ] =>
      specialize (Hc σ0 Ha Hb);
        let someσ1 := fresh "σ" in
        let someσ2 := fresh "σ" in
        let Htmp := fresh in
        destruct Hc as [someσ1 Htmp];
          destruct Htmp as [someσ2];
          exists someσ1, someσ2;
          intros
    end.
    andDestruct; a_prop.
    repeat split; eauto with loo_db.

  - match goal with
    | [H : _ ⦂ _ ◎ _ ⊨ (a_was (_ ∧ _)) |- _] =>
      inversion H; subst
    end.
    apply sat_was;
      intros.
    match goal with
    | [ Ha : initial ?σ0,
             Hb : ?M1 ⦂ ?M2 ⦿ ?σ0 ⤳⋆ ?σ',
                  Hc : forall σ, initial σ ->
                            ?M1 ⦂ ?M2 ⦿ σ ⤳⋆ ?σ' ->  _ |- exists _ : config, _ ] =>
      specialize (Hc σ0 Ha Hb);
        let someσ1 := fresh "σ" in
        let someσ2 := fresh "σ" in
        let Htmp := fresh in
        destruct Hc as [someσ1 Htmp];
          destruct Htmp as [someσ2];
          exists someσ1, someσ2;
          intros
    end.
    andDestruct; a_prop.
    repeat split; eauto with loo_db.
Qed.

Hint Resolve was_conjunction : chainmail_db.
Hint Rewrite was_conjunction : chainmail_db.

Lemma pair_reductions_trans :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ3 ->
                       M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_trans : loo_db.
Hint Rewrite pair_reductions_trans : loo_db.

Lemma finite_ψ_top_frame :
  forall ϕ ψ, finite_ψ (ϕ::ψ) ->
         finite_ψ (ϕ::nil).
Proof.
  intros.
  finite_auto;
    intros.
  inversion H0; subst.

  - apply H, in_eq.

  - crush.

Qed.

Hint Resolve finite_ψ_top_frame : loo_db.

Lemma finite_σ_top_frame :
  forall χ ϕ ψ, finite_σ (χ, ϕ::ψ) ->
           forall χ', finite_σ (χ', ϕ::nil).
Proof.
  intros.
  unfold finite_σ in *;
    simpl in *.
  eauto with loo_db.
Qed.

Hint Resolve finite_σ_top_frame : loo_db.

Lemma has_self_σ_top_frame :
  forall χ ϕ ψ, has_self_σ (χ, ϕ::ψ) ->
           has_self_σ (χ, ϕ::nil).
Proof.
  intros.
  inversion H; subst.
  apply self_config; intros.
  inversion H0; subst.

  - apply H1, in_eq.

  - crush.
Qed.

Hint Resolve has_self_σ_top_frame : loo_db.

Lemma not_stuck_σ_top_frame :
  forall χ ϕ ψ, not_stuck_σ (χ, ϕ::ψ) ->
           not_stuck_σ (χ, ϕ::nil).
Proof.
  intros.
  inversion H; subst.
  unfold not_stuck_σ.
  destruct_exists_loo;
    simpl in *;
    andDestruct.
  crush.
  repeat eexists; eauto.
Qed.

Hint Resolve not_stuck_σ_top_frame : loo_db.

Lemma waiting_σ_top_frame :
  forall χ ϕ ψ, waiting_σ (χ, ϕ::ψ) ->
           waiting_σ (χ, ϕ::nil).
Proof.
  intros.
  inversion H; subst.
  unfold waiting_σ.
  destruct_exists_loo;
    simpl in *;
    andDestruct.
  crush.
  repeat eexists; eauto.
  unfold waiting_ψ;
    intros;
    crush.
Qed.

Hint Resolve waiting_σ_top_frame : loo_db.

Lemma σ_wf_top_frame :
  forall χ ϕ ψ, σ_wf (χ, ϕ::ψ) ->
           σ_wf (χ, ϕ::nil).
Proof.
  intros.
  inversion H; subst.
  apply config_wf; eauto with loo_db.
Qed.

Hint Resolve σ_wf_top_frame : loo_db.

Lemma finite_ϕ_update :
  forall ϕ, finite_ϕ ϕ ->
       forall y v, finite_ϕ (update_ϕ_map ϕ y v).
Proof.
  intros.
  finite_auto;
    intros.
  destruct ϕ as [m c];
    simpl in *.
  eauto with map_db.
Qed.

Hint Resolve finite_ϕ_update : loo_db.

Lemma finite_ψ_update :
  forall ψ, finite_ψ ψ ->
       forall y v, finite_ψ (update_ψ_map ψ y v).
Proof.
  intros.
  unfold finite_ψ in *;
    intros.
  destruct ψ as [|ϕ' ψ'];
    simpl in *;
    [crush|].
  destruct H0; subst;
    eauto with loo_db.
Qed.

Hint Resolve finite_ψ_update : loo_db.

Lemma finite_σ_update :
  forall σ, finite_σ σ ->
       forall y v, finite_σ (update_σ_map σ y v).
Proof.
  intros.
  unfold finite_σ in *;
    simpl in *;
    eauto with loo_db.
Qed.

Hint Resolve finite_σ_update : loo_db.

Lemma has_self_σ_update :
  forall σ, has_self_σ σ ->
       forall y v A, fresh_x_σ y σ A ->
                has_self_σ (update_σ_map σ y v).
Proof.
  intros.
  inversion H; subst.
  apply self_config;
    intros;
    simpl in *.
  destruct ψ as [|ϕ' ψ'];
    unfold update_ψ_map in *;
    unfold update_ϕ_map in *;
    [crush|].
  destruct H2;
    subst;
    eauto.

  - apply self_frm.
    specialize (H1 ϕ' (in_eq ϕ' ψ')).
    inversion H1;
      subst.
    repeat destruct_exists_loo;
      andDestruct;
      crush.
    exists α, o;
      split;
      auto.
    destruct (eq_dec y this) as [Heq|Hneq];
      subst;
      repeat map_rewrite.
    unfold fresh_x_σ in *;
      repeat destruct_exists_loo;
      andDestruct;
      match goal with
      | [H : (_, _) = (_, _) |- _] =>
        inversion H; subst
      end.
    match goal with
    | [H : fresh_x _ _ _ |- _] =>
      inversion H;
        crush
    end.

  - apply H1, in_cons; auto.
Qed.

Hint Resolve has_self_σ_update : loo_db.

Lemma not_stuck_σ_update :
  forall σ, not_stuck_σ σ ->
       forall y v, not_stuck_σ (update_σ_map σ y v).
Proof.
  intros.
  inversion H; subst.
  unfold not_stuck_σ.
  destruct_exists_loo;
    simpl in *;
    andDestruct.
  crush.
  repeat eexists; eauto.
Qed.

Hint Resolve not_stuck_σ_update : loo_db.

Lemma waiting_σ_update :
  forall σ, waiting_σ σ ->
       forall y v, waiting_σ (update_σ_map σ y v).
Proof.
  intros.
  inversion H; subst.
  unfold waiting_σ.
  destruct_exists_loo;
    simpl in *;
    andDestruct.
  crush.
  repeat eexists; eauto.
Qed.

Hint Resolve waiting_σ_update : loo_db.

Lemma σ_wf_update :
  forall σ, σ_wf σ ->
       forall y v A, fresh_x_σ y σ A ->
                σ_wf (update_σ_map σ y v).
Proof.
  intros.
  inversion H; subst.
  apply config_wf; eauto with loo_db.
Qed.

Hint Resolve σ_wf_update : loo_db.

Lemma has_self_σ_this_interpretation :
  forall χ ϕ ψ, has_self_σ (χ, ϕ::ψ) ->
           exists α o, ⌊ this ⌋ (χ, ϕ::ψ) ≜ (v_addr α) /\
                  χ α = Some o.
Proof.
  intros.
  match goal with
  | [H : has_self_σ ?σ |- _] =>
    inversion H; subst
  end.
  match goal with
  | [H : forall ϕ, In ϕ (?ϕ::?ψ) -> _ |- _] =>
    specialize (H ϕ (in_eq ϕ ψ));
      inversion H;
      subst
  end.
  repeat destruct_exists_loo;
    andDestruct.
  exists α, o; split; eauto.
  eapply int_x; simpl; eauto.
Qed.

Hint Resolve has_self_σ_this_interpretation : loo_db.

Lemma wf_σ_this_interpretation :
  forall χ ϕ ψ, σ_wf (χ, ϕ::ψ) ->
           exists α o, ⌊ this ⌋ (χ, ϕ::ψ) ≜ (v_addr α) /\
                  χ α = Some o.
Proof.
  intros χ ϕ ψ H;
    inversion H;
    subst;
    eauto with loo_db.
Qed.

Hint Resolve wf_σ_this_interpretation : loo_db.

Lemma update_map_implies_mapping :
  forall {A B : Type}`{Eq A} (f : partial_map A B) a b,
    f a = Some b ->
    forall a' b', exists b'', (update a' b' f) a = Some b''.
Proof.
  intros.
  repeat map_rewrite.
  destruct (eq_dec a a');
    subst;
    eq_auto;
    eexists;
    eauto.
Qed.

Hint Resolve update_map_implies_mapping : map_db.

Lemma reduction_heap_monotonic :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall α o, (fst σ1) α = Some o ->
                    exists o', (fst σ2) α = Some o'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    simpl in *;
    eauto with map_db.
Qed.

Hint Resolve reduction_heap_monotonic : loo_db.

Lemma reductions_heap_monotonic :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall α o, (fst σ1) α = Some o ->
                        exists o', (fst σ2) α = Some o'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
  match goal with
  | [Ha : forall α' o', fst ?σ1 α' = Some o' -> exists o'', _,
       Hb : fst ?σ1 ?α = Some ?o |- _] =>
    specialize (Ha α o Hb)
  end.
  destruct_exists_loo.
  eauto with loo_db.
Qed.

Hint Resolve reductions_heap_monotonic : loo_db.

Lemma pair_reduction_heap_monotonic :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall α o, (fst σ1) α = Some o ->
                        exists o', (fst σ2) α = Some o'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
  eapply reductions_heap_monotonic in H;
    eauto.
  destruct_exists_loo.
  eapply reduction_heap_monotonic in H;
    eauto.
Qed.

Hint Resolve pair_reduction_heap_monotonic.

Lemma pair_reductions_heap_monotonic :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall α o, (fst σ1) α = Some o ->
                        exists o', (fst σ2) α = Some o'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
  destruct (pair_reduction_heap_monotonic M1 M2 σ1 σ H α o) as [o'];
    auto.
  match goal with
  | [Ha : forall α' o', fst ?σ α' = Some o' -> exists o'', _,
       Hb : fst ?σ ?α = Some ?o |- _] =>
    specialize (Ha α o Hb)
  end.
  destruct_exists_loo.
  eauto with loo_db.
Qed.

Hint Resolve pair_reductions_heap_monotonic : loo_db.

Lemma has_self_adaptation :
  forall σ1 σ2, has_self_σ σ1 ->
           has_self_σ σ2 ->
           forall σ, σ1 ◁ σ2 ≜ σ ->
                (forall α o, (fst σ1) α = Some o ->
                        exists o', (fst σ2) α = Some o') ->
                has_self_σ σ.
Proof.
  intros; subst.
  match goal with
  | [H : ?σ1 ◁ ?σ2 ≜ ?σ |- _] =>
    inversion H;
      subst
  end.
  repeat match goal with
         | [H : has_self_σ (?χ, ?ψ)  |- _] =>
           notHyp (forall ϕ : frame, In ϕ ψ -> has_self_ϕ χ ϕ);
             inversion H; subst
         end.
  apply self_config;
    intros ϕ Hin;
    destruct Hin;
    subst.

  - repeat match goal with
           | [H : forall ϕ' : frame, In ϕ' (?ϕ::?ψ) -> has_self_ϕ _ _ |- _] =>
             specialize (H ϕ (in_eq ϕ ψ));
               inversion H;
               subst
           end.
    repeat destruct_exists_loo;
      andDestruct;
      repeat match goal with
             | [H : context [vMap _] |- _] =>
               simpl in H
             end.
    apply self_frm;
      simpl.
    unfold fst in *.
    match goal with
    |[Ha : forall α' o', ?χ α' = Some o' -> exists _, _,
        Hb : ?χ ?α = Some ?o |- _] =>
     specialize (Ha α o Hb)
    end.
    repeat destruct_exists_loo.
    exists α0, o1;
      split; auto.
    apply extend_some_2; auto.
    apply disjoint_dom_symmetry.
    apply disjoint_composition; eauto with map_db.

  - match goal with
    | [Ha : forall ϕ', In ϕ' (_::?ψ) -> has_self_ϕ ?χ' ϕ',
         Hb : In ?ϕ ?ψ |- has_self_ϕ ?χ' ?ϕ] =>
      apply Ha, in_cons; auto
    end.
Qed.

Hint Resolve has_self_adaptation : loo_db.

Lemma extend_update :
  forall {A B : Type}`{Eq A}(f g : partial_map A B) a b,
    (update a b f) ∪ g = (update a b (f ∪ g)).
Proof.
  intros;
    unfold extend;
    repeat map_rewrite;
    apply functional_extensionality;
    intros a';
    destruct (eq_dec a' a);
    subst;
    eq_auto.
Qed.

Hint Resolve extend_update : map_db.
Hint Rewrite @extend_update : map_db.

Lemma finite_extend :
  forall {A B : Type}`{Eq A}(f : partial_map A B),
    finite f ->
    forall g, finite g ->
         finite (f ∪ g).
Proof.
  intros A B HeqA f Hfin;
    induction Hfin;
    intros;
    auto.
  rewrite extend_update; eauto with map_db.
Qed.

Hint Resolve finite_extend.

Lemma compose_empty_right :
  forall {A B C : Type}`{Eq A}{HeqB : Eq B}(f : partial_map A B),
    (f ∘ (@empty B C HeqB)) = empty.
Proof.
  intros;
    apply functional_extensionality;
    intros a;
    repeat map_rewrite;
    simpl;
    destruct (f a);
    auto.
Qed.

Hint Resolve compose_empty_right : map_db.
Hint Rewrite @compose_empty_right : map_db.

Lemma compose_empty_left :
  forall {A B C : Type}{HeqA : Eq A}`{Eq B}(f : partial_map B C),
    ((@empty A B HeqA) ∘ f) = empty.
Proof.
  intros;
    simpl;
    auto.
Qed.

Hint Resolve compose_empty_left : map_db.
Hint Rewrite @compose_empty_left : map_db.

Lemma finite_map_composition_2' :
  forall {A B C : Type}`{Eq A}`{Eq B}(g : partial_map B C),
    finite_normal_form g -> forall (f : partial_map A B), one_to_one f -> finite_normal_form (f ∘ g).
Proof.
  intros A B C HeqA HeqB g Hfin;
    induction Hfin;
    intros f H121.

  - rewrite compose_empty_right; auto with map_db.

  - destruct (excluded_middle (exists a', f a' = Some a)).
    + destruct_exists_loo.
      assert (Heq : f ∘ (update a b m) = (update x b (f ∘ m)));
        [apply functional_extensionality; intros a'; simpl
        |rewrite Heq; apply norm_update; auto; crush].
      repeat map_rewrite; simpl.
      destruct (partial_map_dec a' f) as [Hsome|Hnone];
        [destruct Hsome as [b' Htmp];
         rewrite Htmp
        |rewrite Hnone].
      * destruct (eq_dec b' a);
          subst;
          eq_auto.
        ** destruct (eq_dec a' x);
             subst;
             eq_auto.
           specialize (H121 x a' a H0 Htmp);
             crush.
        ** destruct (eq_dec a' x);
             subst;
             eq_auto.
           crush.
      * destruct (eq_dec a' x);
          subst;
          [crush|eq_auto].
    + assert (Heq : f ∘ update a b m = f ∘ m);
        [apply functional_extensionality; intros a';
         simpl
        |rewrite Heq; auto].
      destruct (partial_map_dec a' f) as [Hsome|Hnone];
        [destruct Hsome as [b' Hsome];
         rewrite Hsome
        |rewrite Hnone; auto].
      repeat map_rewrite;
        destruct (eq_dec a b');
        subst;
        eq_auto.
      contradiction n; eauto.
Qed.

Hint Resolve finite_map_composition_2' : map_db.

Lemma finite_map_composition_2 :
  forall {A B C : Type}`{Eq A}`{Eq B}(g : partial_map B C),
    finite g -> forall (f : partial_map A B), one_to_one f -> finite (f ∘ g).
Proof.
  intros; eauto with map_db.
Qed.

Hint Resolve finite_map_composition_2 : map_db.

Lemma finite_adaptation :
  forall σ1 σ2, finite_σ σ1 ->
           finite_σ σ2 ->
           forall σ, σ1 ◁ σ2 ≜ σ ->
                finite_σ σ.
Proof.
  intros σ1 σ2 Hfin1 Hfin2 σ Hadapt;
    inversion Hadapt;
    subst.
  unfold finite_σ, finite_ψ, finite_ϕ in *;
    intros ϕ;
    unfold snd in *;
    intros Hin;
    destruct Hin;
    subst;
    [unfold vMap|].

  - repeat match goal with
           | [H : forall ϕ', In ϕ' (?ϕ::?ψ) -> finite (vMap ϕ')  |- _] =>
             specialize (H ϕ (in_eq ϕ ψ));
               unfold vMap in H
           end.
    apply finite_extend;
      auto.
    apply finite_map_composition_2; auto.

  - apply Hfin2, in_cons; auto.

Qed.

Hint Resolve finite_adaptation : loo_db.

Lemma not_stuck_adaptation :
  forall σ1 σ2, not_stuck_σ σ2 ->
           forall σ, σ1 ◁ σ2 ≜ σ ->
                not_stuck_σ σ.
Proof.
  intros.
  match goal with
  | [H : ?σ1 ◁ ?σ2 ≜ ?σ |- _] =>
    inversion H; subst
  end.
  unfold not_stuck_σ, snd in *.
  repeat destruct_exists_loo;
    andDestruct.
  match goal with
  | [H : ?ϕ1::?ψ  = ?ϕ2::?ψ2 |- _] =>
    inversion H; subst
  end.
  exists (frm ((f ∘ β') ∪ β) (c_stmt (❲ f' ↦ s ❳))), ψ0;
    split; auto.
  unfold not_stuck_ϕ, contn in *.
  auto with loo_db.
Qed.

Hint Resolve not_stuck_adaptation : loo_db.

Lemma waiting_adaptation :
  forall σ1 σ2, waiting_σ σ2 ->
           forall σ, σ1 ◁ σ2 ≜ σ ->
                waiting_σ σ.
Proof.
  intros.
  match goal with
  | [H : ?σ1 ◁ ?σ2 ≜ ?σ |- _] =>
    inversion H; subst
  end.
  unfold waiting_σ, snd in *.
  repeat destruct_exists_loo;
    andDestruct.
  match goal with
  | [H : ?ϕ1::?ψ  = ?ϕ2::?ψ2 |- _] =>
    inversion H; subst
  end.
  eexists; eauto.
Qed.

Hint Resolve waiting_adaptation : loo_db.

Lemma wf_adaptation :
  forall σ1 σ2, σ_wf σ1 ->
           σ_wf σ2 ->
           forall σ, σ1 ◁ σ2 ≜ σ ->
                (forall α o, (fst σ1) α = Some o ->
                        exists o', (fst σ2) α = Some o') ->
                σ_wf σ.
Proof.
  intros;
    match goal with
    | [Ha : σ_wf ?σ1,
            Hb : σ_wf ?σ2 |- _] =>
      inversion Ha;
        inversion Hb;
        subst
    end.
  apply config_wf; eauto with loo_db.
Qed.

Hint Resolve wf_adaptation : loo_db.

(*Lemma guards_method_call :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall χ ϕ σ1' σ2', (χ, ϕ::nil) ◁ σ1 ≜ σ1' ->
                                (χ, ϕ::nil) ◁ σ2 ≜ σ2' ->
                                σ_wf (χ, ϕ::nil) ->
                                M1 ⦂ M2 ⦿ (χ, ϕ::nil) ⤳⋆ σ1 ->
                                forall x y, M1 ⦂ M2 ◎ σ1' ⊨ guards x y ->
                                       M1 ⦂ M2 ◎ σ2' ⊨ (¬ guards x y) ->
                                       (forall σ σ', M1 ⦂ M2 ⦿ (χ, ϕ::nil) ⤳⋆ σ ->
                                                M1 ⦂ M2 ⦿ σ ⤳⋆ σ1 ->
                                                (χ, ϕ::nil) ◁ σ ≜ σ' ->
                                                M1 ⦂ M2 ◎ σ' ⊨ guards x y) ->
                                       (M1 ⦂ M2 ◎ (χ, ϕ::nil) ⊨ guards x y) ->
                                       exists z m vMap, M1 ⦂ M2 ◎ σ1' ⊨ ((a_ this) calls (a_ z) ∎ m ⟨ vMap ⟩).
Proof.
  intros.

  destruct (pair_reduction_change_implies_method_call M1 M2 σ1 σ2);
    auto.

  - eapply pair_reductions_preserves_config_wf;
      eauto.

  - repeat destruct_exists_loo;
      andDestruct;
      subst.
    match goal with
    | [H : (_, _) ◁ (_, _) ≜ _ |- _] =>
      inversion H; subst
    end;
      repeat (match goal with
              | [Heq : ?x = ?x |- _] =>
                clear Heq
              | [H : (_, _) = (_, _) |- _] =>
                inversion H; subst
              end).
    match goal with
    | [H : context [contn _] |- _] =>
      simpl in H
    end.
    match goal with
    | [H : c_stmt _ = c_stmt _ |- _] =>
      inversion H; subst
    end.
    rename_simpl.
    let α := fresh "α" in
    let o := fresh "o" in
    let H := fresh in
    destruct (wf_σ_this_interpretation χ')
      with
        (ψ:=ψ')
        (ϕ:=frm ((f ∘ β') ∪ β0)
                (c_stmt (s_stmts (s_meth (❲ f' ↦ x0 ❳) (❲ f' ↦ x1 ❳) m (❲ f' ↦ β ❳)) (❲ f' ↦ s ❳))))
      as [α H];
      auto.
    +  apply (wf_adaptation)
         with
           (σ1:= (χ1, (frm β0 c) :: nil))
           (σ2:= (χ', (frm β' (c_stmt (s_stmts (s_meth x0 x1 m β) s))) :: ψ'));
         auto.
       * eapply pair_reductions_preserves_config_wf;
           eauto.
       * intros.
         eapply pair_reductions_heap_monotonic; eauto.

    + destruct_exists_loo; andDestruct.
      exists (❲ f' ↦ x1 ❳), m, (❲ f' ↦ β ❳ ∘ v_to_av).
      eapply sat_call
        with (χ:=χ')(ψ:=ψ')
             (x':=❲ f' ↦ x0 ❳)
             (y':=❲ f' ↦ x1 ❳)
             (vMap':=❲ f' ↦ β ❳)
             (s:=❲ f' ↦ s ❳);
        eauto.
      * admit. (* x1 maps to something  *)
      * admit. (* x1 maps to something  *)
      * admit. (* same domain refl *)
      * intros.
        (* vMap, the parameters supplied to the method call maps to some values in the  *)
        (* this perhaps needs to be added to the reduction definition *)
        admit.

  - admit.
    (* if the continuation is a return statement, 
       then there is some method call from within M1 that is  
       being returned from.
       Subsequently, either some method then returns back to 
       client code, or client code is called from the module in 
       question.

     *)

Admitted.*)

(** 

#<h2>#Thoughts on access, expose, temporal operators:#</h2>#

 *)

(**

The non-determinism of both was and will means that
will(was _) and was(will _) have no relation to 
the current configuration. In the original version 
of the expose example, we used *)
(**will((_ access _) ⇒ was (_)). *)
(**
This does not mean what we expect it to mean, because
the "was" does not only refer to the reduction from the 
current configuration to the future moment in time 
where the data was exposed, rather it refers to all 
possible reductions that lead up to the future point in 
time. What we really intend to say is "if in some future
point in time, the private data is aliased, then 
at some point in time between the current moment and that 
future moment, the expose method must have been called".

 *)
(**

In the current model, only was is non-deterministic, 
will is deterministic. As such was(will _) does in fact
mean what we initially meant it to mean, however, 
ideally we would like to model non-determinism of reduction 
to cover really world programs.

 *)
