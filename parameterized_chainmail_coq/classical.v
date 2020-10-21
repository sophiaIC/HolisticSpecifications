Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import chainmail.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module ClassicalProperties(L : LanguageDef).

  Import L.
  Module L_Chainmail := Chainmail(L).
  Import L_Chainmail.
  Import L_Semantics.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.

  Ltac sat_contra_inversion :=
    match goal with
    | [|- ~ _ ⦂ _ ◎ _ … _ ⊨ _] =>
      let Hcontra := fresh in
      intro Hcontra;
      inversion Hcontra;
      subst;
      clear Hcontra
    | [|- ~ _ ⦂ _ ◎ _ … _ ⊭ _] =>
      let Hcontra := fresh in
      intro Hcontra;
      inversion Hcontra;
      subst;
      clear Hcontra
    | [|- ~ ?P] =>
      let Hcontra := fresh in
      intro Hcontra
    end.


Lemma restrict_unique :
  forall Σ χ χ1 χ2, restrict Σ χ χ1 ->
               restrict Σ χ χ2 ->
               χ1 = χ2.
Proof.
  intros;
    repeat match goal with
           | [H : restrict _ _ _ |- _ ] =>
             inversion H;
               subst;
               clear H
           end.
  apply functional_extensionality;
    intros.
  destruct (partial_map_dec x χ1) as [Hsome1 | Hnone1];
    destruct (partial_map_dec x χ2) as [Hsome2 | Hnone2];
    repeat destruct_exists_loo;
    try rewrite Hsome1;
    try rewrite Hsome2;
    try rewrite Hnone1;
    try rewrite Hnone2;
    auto.

  - repeat match goal with
           | [Ha : forall y o', ?m y = Some o' -> _ ,
                Hb : ?m ?x = Some ?o |- context [?m ?x]] =>
             specialize (Ha x o);
               auto_specialize
           end.
    repeat simpl_crush;
      crush.

  - repeat match goal with
           | [Ha : forall y o', ?m y = Some o' -> _ ,
                Hb : ?m ?x = Some ?o |- context [?m ?x]] =>
             specialize (Ha x o);
               auto_specialize
           end.
    repeat match goal with
           | [Ha : forall y, set_In (a_ y) ?Σ -> _ ,
                Hb : set_In (a_ ?x) ?Σ |- _ ] =>
             specialize (Ha x);
               auto_specialize
           end;
      repeat destruct_exists_loo;
      repeat simpl_crush.

  -  repeat match goal with
           | [Ha : forall y o', ?m y = Some o' -> _ ,
                Hb : ?m ?x = Some ?o |- context [?m ?x]] =>
             specialize (Ha x o);
               auto_specialize
           end.
    repeat match goal with
           | [Ha : forall y, set_In (a_ y) ?Σ -> _ ,
                Hb : set_In (a_ ?x) ?Σ |- _ ] =>
             specialize (Ha x);
               auto_specialize
           end;
      repeat destruct_exists_loo;
      repeat simpl_crush.
Qed.

Ltac unique_restriction :=
  match goal with
  | [Ha : restrict ?Σ ?χ ?χ1,
          Hb : restrict ?Σ ?χ ?χ2 |- _ ] =>
    assert (χ1 = χ2);
    [eapply restrict_unique; eauto|subst; clear Hb]
  end.

  Ltac disj_split :=
    match goal with
    | [H : _ \/ _ |- _ ] =>
      destruct H
    end.

  (** Lemma 5: Classical (4) *)
  Theorem sat_implies_not_nsat_mutind :
    (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                     ~ M1 ⦂ M2 ◎ σ0 … σ ⊭ A) /\

    (forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                     ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ A).
  Proof.
    apply sat_mutind;
      intros;
      try solve [sat_contra_inversion;
                 repeat link_unique_auto;
                 repeat eval_rewrite;
                 repeat simpl_crush;
                 crush;
                 eauto].

    - (* sat_was *)
      sat_contra_inversion.
      + disj_split;
          subst;
          match goal with
          | [H : forall (_ : config), _ -> _ -> _ ⦂ _ ◎ _ … _ ⊭ _,
               _ : ~ _ ⦂ _ ◎ _ … ?σa ⊭ _ |- _] =>
            specialize (H σa)
          end;
          repeat auto_specialize;
          auto.
      + disj_split; subst; auto.
        match goal with
        | [H : ~ _ ⦂ _ ⦿ _ ⤳⋆ _  |- _ ] =>
          contradiction H
        end.
        eapply pair_reductions_transitive;
          eauto.

    - (* sat_in *)
      sat_contra_inversion.
      + match goal with
        | [Ha : forall _, ~ restrict _ _ _,
             Hb : restrict _ _ ?χ |- _ ] =>
          specialize (Ha χ);
            auto
        end.
      + unique_restriction;
          auto.

    - (* nsat_was *)
      sat_contra_inversion.
      disj_split;
        subst;
        auto.
      match goal with
      | [H : ~ _ ⦂ _ ⦿ _ ⤳⋆ _  |- _ ] =>
        contradiction H
      end.
      eapply pair_reductions_transitive;
        eauto.

    - (* nsat_in *)
      sat_contra_inversion;
        unique_restriction;
        auto.
  Qed.

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

  Fixpoint subst_list {A : Type}`{Subst A nat a_var} (s : list (a_var * nat))(a : A) :=
    match s with
    | (x, n) :: s' => ⟦x /s n⟧ (subst_list s' a)
    | _ => a
    end.

  Instance substΣavar : Subst a_set nat a_var :=
    {
    sbst := sbstΣ
    }.

  Lemma subst_list_asrt_exp :
    forall s e, subst_list s (a_exp e) = (a_exp (subst_list s e)).
  Proof.
    intro s;
      induction s as [|p s'];
      intros;
      try solve [simpl; auto].

    destruct p as [a n].
    simpl.
    rewrite IHs'.
    auto.
  Qed.

  Ltac subst_list_induction :=
    match goal with
    | [|- context[subst_list ?s _]] =>
      let p := fresh "p" in
      let s' := fresh "s" in
      let a := fresh "a" in
      let n := fresh "n" in
      let IH := fresh "IH" in
      induction s as [|p s' IH];
      intros;
      [|destruct p as [a n];
        simpl;
        rewrite IH];
      try solve [simpl; auto]
    end.

  Fixpoint list_S (s : list (a_var * nat)) :=
    match s with
    | (a, n) :: s' => (a, S n) :: (list_S s')
    | _ => s
    end.

  Lemma subst_list_asrt_class :
    forall s v C, subst_list s (a_class v C) = (a_class (subst_list s v) C).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_arr :
    forall s A1 A2, subst_list s (A1 ⟶ A2) =
                    ((subst_list s A1) ⟶ (subst_list s A2)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_and :
    forall s A1 A2, subst_list s (A1 ∧ A2) =
                    ((subst_list s A1) ∧ (subst_list s A2)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_or :
    forall s A1 A2, subst_list s (A1 ∨ A2) =
                    ((subst_list s A1) ∨ (subst_list s A2)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_all :
    forall s T A, subst_list s (∀[x⦂ T]∙ A) = (∀[x⦂ T]∙ (subst_list (list_S s) A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_ex :
    forall s T A, subst_list s (∃[x⦂ T]∙ A) = (∃[x⦂ T]∙ (subst_list (list_S s) A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_neg :
    forall s A, (subst_list s (¬ A)) = (¬ (subst_list s A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_asrt_cons :
    forall s A x m, (⟦x /s m⟧ subst_list s A) = subst_list ((x, m) :: s) A.
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_access :
    forall s x y, subst_list s (x access y) = ((subst_list s x) access (subst_list s y)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_calls :
    forall s x y m β, subst_list s (x calls y ◌ m ⟨ β ⟩) =
                      ((subst_list s x) calls (subst_list s y) ◌ (subst_list s m) ⟨ subst_list s β ⟩).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_internal :
    forall s x, subst_list s (x internal) = ((subst_list s x) internal).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_external :
    forall s x, subst_list s (x external) = ((subst_list s x) external).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_next :
    forall s A, subst_list s (a_next A) = (a_next (subst_list s A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_will :
    forall s A, subst_list s (a_will A) = (a_will (subst_list s A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_prev :
    forall s A, subst_list s (a_prev A) = (a_prev (subst_list s A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_was :
    forall s A, subst_list s (a_was A) = (a_was (subst_list s A)).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_in_set :
    forall s e Σ, subst_list s (a_in e Σ) = a_in (subst_list s e) (subst_list s Σ).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_elem :
    forall s e Σ, subst_list s (e ∈ Σ) = (subst_list s e) ∈ (subst_list s Σ).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_self :
    forall s a', subst_list s (a_self a') = (a_self (subst_list s a')).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Ltac subst_list_rewrite :=
    try rewrite subst_list_asrt_exp in *;
    try rewrite subst_list_asrt_class in *;
    try rewrite subst_list_elem in *;
    try rewrite subst_list_arr in *;
    try rewrite subst_list_and in *;
    try rewrite subst_list_or in *;
    try rewrite subst_list_all in *;
    try rewrite subst_list_ex in *;
    try rewrite subst_list_neg in *;
    try rewrite subst_list_access in *;
    try rewrite subst_list_calls in *;
    try rewrite subst_list_next in *;
    try rewrite subst_list_will in *;
    try rewrite subst_list_prev in *;
    try rewrite subst_list_was in *;
    try rewrite subst_list_in_set in *;
    try rewrite subst_list_external in *;
    try rewrite subst_list_internal in *;
    try rewrite subst_list_self in *.

  (** Lemma 5: Classical (1) *)
  Lemma sat_excluded_middle_with_subst :
    (forall A M1 M2 σ0 σ s, (M1 ⦂ M2 ◎ σ0 … σ ⊨ (subst_list s A)) \/
                       (M1 ⦂ M2 ◎ σ0 … σ ⊭ (subst_list s A))).
  Proof.
    intro A;
      induction A;
      intros;
      auto;
      subst_list_rewrite;
      try solve [repeat match goal with
                        | [H : (forall (_ _ : mdl) (_ _ : config)(_ : list (a_var * nat)), _ \/ _)
                           |- ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ _ \/ _ ] =>
                          specialize (H M1 M2 σ0 σ);
                          match goal with
                          | [|- context [subst_list ?s _]] =>
                            specialize (H s)
                          end
                        end;
                 repeat match goal with
                        | [H : _ \/ _ |- _ ] =>
                          destruct H
                        end;
                 eauto with chainmail_db].

    - (* exp *)
      destruct (excluded_middle (exp_satisfaction M1 M2 σ (subst_list s e)));
        auto with chainmail_db.

    - (* class *)
      destruct (excluded_middle (has_class σ (subst_list s a) c));
        auto with chainmail_db.

    - (* elem *)
      destruct (excluded_middle (elem_of_set M1 M2 σ (subst_list s e) (subst_list s a)));
        auto with chainmail_db.

    - (* all *)
      destruct (excluded_middle (exists x, has_type σ x a /\
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ (⟦x /s 0⟧subst_list (list_S s) A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db|].
      left.
      apply sat_all;
        intros.
      destruct (IHA M1 M2 σ0 σ ((x, 0)::(list_S s)));
        auto.
      match goal with
      | [ H : ~ _ |- _ ] =>
        contradiction H
      end.
      eauto.

    - (* ex *)
      destruct (excluded_middle (exists x, has_type σ x a /\
                                           M1 ⦂ M2 ◎ σ0 … σ ⊨ (⟦x /s 0⟧subst_list (list_S s) A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db|].

      right;
        apply nsat_ex;
        intros.
      destruct (IHA M1 M2 σ0 σ ((x, 0) :: (list_S s)));
        eauto with chainmail_db.
      match goal with
      | [ H : ~ _ |- _ ] =>
        contradiction H
      end.
      eauto.

    - (* access *)
      destruct (excluded_middle (has_access_aval M1 M2 σ (subst_list s a) (subst_list s a0)));
        auto with chainmail_db.

    - (* calls *)
      destruct (excluded_middle (makes_call σ
                                            (subst_list s a)
                                            (subst_list s a0)
                                            (subst_list s a1)
                                            (subst_list s p)));
        auto with chainmail_db.

    - (* next *)
      destruct (excluded_middle (exists σ', M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ' /\ M1 ⦂ M2 ◎ σ0 … σ' ⊨ (subst_list s A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db
        |right].
      apply nsat_next;
        intros.
      specialize (IHA M1 M2 σ0 σ' s).
      disj_split;
        auto.
      contradiction n;
        eauto.

    - (* will *)
      destruct (excluded_middle (exists σ', M1 ⦂ M2 ⦿ σ ⌈⤳⋆⌉ σ' /\ M1 ⦂ M2 ◎ σ0 … σ' ⊨ (subst_list s A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db
        |right].
      apply nsat_will;
        intros.
      specialize (IHA M1 M2 σ0 σ' s).
      disj_split;
        auto.
      contradiction n;
        eauto.

    - (* prev *)
      destruct (excluded_middle (exists σ', ((M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' \/
                                              σ0 = σ') /\
                                             M1 ⦂ M2 ⦿ σ' ⤳ σ /\
                                             M1 ⦂ M2 ◎ σ0 … σ' ⊭ (subst_list s A))));
        [destruct_exists_loo; andDestruct; eauto with chainmail_db|left].

      apply sat_prev;
        intros.
      specialize (IHA M1 M2 σ0 σ' s).
      repeat disj_split;
        subst;
        auto;
        contradiction n;
        eauto.

    - (* was *)
      destruct (excluded_middle (M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ));
        [|auto with chainmail_db].
      destruct (excluded_middle (exists σ', (M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' \/
                                             σ0 = σ') /\
                                            M1 ⦂ M2 ⦿ σ' ⤳⋆ σ /\
                                            M1 ⦂ M2 ◎ σ0 … σ' ⊨ (subst_list s A)));
        [destruct_exists_loo; andDestruct; eauto with chainmail_db|].

      right; apply nsat_was1;
        intros;
        auto.

      + specialize (IHA M1 M2 σ0 σ' s).
        disj_split;
          eauto with chainmail_db.
        * contradiction n.
          exists σ';
            repeat split;
            eauto.

      + specialize (IHA M1 M2 σ0 σ0 s).
        disj_split;
          eauto with chainmail_db.
        * contradiction n.
          exists σ0;
            repeat split;
            eauto.

    - (* space *)
      destruct σ as [χ ψ].
      destruct (excluded_middle (exists χ', restrict (subst_list s a) χ χ'));
        [destruct_exists_loo|].

      + specialize (IHA M1 M2 σ0 (χ0, ψ) s);
          disj_split;
          eauto with chainmail_db.

      + right; apply nsat_in1;
          intros; intro Hcontra.
        contradiction n;
          eauto.

    - destruct (excluded_middle (external_obj M1 M2 σ (subst_list s a)));
        auto with chainmail_db.

    - destruct (excluded_middle (internal_obj M1 M2 σ (subst_list s a)));
        auto with chainmail_db.

    - destruct (excluded_middle (is_self σ (subst_list s a)));
        auto with chainmail_db.

  Qed.

  Theorem sat_excluded_middle :
    forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A \/
                         M1 ⦂ M2 ◎ σ0 … σ ⊭ A.
  Proof.
    intros.
    destruct (sat_excluded_middle_with_subst A M1 M2 σ0 σ nil);
      simpl in *;
      auto.
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

    apply sat_implies_not_nsat_mutind in H4;
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

    apply sat_implies_not_nsat_mutind in H4;
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
           (σ:=σ)(σ0:=σ0)(A:=A1);
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

  Lemma all_x_prop :
    forall M1 M2 σ0 σ A T,
      M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀[x⦂ T]∙ A) <->
      (forall x, has_type σ x T ->
            M1 ⦂ M2 ◎ σ0 … σ ⊨ (⟦x /s 0⟧A)).
  Proof.
    intros; split; eauto with chainmail_db; intros.
    inversion H;
      subst;
      eauto.
  Qed.

  Lemma ex_x_prop :
    forall M1 M2 σ0 σ A T,
      M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ T]∙A) <->
      (exists x, has_type σ x T /\
            M1 ⦂ M2 ◎ σ0 … σ ⊨ (⟦x /s 0⟧ A)).
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
    forall A, entails (A ∧ ¬ A) (a_exp (e_val v_false)).
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
    forall A, entails (a_exp (e_val v_false)) (A ∧ ¬ A).
  Proof.
    intros.
    apply ent;
      intros.

    inversion H;
      subst.
    inversion H5;
      subst.
    match goal with
    | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
      inversion H
    end.
  Qed.

  Hint Resolve false_entails_sat_and_nsat : chainmail_db.

  (** Lemma 6: (1) *)
  Lemma sat_and_nsat_equiv_false :
    forall A, equiv_a (A ∧ ¬ A) (a_exp (e_val v_false)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Lemma or_commutative' :
    forall A1 A2, entails (A1 ∨ A2) (A2 ∨ A1).
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
    forall A1 A2, equiv_a (A1 ∨ A2) (A2 ∨ A1).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_commutative : chainmail_db.

  Lemma and_commutative' :
    forall A1 A2, entails (A1 ∧ A2) (A2 ∧ A1).
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
    forall A1 A2, equiv_a (A1 ∧ A2) (A2 ∧ A1).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_commutative : chainmail_db.

  Lemma or_associative_1:
    forall A1 A2 A3, entails ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
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
    forall A1 A2 A3, entails (A1 ∨ (A2 ∨ A3)) ((A1 ∨ A2) ∨ A3).
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
    forall A1 A2 A3, equiv_a ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_associative : chainmail_db.

  Lemma and_distributive_1:
    forall A1 A2 A3, entails ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
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
    forall A1 A2 A3, entails ((A1 ∧ A3) ∨ (A2 ∧ A3)) ((A1 ∨ A2) ∧ A3).
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
    forall A1 A2 A3, equiv_a ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_distributive : chainmail_db.

  Lemma or_distributive_1:
    forall A1 A2 A3, entails ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
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
    forall A1 A2 A3, entails ((A1 ∨ A3) ∧ (A2 ∨ A3)) ((A1 ∧ A2) ∨ A3).
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
    forall A1 A2 A3, equiv_a ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_distributive : chainmail_db.

  Lemma neg_distributive_and_1:
    forall A1 A2, entails (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
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
    forall A1 A2, entails (¬A1 ∨ ¬A2) (¬(A1 ∧ A2)).
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
    forall A1 A2, equiv_a (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_and : chainmail_db.

  Lemma neg_distributive_or_1:
    forall A1 A2, entails (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
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
    forall A1 A2, entails (¬A1 ∧ ¬A2) (¬(A1 ∨ A2)).
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
    forall A1 A2, equiv_a (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_or : chainmail_db.

  Lemma not_ex_x_all_not_1 : 
    forall A T, entails (¬(∃[x⦂ T]∙A)) (∀[x⦂ T]∙¬A).
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

  Hint Resolve not_ex_x_all_not_1 : chainmail_db.

  Lemma not_ex_x_all_not_2 : 
    forall A T, entails (∀[x⦂ T]∙¬A) (¬(∃[x⦂ T]∙A)).
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

  Hint Resolve not_ex_x_all_not_2 : chainmail_db.

  (** Lemma 6: (10) *)
  Lemma not_ex_x_all_not : 
    forall A T, equiv_a (¬(∃[x⦂ T]∙A)) (∀[x⦂ T]∙¬A).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve not_ex_x_all_not : chainmail_db.

  Lemma not_all_x_ex_not_1 : 
    forall A T, entails (¬(∀[x⦂ T]∙A)) (∃[x⦂ T]∙¬A).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H;
      subst.
    inversion H5;
      subst.

    apply sat_ex with (x:=x);
      auto with chainmail_db.

    apply sat_not; auto.
  Qed.

  Hint Resolve not_all_x_ex_not_1 : chainmail_db.

  Lemma not_all_x_ex_not_2 : 
    forall A T, entails (∃[x⦂ T]∙¬A) (¬(∀[x⦂ T]∙A)).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H;
      subst.

    apply sat_not.
    apply nsat_all with (x:=x);
      auto with chainmail_db.
    inversion H7; subst; auto.
  Qed.

  Hint Resolve not_all_x_ex_not_2 : chainmail_db.

  Lemma not_all_x_ex_not : 
    forall A T, equiv_a (¬(∀[x⦂ T]∙A)) (∃[x⦂ T]∙¬A).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve not_all_x_ex_not : chainmail_db.

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

  Ltac a_intro :=
    match goal with
    | [|- _ ⦂ _ ◎ _ … _ ⊨ (∀[x⦂ _ ]∙ _)] => apply sat_all; intros; simpl in *
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
           | [H : _ ⦂ _ ◎ _ … _ ⊨ (∀[x⦂ _]∙_) |- _] => rewrite all_x_prop in H; simpl in *
           | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ∧ _)] => apply sat_and
           | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ∨ _)] => apply <- or_iff
           | [H : entails ?A1 ?A2,
                  Ha : ?M1 ⦂ ?M2 ◎  ?σ0 … (?χ, ?ϕ::?ψ) ⊨ ?A1 |- _] =>
             notHyp (M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ A2);
             let H' := fresh in 
             assert (H' : M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ A2);
             [apply (entails_implies M1 M2 χ ϕ ψ A1 Ha A2 H); eauto|]
           | [Ha : ?M1 ⦂ ?M2 ◎  ?σ0 … ?σ ⊨ ?A,
                   Hb : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ¬ ?A |- _] =>
             apply sat_implies_not_nsat in Ha
           | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ ¬ ?A,
                   Hb : ~ ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊭ ?A |- _] =>
             inversion Ha; subst; crush
           end.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End ClassicalProperties.
