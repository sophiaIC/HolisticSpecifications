Require Import common.
Require Import loo_def.
Require Import decoupling.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import function_operations.
Require Import sbst_decoupled.
Require Import exp.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(**
#<h1>Classical Properties of Chainmail</h1>#
Lemma 5.1 (Assertions are classical-1). For all initial configurations σ0 , runtime configurations
σ , assertions A and A′, and modules M and M′, we have
#<ol>#
#<li>#
(1) M M′, σ0 , σ ⊨ A or M # M′, σ0 , σ |= ¬A
#</li>#
#<li>#
(2) M M′, σ0 , σ ⊨ A ∧ A′ if and only if M M′, σ0 , σ |= A and M M′, σ0 , σ |= A′
#</li>#
#<li>#
(3) M M′, σ0 , σ ⊨ A ∨ A′ if and only if M M′, σ0 , σ |= A or σ0 , |= A′
#</li>#
#<li>#
(4) M M′, σ0 , σ ⊨ A ∧ ¬A never holds.
#</li>#
#<li>#
(5) M M′, σ0 , σ ⊨ A and M # M′, σ0 , σ ⊨ A → A′ implies M # M′, σ0 , σ |= A′.
#</li>#
</ol>#
 *)

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

Ltac disj_split :=
  match goal with
  | [H : _ \/ _ |- _ ] =>
    destruct H
  end.

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

(*Ltac nsat_class_auto :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊭ (a_class (av_ (v_true)) _) ] =>
    apply nsat_class4;
    intros;
    crush
  | [|- ~ _ ⦂ _ ◎ _ … _ ⊨ (a_class (av_ (v_true)) _) ] =>
    sat_contra_inversion

  | [|- _ ⦂ _ ◎ _ … _ ⊭ (a_class (av_ (v_false)) _) ] =>
    apply nsat_class4;
    intros;
    crush
  | [|- ~ _ ⦂ _ ◎ _ … _ ⊨ (a_class (av_ (v_false)) _) ] =>
    sat_contra_inversion

  | [|- _ ⦂ _ ◎ _ … _ ⊭ (a_class (av_ (v_null)) _) ] =>
    apply nsat_class4;
    intros;
    crush
  | [|- ~ _ ⦂ _ ◎ _ … _ ⊨ (a_class (av_ (v_null)) _) ] =>
    sat_contra_inversion

  | [|- _ ⦂ _ ◎ _ … _ ⊭ (a_class (av_ (v_int _)) _) ] =>
    apply nsat_class4;
    intros;
    crush
  | [|- ~ _ ⦂ _ ◎ _ … _ ⊨ (a_class (av_ (v_int _)) _) ] =>
    sat_contra_inversion
  end.*)



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
    try solve [sat_contra_inversion;
               repeat is_exp_auto;
               repeat link_unique_auto;
               repeat eval_rewrite;
               repeat simpl_crush;
               repeat unique_reduction_auto;
               auto];
    try solve [sat_contra_inversion;
               repeat match goal with
                      | [Ha : forall _, has_type _ _ _ -> _,
                           Hb : has_type _ ?x _ |- _] =>
                        specialize (Ha x);
                        auto_specialize
                      end;
               auto].

  - (* sat-prev *)
    sat_contra_inversion.
    match goal with
    | [H : _ \/ _ |- _] =>
      destruct H;
        subst
    end.
    + specialize (H σ');
        repeat auto_specialize.
      auto.
    + specialize (H σ' (or_intror eq_refl));
        repeat auto_specialize.
      auto.

  - (* sat-was *)
    sat_contra_inversion.
    + disj_split;
        subst;
        auto.
    + disj_split;
        subst;
        auto.
      match goal with
      | [H : ~ _ ⦂ _ ⦿ _ ⤳⋆ _ |- _ ] =>
        contradiction H
      end.
      eapply pair_reductions_transitive;
        eauto.

  - (* sat-in *)
    sat_contra_inversion;
      [crush; eauto|unique_restriction; auto].

  - (* nsat-next *)
    sat_contra_inversion.
    specialize (H σ');
      auto_specialize;
      auto.

  - (* nsat-will *)
    sat_contra_inversion.
    repeat match goal with
           | [Ha : forall σ', _ ⦂ _ ⦿ _ ⌈⤳⋆⌉ σ' -> _,
                Hb : _ ⦂ _ ⦿ _ ⌈⤳⋆⌉ ?σ |- _] =>
             specialize (Ha σ);
               auto_specialize
           end.
    auto.

  - (* nsat-prev *)
    sat_contra_inversion.
    disj_split;
      subst;
      auto.

  - (* nsat-was1 *)
    sat_contra_inversion.
    disj_split;
      subst;
      auto.
    specialize (n σ');
      specialize (H σ');
      repeat auto_specialize.
    auto.

  - (* nsat-was2 *)
    sat_contra_inversion.
    disj_split;
      subst;
      auto.
    match goal with
    | [H : ~ _ ⦂ _ ⦿ _ ⤳⋆ _ |- _ ] =>
      contradiction H
    end.
    eapply pair_reductions_transitive;
      eauto.

  - (* nsat-in1 *)
    sat_contra_inversion;
      eauto.
    match goal with
    | [Ha : forall χ', ~ restrict _ _ χ',
         Hb : restrict _ _ ?χ |- _ ] =>
      specialize (Ha χ)
    end;
      auto.



  - (* nsat-in2 *)
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
  | (x, n) :: s' => [x /s n] (subst_list s' a)
  | _ => a
  end.

Instance substΣavar : Subst a_set nat a_var :=
  {
    sbst := sbstΣ
  }.

Lemma subst_list_asrt_exp :
  forall s e, subst_list s (a_expr e) = (a_expr (subst_list s e)).
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
  forall s A x m, ([x /s m] subst_list s A) = subst_list ((x, m) :: s) A.
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
  forall s x y m β, subst_list s (x calls y ▸ m ⟨ β ⟩) =
               ((subst_list s x) calls (subst_list s y) ▸ (subst_list s m) ⟨ subst_list s β ⟩).
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

Lemma subst_list_private :
  forall s a1 a2, subst_list s (a_private a1 a2) =
             a_private (subst_list s a1) (subst_list s a2).
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
  try rewrite subst_list_private in *;
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
                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ ([x /s 0]subst_list (list_S s) A)));
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
                                    M1 ⦂ M2 ◎ σ0 … σ ⊨ ([x /s 0]subst_list (list_S s) A)));
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
    destruct (excluded_middle (has_access_to σ (subst_list s a) (subst_list s a0)));
      auto with chainmail_db.

  - (* calls *)
    destruct (excluded_middle (makes_call M1 M2 σ
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

  - destruct (excluded_middle (is_private M1 M2 σ (subst_list s a) (subst_list s a0)));
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

Theorem not_sat_implies_nsat :
  (forall M1 M2 σ0 σ A, ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A).
Proof.
  intros.
  destruct (sat_excluded_middle M1 M2 σ0 σ A);
    crush.
Qed.

Theorem not_nsat_implies_sat :
  forall M1 M2 σ0 σ A, ~ M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                  M1 ⦂ M2 ◎ σ0 … σ ⊨ A.
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

  match goal with
  | [H : context[ex_false] |- _] =>
    inversion H;
      subst
  end.
  match goal with
  | [H : context[exp_satisfaction] |- _] =>
    inversion H;
      subst
  end.
  is_exp_auto.
  match goal with
  | [H : _ ∙ _ ⊢ e_false ↪ v_true |- _] =>
    inversion H
  end.
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

Lemma a_self_unique :
  forall {M1 M2 σ0 σ a1}, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_self a1) ->
                       forall {a2}, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_self a2) ->
                               a1 = a2.
Proof.
  intros.
  repeat match goal with
         | [H : _ ⦂  _ ◎ _ … _ ⊨ a_self _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  repeat match goal with
         | [H : is_self _ _ |- _] =>
           inversion H;
             subst;
             clear H
         end.
  crush.
Qed.

(*Lemma is_private_a_private :
  forall {a1 a2 x}, entails (is_private a1 x ∧ a_self a1)
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
Qed.*)

(*Lemma a_private_is_private :
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
Qed.*)

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
  | [H : has_type _ _ a_Mth |- _] =>
    apply has_type_mth in H;
    repeat destruct_exists_loo;
    andDestruct;
    subst
  | [H : has_type _ _ a_Set |- _] =>
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

         | [|- _ ⦂ _ ◎ _ … _ ⊨ (∀[x⦂ _ ]∙ _)] =>
           a_intro
         | [|- _ ⦂ _ ◎ _ … _ ⊨ (_ ⟶ _)] =>
           a_intro

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

(*         | [H : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_private ?a1 ?a2 ∧ a_name ?a2 ?x)
            |- ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ is_private ?a1 ?x] =>
           apply (entails_implies (@a_private_is_private a1 a2 x))
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_private ?a1 ?a2),
                 Hb : ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (a_name ?a2 ?x)
            |- ?M1 ⦂ ?M2 ◎ ?σ0 … ?σ ⊨ (is_private ?a1 ?x)] =>
           apply (entails_implies (@a_private_is_private a1 a2 x))*)
         end;
  repeat has_type_decompose.

Ltac a_destruct :=
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ _ ]∙_) |- _] =>
    apply -> ex_prop in H;
    destruct_exists_loo
  | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ∨ _) |- _] =>
    apply -> or_iff in H;
    destruct H
  end.

Definition ex_conv (M1 M2 : mdl)(σ0 σ : config)(T : a_type)(A : asrt):=
  match T with
  | a_Obj => exists α, has_type σ (ax_val (v_ α)) T /\
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val (v_ α) /s 0] A
  | a_Int => exists i, has_type σ (ax_val (v_int i)) T /\
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val (v_int i) /s 0] A
  | a_Mth => exists m, has_type σ (ax_mth m) T /\
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_mth m /s 0] A
  | a_Set => exists Σ, has_type σ (ax_set Σ) T /\
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_set Σ /s 0] A
  | _ => exists v, has_type σ (ax_val v) T /\
             M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val v /s 0] A
  end.

Ltac a_var_crush :=
  match goal with
  | [H : ax_val ?v = ax_val ?v' |- _] =>
    inversion H;
    subst;
    clear H
  end.

Ltac disj_destruct :=
  match goal with
  | [H : _ \/ _ |- _] =>
    destruct H
  end.

Lemma exists_obj :
  forall {M1 M2 σ0 σ A}, (exists α, has_type σ (ax_val (v_ α)) a_Obj /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val (v_ α) /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Obj]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    eapply sat_ex;
    eauto.

  - a_destruct;
      andDestruct.
    a_prop.
    eauto with chainmail_db.
Qed.

Lemma exists_val :
  forall {M1 M2 σ0 σ A}, (exists v, has_type σ (ax_val v) a_Val /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val v /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Val]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    eapply sat_ex;
    eauto.

  - a_destruct;
      andDestruct.
    a_prop.
    eauto with chainmail_db.
Qed.

Lemma exists_int :
  forall {M1 M2 σ0 σ A}, (exists i, has_type σ (ax_val (v_int i)) a_Int /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val (v_int i) /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Int]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    eapply sat_ex;
    eauto.

  - a_destruct;
      andDestruct.
    a_prop.
    eauto with chainmail_db.
Qed.

Lemma exists_bool :
  forall {M1 M2 σ0 σ A}, (exists b, has_type σ (ax_val b) a_Bool /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_val b /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Bool]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    a_prop.
    a_var_crush.
    disj_destruct;
      subst.
    + apply sat_ex with (x:=ax_val v_true);
        eauto with chainmail_db.
    + apply sat_ex with (x:=ax_val v_false);
        eauto with chainmail_db.

  - a_destruct;
      andDestruct.
    a_prop.
    disj_destruct;
      subst;
      eauto with chainmail_db.
Qed.

Lemma exists_set :
  forall {M1 M2 σ0 σ A}, (exists Σ, has_type σ (ax_set Σ) a_Set /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_set Σ /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Set]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    eapply sat_ex;
    eauto.

  - a_destruct;
      andDestruct.
    a_prop.
    eauto with chainmail_db.
Qed.

Lemma exists_mth :
  forall {M1 M2 σ0 σ A}, (exists m, has_type σ (ax_mth m) a_Mth /\
                          M1 ⦂ M2 ◎ σ0 … σ ⊨ [ax_mth m /s 0] A) <->
                    (M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ a_Mth]∙A)).
Proof.
  intros;
    split;
    intro.

  - destruct_exists_loo;
      andDestruct.
    eapply sat_ex;
    eauto.

  - a_destruct;
      andDestruct.
    a_prop.
    eauto with chainmail_db.
Qed.

Ltac a_exists_base :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ a_Obj]∙_)] =>
    apply exists_obj
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ a_Val]∙_)] =>
    apply exists_val
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ a_Int]∙_)] =>
    apply exists_int
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ a_Set]∙_)] =>
    apply exists_set
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ a_Mth]∙_)] =>
    apply exists_mth
  end.

Ltac a_exists_actual :=
  match goal with
  | [|- _ ⦂ _ ◎ _ … _ ⊨ (∃[x⦂ _ ]∙ _)] =>
    a_exists_base;
    simpl
  end.

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

Ltac a_exists_with_args x y z :=
  match type of x with
  | ltac_No_arg => a_exists_actual
  | _ =>
    match type of y with
    | ltac_No_arg => 
      a_exists_actual;
      exists x; split
    | _ =>
      match type of z with
      | ltac_No_arg =>
        a_exists_actual;
        exists x; split;
        [
        |a_exists_actual;
         exists y; split]
      | _ => 
        a_exists_actual;
        exists x; split;
        [
        |a_exists_actual;
         exists y; split;
         [|
          a_exists_actual;
          exists z; split]]
      end
    end
  end.

Tactic Notation "a_exists" :=
  a_exists_base.
Tactic Notation "a_exists" constr(x) :=
  a_exists_with_args x ltac_no_arg ltac_no_arg.
Tactic Notation "a_exists" constr(x) constr(y):=
  a_exists_with_args x y ltac_no_arg.
Tactic Notation "a_exists" constr(x) constr(y) constr(z):=
  a_exists_with_args x y z.

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

Lemma exp_satisfaction_head :
  forall M1 M2 χ ϕ ψ e, exp_satisfaction M1 M2 (χ, ϕ :: ψ) e ->
                   exp_satisfaction M1 M2 (χ, ϕ :: nil) e.
Proof.
  intros.
  match goal with
  | [H : exp_satisfaction _ _ _ _ |- _] =>
    inversion H;
      subst
  end.
  match goal with
  | [H : _ ∙ (?χ, ?ϕ :: ?ψ) ⊢ _ ↪ _ |- _] =>
    apply eval_head with (χ:=χ)(ϕ:=ϕ)(ψ:=ψ) in H;
      auto
  end.
  eauto with chainmail_db.
Qed.

Lemma sat_head_exp :
  forall M1 M2 σ0 χ ϕ ψ e, M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: ψ) ⊨ (a_expr e) ->
                      M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: nil) ⊨ (a_expr e).
Proof.
  intros.
  match goal with
  | [H : _ ⦂ _ ◎ _ … _ ⊨ _ |- _] =>
    inversion H;
      subst
  end.
  apply sat_exp; eauto.
  eapply exp_satisfaction_head; eauto.
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

