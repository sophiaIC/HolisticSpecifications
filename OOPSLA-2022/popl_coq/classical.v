Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import operational_semantics.
Require Import chainmail.
Require Import chainmail_tactics.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module ClassicalProperties(L : LanguageDef).

  Import L.
  Module L_ChainmailTactics := ChainmailTactics(L).
  Export L_ChainmailTactics.
  Open Scope reduce_scope.
  Open Scope chainmail_scope.

  Ltac sat_contra_inversion :=
    match goal with
    | [|- ~ _ ◎ _ ⊨ _] =>
      let Hcontra := fresh in
      intro Hcontra;
      inversion Hcontra;
      subst;
      clear Hcontra
    | [|- ~ _ ◎ _ ⊭ _] =>
      let Hcontra := fresh in
      intro Hcontra;
      inversion Hcontra;
      subst;
      clear Hcontra
    | [|- ~ ?P] =>
      let Hcontra := fresh in
      intro Hcontra
    end.

  (** Lemma 5: Classical (4) *)
  Theorem sat_implies_not_nsat_mutind :
    (forall M σ A, M ◎ σ ⊨ A ->
                       ~ M ◎ σ ⊭ A) /\

    (forall M σ A, M ◎ σ ⊭ A ->
                   ~ M ◎ σ ⊨ A).
  Proof.
    apply sat_mutind;
      intros;
      try solve [sat_contra_inversion;
                 repeat link_unique_auto;
                 repeat eval_rewrite;
                 repeat simpl_crush;
                 crush;
                 eauto].
  Qed.

  Theorem sat_implies_not_nsat :
    (forall M σ A, M ◎ σ ⊨ A ->
                   ~ M ◎ σ ⊭ A).
  Proof.
    destruct sat_implies_not_nsat_mutind; crush.
  Qed.

  Theorem nsat_implies_not_sat :
    (forall M σ A, M ◎ σ ⊭ A ->
                   ~ M ◎ σ ⊨ A).
  Proof.
    destruct sat_implies_not_nsat_mutind; crush.
  Qed.

  Fixpoint subst_list {A : Type}`{Subst A nat value} (s : list (value * nat))(a : A) :=
    match s with
    | (x, n) :: s' => [x /s n] (subst_list s' a)
    | _ => a
    end.

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

  Fixpoint list_S (s : list (value * nat)) :=
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
    forall s A, subst_list s (∀x.[A]) = (∀x.[(subst_list (list_S s) A)]).
  Proof.
    intro s;
      subst_list_induction.
  Qed.

  Lemma subst_list_ex :
    forall s A, subst_list s (∃x.[A]) = (∃x.[(subst_list (list_S s) A)]).
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
    forall s x y m β, subst_list s (x calls y ◌ m ⟨ β ⟩) =
                      ((subst_list s x) calls (subst_list s y) ◌ m ⟨ subst_list s β ⟩).
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

  Ltac subst_list_rewrite :=
    try rewrite subst_list_asrt_exp in *;
    try rewrite subst_list_asrt_class in *;
    try rewrite subst_list_arr in *;
    try rewrite subst_list_and in *;
    try rewrite subst_list_or in *;
    try rewrite subst_list_all in *;
    try rewrite subst_list_ex in *;
    try rewrite subst_list_neg in *;
    try rewrite subst_list_access in *;
    try rewrite subst_list_calls in *;
    try rewrite subst_list_external in *;
    try rewrite subst_list_internal in *.

  (** Lemma 5: Classical (1) *)
  Lemma sat_excluded_middle_with_subst :
    (forall A M σ s, (M ◎ σ ⊨ (subst_list s A)) \/
                     (M ◎ σ ⊭ (subst_list s A))).
  Proof.
    intro A;
      induction A;
      intros;
      auto;
      subst_list_rewrite;
      try solve [repeat match goal with
                        | [ s' : list (value * nat),
                                 IH : (forall (_ : mdl)(_ : config)(s : list (value * nat)), _) |-
                            context[?M  ◎ ?σ' ⊨ _]] =>
                          specialize (IH M σ' s')
                        end;
                 repeat disj_split; auto with chainmail_db].

    - (* exp *)
      destruct (excluded_middle (exp_satisfaction M σ (subst_list s e)));
        auto with chainmail_db.

    - (* class *)
      destruct (excluded_middle (has_class M σ (subst_list s e) c));
        auto with chainmail_db.

    - (* all *)
      destruct (excluded_middle (exists x, M ◎ σ ⊭ ([x /s 0] subst_list (list_S s) A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db|].
      left.
      apply sat_all;
        intros.
      destruct (IHA M σ ((x, 0)::(list_S s)));
        auto.
      match goal with
      | [ H : ~ _ |- _ ] =>
        contradiction H
      end.
      eauto.

    - (* ex *)
      destruct (excluded_middle (exists x, M ◎ σ ⊨ ([x /s 0]subst_list (list_S s) A)));
        [destruct_exists_loo;
         andDestruct;
         eauto with chainmail_db|].

      right;
        apply nsat_ex;
        intros.
      destruct (IHA M σ ((x, 0) :: (list_S s)));
        eauto with chainmail_db.
      match goal with
      | [ H : ~ _ |- _ ] =>
        contradiction H
      end.
      eauto.

    - (* access *)
      destruct (excluded_middle (has_access σ (subst_list s a) (subst_list s a0)));
        auto with chainmail_db.

    - (* calls *)
      destruct (excluded_middle (makes_call σ
                                            (subst_list s a)
                                            (subst_list s a0)
                                            m
                                            (subst_list s p)));
        auto with chainmail_db.

    - destruct (excluded_middle (external_obj M σ (subst_list s a)));
        auto with chainmail_db.

    - destruct (excluded_middle (internal_obj M σ (subst_list s a)));
        auto with chainmail_db.

  Qed.

  Theorem sat_excluded_middle :
    forall M σ A, M ◎ σ ⊨ A \/
                  M ◎ σ ⊭ A.
  Proof.
    intros.
    destruct (sat_excluded_middle_with_subst A M σ nil);
      simpl in *;
      auto.
  Qed.

  (** Lemma 5: Classical (5) *)
  Lemma arr_true :
    forall M σ A1 A2,
      M ◎ σ ⊨ (A1 ⟶ A2) ->
      M ◎ σ ⊨ A1 ->
      M ◎ σ ⊨ A2.
  Proof.
    intros M σ A1 A2 Hsat;
      inversion Hsat;
      subst;
      intros;
      auto.

    apply sat_implies_not_nsat_mutind in H2;
      crush.
  Qed.

  Lemma arr_false :
    forall M σ A1 A2,
      M ◎ σ ⊨ (A1 ⟶ A2) ->
      M ◎ σ ⊭ A2 ->
      M ◎ σ ⊭ A1.
  Proof.
    intros M σ A1 A2 Hsat;
      inversion Hsat;
      subst;
      intros;
      auto.

    apply sat_implies_not_nsat_mutind in H2;
      crush.
  Qed.

  Lemma arr_prop1 :
    forall M σ A1 A2,
      (M ◎ σ ⊨ A1 ->
       M ◎ σ ⊨ A2) ->
      M ◎ σ ⊨ (A1 ⟶ A2).
  Proof.
    intros.
    destruct sat_excluded_middle
      with (M:=M)
           (σ:=σ)(A:=A1);
      auto with chainmail_db.
  Qed.

  Lemma arr_prop2 :
    forall M σ A1 A2,
      M ◎ σ ⊨ (A1 ⟶ A2) ->
      (M ◎ σ ⊨ A1 ->
       M ◎ σ ⊨ A2).
  Proof.
    intros.
    eapply arr_true; eauto.
  Qed.

  Lemma arr_prop :
    forall M σ A1 A2,
      M ◎ σ ⊨ (A1 ⟶ A2) <->
      (M ◎ σ ⊨ A1 ->
       M ◎ σ ⊨ A2).
  Proof.
    intros;
      split;
      [apply arr_prop2|apply arr_prop1].
  Qed.

  Lemma all_x_prop :
    forall M σ A,
      M ◎ σ ⊨ (∀x.[A]) <->
      (forall x, M ◎ σ ⊨ ([x /s 0]A)).
  Proof.
    intros; split; eauto with chainmail_db; intros.
    inversion H;
      subst;
      eauto.
  Qed.

  Lemma ex_x_prop :
    forall M σ A,
      M ◎ σ ⊨ (∃x.[A]) <->
      (exists x, M ◎ σ ⊨ ([x /s 0] A)).
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
    forall M σ A1 A2, (M ◎ σ ⊨ (A1 ∧ A2)) <->
                 (M ◎ σ ⊨ A1 /\ M ◎ σ ⊨ A2).
  Proof.
    intros;
      split;
      intros Ha;
      inversion Ha;
      eauto with chainmail_db.
  Qed.

  (** Lemma 5: Classical (3) *)
  Lemma or_iff :
    forall M σ A1 A2, (M ◎ σ ⊨ (A1 ∨ A2)) <->
                 (M ◎ σ ⊨ A1 \/ M ◎ σ ⊨ A2).
  Proof.
    intros;
      split;
      intros Ha;
      inversion Ha;
      eauto with chainmail_db.
  Qed.

  Lemma negate_elim_sat :
    (forall A M σ, M ◎ σ ⊨ (¬ ¬ A) ->
              M ◎ σ ⊨ A).
  Proof.
    intros;
      auto.
    inversion H;
      subst.
    inversion H3;
      auto.
  Qed.

  Lemma negate_elim_nsat :
    (forall A M σ, M ◎ σ ⊭ (¬ ¬ A) ->
              M ◎ σ ⊭ A).
  Proof.
    intros;
      auto.
    inversion H;
      subst.
    inversion H3;
      auto.
  Qed.

  Lemma negate_intro_sat :
    (forall A M σ, M ◎ σ ⊨ A ->
              M ◎ σ ⊨ (¬ ¬ A)).
  Proof.
    intros;
      auto with chainmail_db.
  Qed.

  Lemma negate_intro_nsat :
    (forall A M σ, M ◎ σ ⊭ A ->
              M ◎ σ ⊭ (¬ ¬ A)).
  Proof.
    intros;
      auto with chainmail_db.
  Qed.

  Lemma sat_and_nsat_entails_false :
    forall M A, entails M (A ∧ ¬ A) (a_exp (e_val v_false)).
  Proof.
    intros.
    apply ent;
      intros.

    apply and_iff in H0;
      andDestruct.
    inversion Hb;
      subst.

    apply sat_implies_not_nsat in Ha;
      crush.
  Qed.

  Hint Resolve sat_and_nsat_entails_false : chainmail_db.

  Lemma false_entails_sat_and_nsat :
    forall M A, entails M (a_exp (e_val v_false)) (A ∧ ¬ A).
  Proof.
    intros.
    apply ent;
      intros.

    inversion H0;
      subst.
    inversion H4;
      subst.
    match goal with
    | [H : evaluate _ _ _ _ |- _ ] =>
      inversion H
    end.
  Qed.

  Hint Resolve false_entails_sat_and_nsat : chainmail_db.

  (** Lemma 6: (1) *)
  Lemma sat_and_nsat_equiv_false :
    forall M A, equiv_a M (A ∧ ¬ A) (a_exp (e_val v_false)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Lemma or_commutative' :
    forall M A1 A2, entails M (A1 ∨ A2) (A2 ∨ A1).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H0;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_commutative' : chainmail_db.

  (** Lemma 6: (4) *)
  Lemma or_commutative :
    forall M A1 A2, equiv_a M (A1 ∨ A2) (A2 ∨ A1).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_commutative : chainmail_db.

  Lemma and_commutative' :
    forall M A1 A2, entails M (A1 ∧ A2) (A2 ∧ A1).
  Proof.
    intros;
      eapply ent;
      intros;
      eauto.
    inversion H0;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_commutative' : chainmail_db.

  (** Lemma 6: (3) *)
  Lemma and_commutative :
    forall M A1 A2, equiv_a M (A1 ∧ A2) (A2 ∧ A1).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_commutative : chainmail_db.

  Lemma or_associative_1:
    forall M A1 A2 A3, entails M ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_associative_1 : chainmail_db.

  Lemma or_associative_2:
    forall M A1 A2 A3, entails M (A1 ∨ (A2 ∨ A3)) ((A1 ∨ A2) ∨ A3).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_associative_2 : chainmail_db.

  (** Lemma 6: (5) *)
  Lemma or_associative:
    forall M A1 A2 A3, equiv_a M ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_associative : chainmail_db.

  Lemma and_distributive_1:
    forall M A1 A2 A3, entails M ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H5;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_distributive_1 : chainmail_db.

  Lemma and_distributive_2:
    forall M A1 A2 A3, entails M ((A1 ∧ A3) ∨ (A2 ∧ A3)) ((A1 ∨ A2) ∧ A3).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_distributive_2 : chainmail_db.

  (** Lemma 6: (6) *)
  Lemma and_distributive:
    forall M A1 A2 A3, equiv_a M ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve and_distributive : chainmail_db.

  Lemma or_distributive_1:
    forall M A1 A2 A3, entails M ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto with chainmail_db;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_distributive_1 : chainmail_db.

  Lemma or_distributive_2:
    forall M A1 A2 A3, entails M ((A1 ∨ A3) ∧ (A2 ∨ A3)) ((A1 ∧ A2) ∨ A3).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H5;
      inversion H6;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_distributive_2 : chainmail_db.

  (** Lemma 6: (7) *)
  Lemma or_distributive:
    forall M A1 A2 A3, equiv_a M ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve or_distributive : chainmail_db.

  Lemma neg_distributive_and_1:
    forall M A1 A2, entails M (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_and_1 : chainmail_db.

  Lemma neg_distributive_and_2:
    forall M A1 A2, entails M (¬A1 ∨ ¬A2) (¬(A1 ∧ A2)).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_and_2 : chainmail_db.

  (** Lemma 6: (8) *)
  Lemma neg_distributive_and:
    forall M A1 A2, equiv_a M (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_and : chainmail_db.

  Lemma neg_distributive_or_1:
    forall M A1 A2, entails M (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H4;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_or_1 : chainmail_db.

  Lemma neg_distributive_or_2:
    forall M A1 A2, entails M (¬A1 ∧ ¬A2) (¬(A1 ∨ A2)).
  Proof.
    intros;
      apply ent;
      intros;
      inversion H0;
      subst;
      eauto;
      inversion H5;
      inversion H6;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_or_2 : chainmail_db.

  (** Lemma 6: (9) *)
  Lemma neg_distributive_or:
    forall M A1 A2, equiv_a M (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve neg_distributive_or : chainmail_db.

  Lemma not_ex_x_all_not_1 : 
    forall M A, entails M (¬(∃x.[A])) (∀x.[¬A]).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H0;
      subst.
    inversion H4;
      subst.

    apply sat_all;
      intros.
    apply sat_not.
    eapply H5; eauto with chainmail_db.
  Qed.

  Hint Resolve not_ex_x_all_not_1 : chainmail_db.

  Lemma not_ex_x_all_not_2 : 
    forall M A, entails M (∀x.[¬A]) (¬(∃x.[A])).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H0;
      subst.

    apply sat_not.
    apply nsat_ex;
      intros.
    match goal with
    | [H : forall _, _ |- context[[?x' /s _ ] _]] =>
      specialize (H x')
    end.

    subst_simpl.
    match goal with
    | [H : _ ◎ _ ⊨ ¬ _ |- _ ] =>
      inversion H;
        auto
    end.
  Qed.

  Hint Resolve not_ex_x_all_not_2 : chainmail_db.

  (** Lemma 6: (10) *)
  Lemma not_ex_x_all_not : 
    forall M A, equiv_a M (¬(∃x.[A])) (∀x.[¬A]).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve not_ex_x_all_not : chainmail_db.

  Lemma not_all_x_ex_not_1 : 
    forall M A, entails M (¬(∀x.[A])) (∃x.[¬A]).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H0;
      subst.
    inversion H4;
      subst.

    apply sat_ex with (x:=x);
      auto with chainmail_db.

    apply sat_not; auto.
  Qed.

  Hint Resolve not_all_x_ex_not_1 : chainmail_db.

  Lemma not_all_x_ex_not_2 : 
    forall M A, entails M (∃x.[¬A]) (¬(∀x.[A])).
  Proof.
    intros;
      apply ent;
      intros.

    inversion H0;
      subst.

    apply sat_not.
    apply nsat_all with (x:=x);
      auto with chainmail_db.
    inversion H4; subst; auto.
  Qed.

  Hint Resolve not_all_x_ex_not_2 : chainmail_db.

  Lemma not_all_x_ex_not : 
    forall M A, equiv_a M (¬(∀x.[A])) (∃x.[¬A]).
  Proof.
    intros;
      unfold equiv_a;
      intros;
      split;
      eauto with chainmail_db.
  Qed.

  Hint Resolve not_all_x_ex_not : chainmail_db.

  Lemma entails_implies :
    forall {M M' σ A1 A2}, entails M A1 A2 ->
                     arising M M' σ ->
                     M ◎ σ ⊨ A1 ->
                     M ◎ σ ⊨ A2.
  Proof.
    intros.
    inversion H;
      eauto.
  Qed.

  Hint Resolve entails_implies : chainmail_db.

  Lemma true_satisfied :
    forall M σ, exp_satisfaction M σ (e_true).
    intros.
    eapply exp_sat; eauto with exp_db.
  Qed.

  Hint Resolve true_satisfied : chainmail_db.

  Lemma false_not_satisfied :
    forall M σ, ~ M ◎ σ ⊨ (a_exp (e_false)).
    intros.
    intro Hcontra;
      inversion Hcontra;
      subst.
    match goal with
    | [H : exp_satisfaction _ _ _ |- _] =>
      inversion H;
        subst
    end.
    match goal with
    | [H : evaluate _ _ _ _  |- _] =>
      inversion H
    end.
  Qed.

  Hint Resolve true_satisfied : chainmail_db.

  Lemma false_not_satisfied_corollary :
    forall M σ P, M ◎ σ ⊨ (a_exp (e_false)) ->
             P.
  Proof.
    intros M σ P H;
      contradiction (false_not_satisfied M σ).
  Qed.

  Ltac a_intro :=
    match goal with
    | [|- _ ◎ _ ⊨ (∀x.[ _])] => apply sat_all; intros; simpl in *
    | [|- _ ◎ _ ⊨ (_ ⟶ _)] => apply arr_prop1; intros; simpl in *
    end.

  Ltac a_intros :=
    repeat a_intro.

  Ltac a_prop :=
    repeat match goal with
           | [H : _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> and_iff in H;
                                               destruct H
           | [H : _ ◎ _ ⊨ (_ ∨ _) |- _] => apply -> or_iff in H
           | [H : _ ◎ _ ⊨ (_ ⟶ _) |- _] => rewrite -> arr_prop in H
           | [H : context[_ ◎ _ ⊨ (_ ⟶ _)] |- _] => rewrite -> arr_prop in H
           | [H : _ ◎ _ ⊨ (∀x.[_]) |- _] => rewrite all_x_prop in H; simpl in *
           | [|- _ ◎ _ ⊨ (_ ∧ _)] => apply sat_and
           | [|- _ ◎ _ ⊨ (_ ∨ _)] => apply <- or_iff
           | [H : entails ?A1 ?A2,
                  Ha : ?M ◎  (?χ, ?ϕ::?ψ) ⊨ ?A1 |- _] =>
             notHyp (M ◎ (χ, ϕ::ψ) ⊨ A2);
             let H' := fresh in 
             assert (H' : M ◎ (χ, ϕ::ψ) ⊨ A2);
             [apply (entails_implies M χ ϕ ψ A1 Ha A2 H); eauto|]
           | [Ha : ?M1 ◎ ?σ ⊨ ?A,
                   Hb : ?M1 ◎ ?σ ⊨ ¬ ?A |- _] =>
             apply sat_implies_not_nsat in Ha
           | [Ha : ?M1 ◎ ?σ ⊨ ¬ ?A,
                   Hb : ~ ?M1 ◎ ?σ ⊭ ?A |- _] =>
             inversion Ha; subst; crush

           | [H : ?M1 ◎ ?σ ⊨ (a_exp (e_false)) |- ?P] =>
             apply (false_not_satisfied_corollary M1 σ P H)
           end.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End ClassicalProperties.
