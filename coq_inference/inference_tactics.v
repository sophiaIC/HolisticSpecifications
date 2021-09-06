Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import inference.
Require Import List.
Require Export Coq.Lists.ListSet.

Module InferenceTactics(L : LanguageDef).

  Import L.
  Module L_Inference := Inference(L).
  Export L_Inference.

  Open Scope chainmail_scope.
  Open Scope inference_scope.

  Ltac extract1 v' n' :=
    match goal with
    | [|- ?M ⊢ _ to1 ?A2 onlyIf ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    | [|- ?M ⊢ _ to ?A2 onlyIf ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    | [|- ?M ⊢ _ to ?A2 onlyThrough ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    end.

  Ltac extract2 v' n' :=
    match goal with
    | [|- ?M ⊢ ?A1 to1 _ onlyIf ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3
    | [|- ?M ⊢ ?A1 to _ onlyIf ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3
    | [|- ?M ⊢ ?A1 to _ onlyThrough ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3'
    end.

  Ltac extract3 v' n' :=
    match goal with
    | [|- ?M ⊢ ?A1 to1 ?A2 onlyIf _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst

    | [|- ?M ⊢ ?A1 to ?A2 onlyIf _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst A1' A2'

    | [|- ?M ⊢ ?A1 to ?A2 onlyThrough _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst A1' A2'
    end.


  (**  **)

  Lemma conseq_true :
    forall M A, M ⊢ A ⊇ (a_true).
  Admitted.

  Lemma conseq_or_comm :
    forall M A1 A2, M ⊢ A1 ∨ A2 ⊇ A2 ∨ A1.
  Admitted.

  Lemma caller_ext :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 external.
  Admitted.

  Lemma calls_recv :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ α1 access α2.
  Admitted.

  Lemma calls_param1 :
    forall M α1 α2 m x v β, M ⊢ α1 calls α2 ◌ m ⟨ ⟦ x ↦ v ⟧ β ⟩ ⊇ α1 access v.
  Admitted.

  Lemma class_internal :
    forall M α C, C ∈ M -> M ⊢ a_class (e_addr α) C ⊇ (a_ α) internal.
  Admitted.

  Lemma recv_not_wrapped :
    forall M α1 α2 m β, M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (α2).
  Admitted.

  Lemma param_not_wrapped :
    forall M α1 α2 x p m β, ⟦ x ↦ p ⟧_∈ β -> M ⊢ α1 calls α2 ◌ m ⟨ β ⟩ ⊇ ¬ wrapped (p).
  Admitted.

  Lemma inside_wrapped :
    forall M α C Def, ⟦ C ↦ Def ⟧_∈ M ->
                 annot Def = inside ->
                 M ⊢ a_class (e_addr α) C ⊇ wrapped (a_ α).
  Admitted.

  Lemma fld_type :
    forall M e C CDef f D, ⟦ C ↦ CDef ⟧_∈ M ->
                           ⟦ f ↦ (t_cls D) ⟧_∈ c_fields CDef ->
                           M ⊢ a_class e C ⊇ a_class ((e_acc_f e f)) D.
  Admitted.

  Lemma conseq_absurd :
    forall M A, M ⊢ (a_exp (e_false)) ⊇ A.
  Admitted.

  Lemma conseq_refl :
    forall M A, M ⊢ A ⊇ A.
  Admitted.

  Lemma neg_false :
    forall M A, M ⊢ (A ∧ ¬ A) ⊇ (a_exp (e_false)).
  Admitted.

  Lemma conseq_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊇ A2 ->
                       M ⊢ A2 ⊇ A3 ->
                       M ⊢ A1 ⊇ A3.
  Admitted.

  Lemma conseq_excluded_middle :
    forall M A, M ⊢ (a_exp (e_true)) ⊇ (A ∨ ¬ A).
  Admitted.

  Lemma eq_implies_not_lt :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩵ e2)) ⊇ (¬ a_exp (e1 ⩻ e2)).
  Admitted.

  Lemma lt_implies_not_eq :
    forall M e1 e2, M ⊢ (a_exp (e1 ⩻ e2)) ⊇ (¬ a_exp (e1 ⩵ e2)).
  Admitted.

  Lemma not_false_is_true :
    forall M, M ⊢ (¬ a_exp (e_false)) ⊇ (a_exp (e_true)).
  Admitted.

  Lemma true_is_not_false :
    forall M, M ⊢ (a_exp (e_true)) ⊇ (¬ a_exp (e_false)).
  Admitted.

  Lemma and_true1 :
    forall M A, M ⊢ (A ∧ (a_exp (e_true))) ⊇ A.
  Admitted.

  Lemma and_true2 :
    forall M A, M ⊢ A ⊇ (A ∧ (a_exp (e_true))).
  Admitted.

  Lemma and_comm :
    forall M A1 A2 A, M ⊢ (A1 ∧ A2) ⊇ A ->
                 M ⊢ (A2 ∧ A1) ⊇ A.
  Admitted.

  Lemma and_assoc1 :
    forall M A A1 A2 A3, M ⊢ (A1 ∧ A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ (A2 ∧ A3)) ⊇ A.
  Admitted.

  Lemma and_assoc2 :
    forall M A A1 A2 A3, M ⊢ A1 ∧ (A2 ∧ A3) ⊇ A ->
                    M ⊢ (A1 ∧ A2) ∧ A3 ⊇ A.
  Admitted.

  Lemma and_consequence1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                   M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2.
  Admitted.

  Lemma and_consequence2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                        M ⊢ A1 ∧ A2 ⊇ A1 ∧ A2'.
  Admitted.

  Lemma conseq_and1 :
    forall M A1 A1' A2, M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 ∧ A2 ⊇ A1'.
  Admitted.

  Lemma conseq_and2 :
    forall M A1 A2 A2', M ⊢ A2 ⊇ A2' ->
                        M ⊢ A1 ∧ A2 ⊇ A2'.
  Admitted.

  Lemma conseq_and :
    forall M A A1 A2,  M ⊢ A ⊇ A1 ->
                  M ⊢ A ⊇ A2 ->
                  M ⊢ A ⊇ A1 ∧ A2.
  Admitted.

  (* (∀ M ⊢ [y / x] \longright)*)
  Lemma conseq_ex1 :
    forall M A1 A2, (forall x, M ⊢ [x /s 0] A1 ⊇ A2) ->
               M ⊢ (∃x.[A1]) ⊇ A2.
  Proof.
    intros.
    apply ent;
      intros.
    inversion H1;
      subst.
    specialize (H x).
    inversion H;
      subst.
    eapply H2;
      eauto.
  Qed.

(*)  Lemma conseq_ex_and1 :
    forall M A1 A2, M ⊢ (∃x.[A1]) ∧ A2 ⊇ (∃x.[A1 ∧ A)])*)

  Lemma conseq_ex_and1 :
    forall M A1 A2 A, (forall x, M ⊢ A1 ∧ ([x /s 0] A2) ⊇ A) ->
                 M ⊢ A1 ∧ (∃x.[A2]) ⊇ A.
  Proof.
    intros.
    apply ent;
      intros.
    a_prop.
    match goal with
    | [H : _ ◎ _ ⊨ ∃x.[_] |- _] =>
      inversion H;
        subst
    end.
    eauto with chainmail_db.
  Qed.

  Lemma conseq_ex2 :
    forall M A1 A2, (exists x, M ⊢ A1 ⊇ [x /s 0] A2) ->
               M ⊢ A1 ⊇ ∃x.[A2].
  Admitted.

  Lemma subst_eq :
    forall M x y z A1 A2, M ⊢ [y /s z] A1 ⊇ A2 ->
                     M ⊢ [x /s z] (a_exp (e♢ z ⩵ e_val y) ∧ A1) ⊇ A2.
  Admitted.

  Lemma caller_unique :
    forall M v v' a a' m m' β β',
      M ⊢ (av_ v) calls a ◌ m ⟨ β ⟩ ∧ (av_ v') calls a' ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma recv_unique :
    forall M v v' a a' m m' β β',
      M ⊢ a calls (av_ v) ◌ m ⟨ β ⟩ ∧ a' calls (av_ v) ◌ m' ⟨ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma param_unique :
    forall M a1 a1' a2 a2' m m' x v v' β β',
      M ⊢ a1 calls a2 ◌ m ⟨ ⟦ x ↦ (av_ v) ⟧ β ⟩ ∧ a1' calls a2' ◌ m' ⟨ ⟦ x ↦ (av_ v') ⟧ β' ⟩ ⊇ (a_exp ((e_val v) ⩵ (e_val v'))).
  Admitted.

  Lemma neg_distr_and_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∧ A2) ⊇ ¬ A1 ∨ ¬ A2.
  Admitted.

  Lemma neg_distr_and_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∨ ¬ A2 ⊇ ¬ (A1 ∧ A2).
  Admitted.

  Lemma neg_distr_or_1 :
    forall M A1 A2, M ⊢ ¬ (A1 ∨ A2) ⊇ ¬ A1 ∧ ¬ A2.
  Admitted.

  Lemma neg_distr_or_2 :
    forall M A1 A2, M ⊢ ¬ A1 ∧ ¬ A2 ⊇ ¬ (A1 ∨ A2).
  Admitted.

  Lemma or_l :
    forall M A A1 A2, M ⊢ A ⊇ A1 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_r :
    forall M A A1 A2, M ⊢ A ⊇ A2 ->
                 M ⊢ A ⊇ A1 ∨ A2.
  Admitted.

  Lemma or_lr :
    forall M A1 A2 A, M ⊢ A1 ⊇ A ->
                 M ⊢ A2 ⊇ A ->
                 M ⊢ (A1 ∨ A2) ⊇ A.
  Admitted.

  Ltac hoare_simpl :=
    match goal with
    | [|- _ ⊢ {pre: ?A1 ∧ (?A2 ∧ ?A3)} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_assoc2]
    | [|- _ ⊢ {pre: (_ ∧ (_ ∧ _)) ∧ _} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence1, and_assoc2]
    | [|- _ ⊢ {pre: _ ∧ ((_ ∧ _) ∧ _)} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence1, and_assoc2]
    | [|- _ ⊢ {pre: _ ∧ (a_exp (e_true))} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_true1]
    | [|- _ ⊢ {pre: _ ∧ (¬ (a_exp (e_false)))} _ {post: _}] =>
      eapply hoare_consequence1;
      [|apply and_consequence2, not_false_is_true]
    end.

  Lemma if1_start :
    forall M A1 A2, M ⊢ A1 to1 A2 onlyIf A1.
  Proof.
    auto with inference_db.
  Qed.

  Hint Resolve if1_start : inference_db.

  Lemma if1_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                      M ⊢ A1 to1 A2 onlyIf A3 ->
                      M ⊢ A1' to1 A2 onlyIf A3.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if1_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to1 A2 onlyIf A3 ->
                           M ⊢ A1 to1 A2' onlyIf A3.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if1_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to1 A2 onlyIf A3 ->
                           M ⊢ A1 to1 A2 onlyIf A3'.
  Proof.
    intros.
    eapply if1_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve if1_conseq1 if1_conseq2 if1_conseq3 : inference_db.

  Lemma if_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1' to A2 onlyIf A3.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1 to A2' onlyIf A3.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma if_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to A2 onlyIf A3 ->
                           M ⊢ A1 to A2 onlyIf A3'.
  Proof.
    intros.
    eapply if_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve if_conseq1 if_conseq2 if_conseq3 : inference_db.

  Lemma ot_conseq1 :
    forall M A1 A2 A3 A1', M ⊢ A1' ⊇ A1 ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1' to A2 onlyThrough A3.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma ot_conseq2 :
    forall M A1 A2 A3 A2', M ⊢ A2' ⊇ A2 ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1 to A2' onlyThrough A3.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Lemma ot_conseq3 :
    forall M A1 A2 A3 A3', M ⊢ A3 ⊇ A3' ->
                           M ⊢ A1 to A2 onlyThrough A3 ->
                           M ⊢ A1 to A2 onlyThrough A3'.
  Proof.
    intros.
    eapply ot_conseq;
      try solve [eauto];
      try solve [apply conseq_refl].
  Qed.

  Hint Resolve ot_conseq1 ot_conseq2 ot_conseq3 : inference_db.

  Lemma if1_start_conseq :
    forall M A1 A2 A1', M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 to1 A2 onlyIf A1'.
  Proof.
    intros.
    eapply if1_conseq3;
      eauto with inference_db.
  Qed.

  Hint Resolve if1_start if1_start_conseq : inference_db.

  Lemma if_start_conseq :
    forall M A1 A2 A1', M ⊢ A1 ⊇ A1' ->
                        M ⊢ A1 to A2 onlyIf A1'.
  Proof.
    intros.
    eapply if_conseq3;
      eauto with inference_db.
  Qed.

  Hint Resolve if_start_conseq : inference_db.

  Lemma if1_andE :
    forall M A1 A2 A A', M ⊢ A1 to1 A2 onlyIf A ∧ A' ->
                         M ⊢ A1 to1 A2 onlyIf A.
  Proof.
    intros.
    eapply if1_conseq with (A':=A ∧ A');
      [ eauto
      | apply conseq_refl
      | apply conseq_refl
      | apply conseq_and1, conseq_refl].
  Qed.

  Lemma compose_update :
    forall {A B C : Type}`{Eq A} (f : B -> C) (a : A) (b : B) (g : partial_map A B),
      (fun b => Some (f b)) ∘ (⟦ a ↦ b ⟧ g) = ⟦ a ↦ f b ⟧ (fun b => Some (f b)) ∘ g.
  Proof.
    intros.
    simpl.
    apply functional_extensionality;
      intros.
    repeat map_rewrite.
    destruct (eqb x a);
      auto.
  Qed.

  Lemma compose_empty :
    forall {A B C}`{Eq A} (f : B -> C),
      (fun b => Some (f b)) ∘ empty = empty.
  Proof.
    intros;
      auto.
  Qed.

  Ltac compose_simpl :=
    match goal with
    | [|- context[(fun _ => Some (?f _)) ∘ ⟦ _ ↦ _ ⟧ _]] =>
      rewrite compose_update
    | [H : context[(fun _ => Some (?f _)) ∘ ⟦ _ ↦ _ ⟧ _] |- _] =>
      rewrite compose_update in H
    | [|- context[(fun _ => Some (?f _)) ∘ empty]] =>
      rewrite compose_empty
    | [H : context[(fun _ => Some (?f _)) ∘ empty] |- _] =>
      rewrite compose_empty in H
    end.

  Lemma conseq_exp_eq_neq :
    forall M e1 e2 e3, M ⊢ (a_exp (e1 ⩵ e2)) ∧ (¬ a_exp (e2 ⩵ e3)) ⊇ (¬ a_exp (e1 ⩵ e3)).
  Proof.
    intros M e1 e2 e3.
  Admitted.

  Lemma neqb_S :
    forall n, n =? S n = false.
  Proof.
    intros n;
      induction n;
      auto.
  Qed.

  Lemma exp_subst_raise_n :
    forall (e : exp)(x : value) n, ([x /s n] (e ↑ n)) = (e ↑ n).
  Proof.
    intros e;
      induction e;
      intros;
      auto;
      try solve [raise_simpl;
                 subst_simpl;
                 try rewrite IHe;
                 try rewrite IHe1;
                 try rewrite IHe2;
                 try rewrite IHe3;
                 auto].

    * simpl.
      destruct  (n0 =? n) eqn : Heq.
      ** apply Nat.eqb_eq in Heq;
           subst.
         assert (Hrewrite : n <=? n = true);
           [apply Nat.leb_refl|rewrite Hrewrite; clear Hrewrite].
         assert (Hrewrite : n =? S n = false);
           [apply neqb_S|rewrite Hrewrite; clear Hrewrite; auto].

      ** destruct (n0 <? n) eqn : Hlt.

         *** apply Nat.ltb_lt in Hlt.
             let H := fresh in
             assert (H : n0 <= n);
               [crush
               |apply leb_correct in H;
                rewrite H;
                clear H].
             assert (Hrewrite : n0 =? S n = false);
               [|rewrite Hrewrite; clear Hrewrite; auto].
             apply <- Nat.eqb_neq.
             crush.

         *** apply Nat.ltb_ge in Hlt.
             apply Nat.eqb_neq in Heq.
             let H := fresh in
             assert (H : n0 <=? n = false);
               [apply <- Nat.leb_gt;
                crush
               |rewrite H].
             apply Nat.eqb_neq in Heq;
               rewrite Heq;
               auto.

  Qed.

  Lemma aval_subst_raise_n :
    forall (a : a_val)(x : value) n, ([x /s n] (a ↑ n)) = (a ↑ n).
  Proof.
    intros.
    destruct a;
      auto.
    let H := fresh in
    destruct (lt_eq_lt_dec n n0) as [H|H];
      [destruct H|].

    * assert (n <= n0);
        [crush|raise_simpl].
      assert (n <> S n0);
        [crush|subst_simpl; auto].

    * subst.
      assert (n0 <= n0);
        [crush|raise_simpl].
      subst_simpl;
        auto.

    * assert (n > n0);
        [auto|raise_simpl].
      subst_simpl.
      assert (n <> n0);
        [crush|subst_simpl; auto].
  Qed.

  Lemma map_subst_raise_n :
    forall (m : partial_map name a_val)(x : value) n,
      ([x /s n] (m ↑ n)) = (m ↑ n).
  Proof.
    intros.
    apply functional_extensionality;
      intros.
    simpl.
    destruct (m x0);
      simpl;
      auto.
    destruct a;
      simpl;
      auto.
    let H := fresh in
    destruct (lt_eq_lt_dec n n0) as [H|H];
      [destruct H|].

    * assert (Hle : n <= n0);
        [crush|].
      apply leb_correct in Hle;
        rewrite Hle.
      assert (Hneq : n <> S n0);
        [crush
        |apply <- Nat.eqb_neq in Hneq;
         rewrite Hneq].
      auto.

    * subst.
      rewrite Nat.leb_refl.
      rewrite neqb_S.
      auto.

    * assert (Hgt : n > n0);
        [auto
        |apply Nat.leb_gt in Hgt;
         rewrite Hgt].
      assert (Hneq : n <> n0);
        [crush
        |apply <- Nat.eqb_neq in Hneq;
         rewrite Hneq].
      auto.

  Qed.

  Lemma asrt_subst_raise_n :
    forall (A : asrt) (x : value) n, ([x /s n] (A ↑ n)) = (A ↑ n).
  Proof.
    intros A;
      induction A;
      intros;
      try solve [raise_simpl;
                 subst_simpl;
                 try rewrite exp_subst_raise_n;
                 try rewrite IHA;
                 try rewrite IHA1;
                 try rewrite IHA2;
                 repeat (rewrite aval_subst_raise_n);
                 repeat (rewrite map_subst_raise_n);
                 auto].
  Qed.

  Lemma conseq_raise_mutind :
    (forall M σ A, M ◎ σ ⊨ A  -> forall n, M ◎ σ ⊨ (A ↑ n)) /\
    (forall M σ A, M ◎ σ ⊭ A  -> forall n, M ◎ σ ⊭ (A ↑ n)).
  Proof.
    apply sat_mutind;
      intros;
      raise_simpl;
      try solve [repeat a_prop; auto with chainmail_db].

    * admit.

    * admit.

    * apply sat_all;
        intros.
      admit.

    * apply sat_ex with (x:=x).
      admit.

  Admitted.

  Lemma conseq_raise :
    (forall M σ A, M ◎ σ ⊨ A  -> forall n, M ◎ σ ⊨ (A ↑ n)).
  Proof.
    destruct conseq_raise_mutind;
      auto.
  Qed.

  Lemma conseq_ex_and_expand_r_1 :
    forall A2 M A1, M ⊢ (∃x.[A1]) ∧ A2 ⊇ (∃x.[A1 ∧ (A2 ↑ 0)]).
  Proof.
    intros.
    apply ent;
      intros.
    repeat a_prop.
    inversion H0;
      subst.
    apply sat_ex with (x:=x).
    subst_simpl.
    a_prop;
      auto.
    rewrite asrt_subst_raise_n.
    apply  conseq_raise;
      auto.
  Qed.

  Lemma conseq_ex_and_expand_l_1 :
    forall A2 M A1, M ⊢ A1 ∧ (∃x.[A2]) ⊇ (∃x.[(A1 ↑ 0) ∧ A2]).
  Proof.
    intros.
    apply ent;
      intros.
    repeat a_prop.
    inversion H1;
      subst.
    apply sat_ex with (x:=x).
    subst_simpl.
    a_prop;
      auto.
    rewrite asrt_subst_raise_n.
    apply conseq_raise;
      auto.
  Qed.

  Ltac spec_auto :=
    match goal with
    |[|- _ ⊢ ?A ⊇ ?A] =>
     apply conseq_refl
    | [ |- _ ⊢ (∃x.[ ?A1 ]) ∧ ?A2 ⊇ (∃x.[ ?A1 ∧ (?A2 ↑ 0)])] =>
      apply conseq_ex_and_expand_r_1
    | [ |- _ ⊢ ?A1 ∧ (∃x.[ ?A2 ]) ⊇ (∃x.[ (?A1 ↑ 0) ∧ ?A2])] =>
      apply conseq_ex_and_expand_l_1
    |[|- _ ⊢ ∃x.[_] ⊇ _] =>
     apply conseq_ex1; intros; simpl

    | [ |- _ ⊢ ¬ (?Aa ∧ ?Ab) ⊇ (¬ ?Aa) ∨ (¬ ?Ab)] =>
      apply neg_distr_and_1
    | [ |- _ ⊢ (¬?Aa) ∨  (¬?Ab) ⊇ ¬ (?Aa ∧ ?Ab)] =>
      apply neg_distr_and_2

    | [ |- _ ⊢ ¬ (?Aa ∨ ?Ab) ⊇ (¬ ?Aa) ∧ (¬ ?Ab)] =>
      apply neg_distr_or_1
    | [ |- _ ⊢ (¬?Aa) ∧  (¬?Ab) ⊇ ¬ (?Aa ∨ ?Ab)] =>
      apply neg_distr_or_2

    |[|- _ ⊢ _ ⊇ _ ∧ _] =>
     apply conseq_and
    |[|- _ ⊢ _ ∧ _ ⊇ _] =>
     tryif (solve [apply conseq_and1; repeat spec_auto])
     then idtac
     else (solve [apply conseq_and2; repeat spec_auto])

    | [|- _ ⊢ _ ∨ _ ⊇ _] =>
      apply or_lr
    | [|- _ ⊢ _ ⊇ _ ∨ _] =>
      tryif (solve [apply or_l; spec_auto])
      then idtac
      else (solve [apply or_r; spec_auto])

    end.

  Lemma conseq_and_components :
    forall M A1 A2 A1' A2', M ⊢ A1 ⊇ A1' ->
                       M ⊢ A2 ⊇ A2' ->
                       M ⊢ A1 ∧ A2 ⊇ A1' ∧ A2'.
  Admitted.

  Lemma conseq_not_not1 :
    forall M A, M ⊢ ¬ (¬ A) ⊇ A.
  Admitted.

  Lemma conseq_not_not2 :
    forall M A, M ⊢ A ⊇ ¬ (¬ A).
  Admitted.

  Ltac is_cnf_l A :=
    match A with
    | ?A1 ∧ (?A2 ∧ ?A3) => fail 1
    | ?A1 ∧ (∃x.[ ?A2 ]) => fail 1
    | (∃x.[ ?A1 ]) ∧ ?A2 => fail 1
    | ?A1 ∧ ?A2 => (tryif (is_cnf_l A1)
                    then (tryif (is_cnf_l A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ?A1 ∨ ?A2 => (tryif (is_cnf_l A1)
                    then (tryif (is_cnf_l A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ?A1 ⟶ ?A2 => (tryif (is_cnf_l A1)
                    then (tryif (is_cnf_l A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ¬ ?A' => is_cnf_l (A')
    | (∀x.[ ?A' ]) => (tryif (is_cnf_l (A'))
                       then (idtac)
                       else (fail 1))
    | (∃x.[ ?A' ]) => (tryif (is_cnf_l (A'))
                       then (idtac)
                       else (fail 1))
    | _ => idtac
    end.

  Ltac not_cnf_l A :=
    tryif (is_cnf_l A)
    then (fail 0)
    else (idtac).

  Ltac distr_neg :=
    match goal with
    | [|- _ ⊢ ?Aa ⊇ _ ] =>
      match Aa with
      | context G [¬ (?Ab ∧ ?Ac)] =>
        let Aa' := context G [(¬ Ab) ∨ (¬ Ac)] in
        apply conseq_trans with (A2:= Aa');
        [repeat spec_auto
        |try distr_neg]
      | context G [¬ (?Ab ∨ ?Ac)] =>
        let Aa' := context G [(¬ Ab) ∧ (¬ Ac)] in
        apply conseq_trans with (A2:= Aa');
        [ repeat spec_auto
        |try distr_neg]
      end
    end.

  Ltac specX_cnf_l :=
    match goal with
    | [|- _ ⊢ ?A ⊇ _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to1 _ onlyIf _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to1 ?A onlyIf _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to _ onlyIf _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to ?A onlyIf _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to _ onlyThrough _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to ?A onlyThrough _] =>
      not_cnf_l A
    end;

    repeat distr_neg;

    match goal with

    (* consequence *)
    | [|- _ ⊢ ?Aa ⊇ _ ] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[(Ab ↑ 0) ∧ Ac]] in
        apply conseq_trans with (A2:=Aa');
        [ repeat spec_auto
        | try specX_cnf_l];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[Ab ∧ (Ac ↑ 0)]] in
        apply conseq_trans with (A2:=Aa');
        [ repeat spec_auto
        | try specX_cnf_l];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad] in
        apply conseq_trans with (A2:=Aa');
        [try (apply and_assoc1, conseq_refl);
         repeat spec_auto
        | try specX_cnf_l]
      end

    (* onlyIf (1) *)
    | [|- _ ⊢ ?Aa to _ onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    (* onlyIf (2) *)
    | [|- _ ⊢ _ to ?Aa onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    (* only through (1)*)
    | [|- _ ⊢ ?Aa to _ onlyThrough _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    (* onlythrough (2) *)
    | [|- _ ⊢ _ to ?Aa onlyThrough _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    (* only if1 (1)*)
    | [|- _ ⊢ ?Aa to1 _ onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    (* only if1 (2) *)
    | [|- _ ⊢ _ to1 ?Aa onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |];
        raise_simpl

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l
        |]
      end

    end.

  Ltac specX_cnf_l_no_ex :=
    match goal with
    | [|- _ ⊢ ?A ⊇ _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to1 _ onlyIf _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to1 ?A onlyIf _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to _ onlyIf _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to ?A onlyIf _] =>
      not_cnf_l A

    | [|- _ ⊢ ?A to _ onlyThrough _] =>
      not_cnf_l A
    | [|- _ ⊢ _ to ?A onlyThrough _] =>
      not_cnf_l A
    end;

    repeat distr_neg;

    match goal with

    (* consequence *)
    | [|- _ ⊢ ?Aa ⊇ _ ] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad] in
        apply conseq_trans with (A2:=Aa');
        [try (apply and_assoc1, conseq_refl);
         repeat spec_auto
        | try specX_cnf_l_no_ex]
      end

    (* onlyIf (1) *)
    | [|- _ ⊢ ?Aa to _ onlyIf _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    (* onlyIf (2) *)
    | [|- _ ⊢ _ to ?Aa onlyIf _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    (* only through (1)*)
    | [|- _ ⊢ ?Aa to _ onlyThrough _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    (* onlythrough (2) *)
    | [|- _ ⊢ _ to ?Aa onlyThrough _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    (* only if1 (1)*)
    | [|- _ ⊢ ?Aa to1 _ onlyIf _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    (* only if1 (2) *)
    | [|- _ ⊢ _ to1 ?Aa onlyIf _] =>
      match Aa with

      | context G [ ?Ab ∧ (?Ac ∧ ?Ad) ] =>
        let Aa' := context G [Ab ∧ Ac ∧ Ad ] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_l_no_ex
        |]
      end

    end.

  Ltac is_cnf_r A :=
    match A with
    | (?A1 ∧ ?A2) ∧ ?A3 => fail 1
    | ?A1 ∧ (∃x.[ ?A2 ]) => fail 1
    | (∃x.[ ?A1 ]) ∧ ?A2 => fail 1
    | ?A1 ∧ ?A2 => (tryif (is_cnf_r A1)
                    then (tryif (is_cnf_r A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ?A1 ∨ ?A2 => (tryif (is_cnf_r A1)
                    then (tryif (is_cnf_r A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ?A1 ⟶ ?A2 => (tryif (is_cnf_r A1)
                    then (tryif (is_cnf_r A2)
                           then idtac
                           else fail 1)
                    else (fail 1))
    | ¬ ?A' => is_cnf_r (A')
    | (∀x.[ ?A' ]) => (tryif (is_cnf_r (A'))
                       then (idtac)
                       else (fail 1))
    | (∃x.[ ?A' ]) => (tryif (is_cnf_r (A'))
                       then (idtac)
                       else (fail 1))
    | _ => idtac
    end.

  Ltac not_cnf_r A :=
    tryif (is_cnf_r A)
    then (fail 0)
    else (idtac).

  Ltac specX_cnf_r :=
    match goal with
    | [|- _ ⊢ ?A ⊇ _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to1 _ onlyIf _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to1 ?A onlyIf _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to _ onlyIf _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to ?A onlyIf _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to _ onlyThrough _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to ?A onlyThrough _] =>
      not_cnf_r A
    end;

    repeat distr_neg;

    match goal with
    (* consequence *)
    | [|- _ ⊢ ?Aa ⊇ _ ] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[(Ab ↑ 0) ∧ Ac]] in
        apply conseq_trans with (A2:=Aa');
        [ repeat spec_auto
        | try specX_cnf_r];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[Ab ∧ (Ac ↑ 0)]] in
        apply conseq_trans with (A2:=Aa');
        [ repeat spec_auto
        | try specX_cnf_r];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad)] in
        apply conseq_trans with (A2:=Aa');
        [try (apply and_assoc2, conseq_refl);
         repeat spec_auto
        | try specX_cnf_r]
      end

    (* onlyIf (1) *)
    | [|- _ ⊢ ?Aa to _ onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    (* onlyIf (2) *)
    | [|- _ ⊢ _ to ?Aa onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    (* only through (1)*)
    | [|- _ ⊢ ?Aa to _ onlyThrough _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    (* onlythrough (2) *)
    | [|- _ ⊢ _ to ?Aa onlyThrough _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    (* only if1 (1)*)
    | [|- _ ⊢ ?Aa to1 _ onlyIf _] =>
      match Aa with

      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    (* only if1 (2) *)
    | [|- _ ⊢ _ to1 ?Aa onlyIf _] =>
      match Aa with
      | context G [ ?Ab ∧ ∃x.[?Ac]] =>
        let Aa' := context G [∃x.[ (Ab ↑ 0) ∧ Ac]] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ ∃x.[?Ab] ∧ ?Ac] =>
        let Aa' := context G [∃x.[ Ab ∧ (Ac ↑ 0) ]] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |];
        raise_simpl

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r
        |]
      end

    end.

  Ltac specX_cnf_r_no_ex :=
    match goal with
    | [|- _ ⊢ ?A ⊇ _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to1 _ onlyIf _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to1 ?A onlyIf _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to _ onlyIf _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to ?A onlyIf _] =>
      not_cnf_r A

    | [|- _ ⊢ ?A to _ onlyThrough _] =>
      not_cnf_r A
    | [|- _ ⊢ _ to ?A onlyThrough _] =>
      not_cnf_r A
    end;

    repeat distr_neg;

    match goal with
    (* consequence *)
    | [|- _ ⊢ ?Aa ⊇ _ ] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad)] in
        apply conseq_trans with (A2:=Aa');
        [try (apply and_assoc2, conseq_refl);
         repeat spec_auto
        | try specX_cnf_r_no_ex]
      end

    (* onlyIf (1) *)
    | [|- _ ⊢ ?Aa to _ onlyIf _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    (* onlyIf (2) *)
    | [|- _ ⊢ _ to ?Aa onlyIf _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    (* only through (1)*)
    | [|- _ ⊢ ?Aa to _ onlyThrough _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply ot_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    (* onlythrough (2) *)
    | [|- _ ⊢ _ to ?Aa onlyThrough _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply ot_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    (* only if1 (1)*)
    | [|- _ ⊢ ?Aa to1 _ onlyIf _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if1_conseq1 with (A1:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    (* only if1 (2) *)
    | [|- _ ⊢ _ to1 ?Aa onlyIf _] =>
      match Aa with

      | context G [ (?Ab ∧ ?Ac) ∧ ?Ad ] =>
        let Aa' := context G [Ab ∧ (Ac ∧ Ad) ] in
        apply if1_conseq2 with (A2:= Aa');
        [try spec_auto;
         try specX_cnf_r_no_ex
        |]
      end

    end.

  Lemma if1_and_assoc1 :
    forall M A1 A2 A3 A4 A5, M ⊢ A1 ∧ (A2 ∧ A3) to1 A4 onlyIf A5 ->
                        M ⊢ (A1 ∧ A2) ∧ A3 to1 A4 onlyIf A5.
  Proof.
    intros.
    specX_cnf_r;
      repeat spec_auto;
      auto.
  Qed.

  Lemma if1_and_assoc1' :
    forall M A1 A2 A3 A4 A5, M ⊢ (A1 ∧ A2) ∧ A3 to1 A4 onlyIf A5 ->
                        M ⊢ A1 ∧ (A2 ∧ A3) to1 A4 onlyIf A5.
  Proof.
    intros.
    specX_cnf_l;
      repeat spec_auto.
    auto.
  Qed.

  Lemma if1_and_assoc2 :
    forall M A1 A2 A3 A4 A5, M ⊢ A1 to1 A2 ∧ (A3 ∧ A4) onlyIf A5 ->
                        M ⊢ A1 to1 (A2 ∧ A3) ∧ A4 onlyIf A5.
  Proof.
    intros;
      specX_cnf_r;
      repeat spec_auto;
      auto.
  Qed.

  Lemma if1_and_assoc3 :
    forall M A1 A2 A3 A4 A5, M ⊢ A1 to1 A2 onlyIf A3 ∧ (A4 ∧ A5) ->
                        M ⊢ A1 to1 A2 onlyIf (A3 ∧ A4) ∧ A5.
  Proof.
    intros M A1 A2 A3 A4 A5 H.
    eapply if1_conseq3;
      [|apply H].
    apply and_assoc1, conseq_refl.
  Qed.

  Lemma or_dumb1 :
    forall M A, M ⊢ A ⊇ A ∨ A.
  Proof.
  Admitted.

  Lemma or_dumb2 :
    forall M A, M ⊢ A ∨ A ⊇ A.
  Proof.
  Admitted.

  Lemma change_class_absurd :
    forall M x C, M ⊢ (a_class (e_ x) C) to1 ¬ (a_class (e_ x) C) onlyIf (a_false).
  Admitted.

  Lemma conseq_not_wrapped :
    forall M x y, M ⊢ x external ∧ x access y ⊇ ¬ wrapped y.
  Admitted.

  Ltac commutativity :=
    match goal with
    | [|- _ ⊢ ?Aa ∧ ?Ab ⊇ _ ] =>
      apply and_comm;
      try specX_cnf_r

    | [|- _ ⊢ ?Aa ∧ ?Ab to1 _ onlyIf _ ] =>
      apply if1_conseq1 with (A1:=Ab ∧ Aa);
      [ apply and_comm;
        spec_auto
       |try specX_cnf_r]

    | [|- _ ⊢ ?Aa ∧ ?Ab to _ onlyIf _ ] =>
      apply if_conseq1 with (A1:=Ab ∧ Aa);
      [ apply and_comm;
        spec_auto
       |try specX_cnf_r]

    | [|- _ ⊢ ?Aa ∧ ?Ab to _ onlyThrough _ ] =>
      apply ot_conseq1 with (A1:=Ab ∧ Aa);
      [ apply and_comm;
        spec_auto
       |try specX_cnf_r]
    end.

  Ltac substitute_equality v :=
    match goal with
    | [ |- _ ⊢ (a_exp ((e_val v) ⩵ _)) ∧ _ ⊇ _ ] =>
      idtac
    | [|- _ ] =>
      fail "no valid equality"
    end;
    extract v 0;
    subst;
    apply subst_eq;
    subst_simpl.

  Ltac there_exists_on_right α :=
    match goal with
    | [ |- _ ⊢ _ ⊇ (∃x.[ _ ]) ] =>
      idtac
    | [ |- _ ] =>
      fail "no top level existential on the right hand side"
    end;
    apply conseq_ex2;
    exists α;
    subst_simpl.

  Ltac introduce_existential_on_left x :=
    match goal with
    | [|- _ ⊢ (∃x.[_]) ⊇ _ ] =>
      apply conseq_ex1;
      intro x;
      subst_simpl
    | [|- _ ⊢ (∃x.[_]) to _ onlyIf _ ] =>
      idtac
    | [|- _ ⊢ (∃x.[_]) to _ onlyIf _ ] =>
      idtac
    | [ |- _ ] =>
      fail "no top level existential on the left hand side"
    end.

  Lemma by_changes_and_conseq :
    forall M A1 A2 A,
      M ⊢ A2 ⊇ ¬ A1 ->
      M ⊢ A1 to1 ¬ A1 onlyIf A ->
      M ⊢ A1 to A2 onlyThrough A.
  Proof.
    intros.
    apply ot_conseq2
      with (A2:=¬ A1);
      auto.
    apply ot_changes.
    auto.
  Qed.

End InferenceTactics.

