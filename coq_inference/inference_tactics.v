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

  Open Scope specw_scope.
  Open Scope inference_scope.
  Open Scope exp_scope.

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

  Open Scope reduce_scope.

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

  Lemma eval_raise' :
    forall M σ e v, evaluate M σ e v ->
               forall e' n, e = (e' ↑ n) ->
                       evaluate M σ e' v.
  Proof.
    intros M σ e v Heval;
      induction Heval;
      intros.

    * destruct e';
        simpl in H;
        inversion H;
        subst;
        auto with exp_db.

    * destruct e';
        simpl in H0;
        inversion H0;
        subst;
        auto with exp_db.

    * destruct e';
        simpl in H;
        inversion H;
        subst;
        auto with exp_db.

    * destruct e';
        simpl in H1;
        inversion H1;
        subst.
      eapply v_f_heap.
      apply IHHeval with (n0:=n);
        auto.
      apply H.
      auto.

    * destruct e'0;
        simpl in H2;
        inversion H2;
        subst.
      eapply v_f_ghost.
      ** apply IHHeval1 with (n0:=n);
           auto.
      ** apply H.
      ** apply H0.
      ** apply H1.
      ** apply IHHeval2 with (n0:=n);
           auto.
      ** auto.

    * destruct e';
        inversion H;
        subst.
      apply v_if_true.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H;
        subst.
      apply v_if_false.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H;
        subst.
      eapply v_equals.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H0;
        subst.
      eapply v_nequals.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.
      auto.

    * destruct e';
        inversion H0;
        subst.
      eapply v_lt.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.
      auto. 

    * destruct e';
        inversion H0;
        subst.
      eapply v_nlt.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.
      auto.

    * destruct e';
        inversion H;
        subst.
      eapply v_plus.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H;
        subst.
      eapply v_minus.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H;
        subst.
      eapply v_mult.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

    * destruct e';
        inversion H;
        subst.
      eapply v_div.
      apply IHHeval1 with (n0:=n);
        auto.
      apply IHHeval2 with (n0:=n);
        auto.

  Qed.

  Lemma eval_raise :
    forall M σ e v n, evaluate M σ e v <->
                      evaluate M σ (e ↑ n) v.
  Proof.
    split.
    * intro Heval.
      induction Heval;
        raise_simpl;
        eauto with exp_db.

    * generalize v n.
      induction e;
        intros;
        auto;
        try solve [raise_simpl;
                   inversion H;
                   subst;
                   eauto with exp_db].

  Qed.

  Lemma exp_subst_raise_lt :
    forall (e : exp) x n m, n < m ->
                       ([x /s n] (e ↑ m)) = (([x /s n] e) ↑ m).
  Proof.
    intro e;
      induction e;
      intros;
      repeat (subst_simpl;
              raise_simpl);
      try solve [try rewrite IHe;
                 try rewrite IHe1;
                 try rewrite IHe2;
                 try rewrite IHe3;
                 repeat (rewrite aval_subst_raise_n);
                 repeat (rewrite map_subst_raise_n);
                 auto].

    * destruct (le_lt_dec m n).
      ** raise_simpl.
         assert (n0 <> n);
           [crush|].
         repeat rewrite ehole_neq_subst;
           [|crush|crush].
         raise_simpl;
           auto.
      ** rewrite ehole_raise_gt;
           auto.
         destruct (eq_dec n0 n);
           subst.
         subst_simpl;
           raise_simpl;
           auto.
         rewrite ehole_neq_subst;
           auto.
         rewrite ehole_raise_gt;
           auto.

  Qed.

  Lemma aval_subst_raise_lt :
    forall (a : a_val) x n m, n < m ->
                         ([x /s n] (a ↑ m)) = (([x /s n] a) ↑ m).
  Proof.
    intros a;
      destruct a;
      intros;
      auto.

    destruct (le_lt_dec m n).
    ** raise_simpl.
       assert (n0 <> n);
         [crush|].
       repeat rewrite ahole_neq_subst;
         [|crush|crush].
       raise_simpl;
         auto.
    ** rewrite ahole_raise_gt;
         auto.
       destruct (eq_dec n0 n);
         subst.
       subst_simpl;
         raise_simpl;
         auto.
       rewrite ahole_neq_subst;
         auto.
       rewrite ahole_raise_gt;
         auto.
  Qed.

  Lemma map_subst_raise_lt :
    forall (p : partial_map name a_val) x n m,
      n < m ->
      ([x /s n] (p ↑ m)) = (([x /s n] p) ↑ m).
  Proof.
    intros.
    apply functional_extensionality;
      intros.
    simpl.
    destruct (p x0);
      simpl;
      auto.
    destruct a;
      simpl;
      auto.
    let H := fresh in
    destruct (lt_eq_lt_dec m n0) as [H|H];
      [destruct H|].

    * assert (Hle : m <= n0);
        [crush|].
      apply leb_correct in Hle;
        rewrite Hle.
      assert (Hneq : n <> S n0);
        [crush
        |apply <- Nat.eqb_neq in Hneq;
         rewrite Hneq].
      assert (Hneq' : n <> n0);
        [crush
        |apply <- Nat.eqb_neq in Hneq';
         rewrite Hneq'].
      rewrite Hle.
      auto.

    * subst.
      rewrite Nat.leb_refl.
      assert (Hneq : n <> n0);
        [crush|].
      apply <- Nat.eqb_neq in Hneq;
        rewrite Hneq.
      assert (Hneq' : n <> S n0);
        [crush|].
      apply <- Nat.eqb_neq in Hneq';
        rewrite Hneq'.
      assert (Heqb : n0 <=? n0 = true);
        [apply leb_correct; auto|rewrite Heqb].
      auto.

    * assert (Hgt : m > n0);
        [auto
        |apply Nat.leb_gt in Hgt;
         rewrite Hgt].
      destruct (Nat.eq_dec n n0) as [|Heq];
        subst.
      ** rewrite Nat.eqb_refl;
           auto.

      ** apply Nat.eqb_neq in Heq;
           rewrite Heq.
         rewrite Hgt.
         auto.
  Qed.

  Lemma asrt_subst_raise_lt :
    forall (A : asrt) x n m,
      n < m ->
      ([x /s n] (A ↑ m)) = (([x /s n] A) ↑ m).
  Proof.
    intros A;
      induction A;
      intros;
      repeat (subst_simpl;
              raise_simpl);
      try solve [raise_simpl;
                 subst_simpl;
                 try rewrite exp_subst_raise_lt;
                 try rewrite IHA;
                 try rewrite IHA1;
                 try rewrite IHA2;
                 repeat (rewrite aval_subst_raise_lt);
                 repeat (rewrite map_subst_raise_lt);
                 crush].

  Qed.

  Lemma raise_value_map :
    forall (m : partial_map name a_val) n,
      (forall x a,  m x = Some a ->
               exists v, a = av_ v) ->
      (m ↑ n) = m.
  Proof.
    intros.
    apply functional_extensionality;
      intros x.
    destruct (partial_maps.partial_map_dec x m).

    * destruct_exists_loo.
      destruct (H x x0) as [v];
        subst;
        auto.
      rewrite H0.
      simpl.
      rewrite H0.
      auto.

    * simpl;
        rewrite e.
      auto.
  Qed.

  Lemma conseq_raise_mutind :
    (forall M σ A, M ◎ σ ⊨ A  -> forall n, M ◎ σ ⊨ (A ↑ n)) /\
    (forall M σ A, M ◎ σ ⊭ A  -> forall n, M ◎ σ ⊭ (A ↑ n)).
  Proof.
    apply sat_mutind;
      intros;
      raise_simpl;
      try solve [repeat a_prop; auto with specw_db];
      try solve [try (apply sat_all);
                 try (apply sat_ex with (x:=x));
                 intros;
                 rewrite asrt_subst_raise_lt;
                 auto;
                 apply Nat.lt_0_succ].

    * apply sat_exp.
      apply exp_sat.
      match goal with
      | [H : exp_satisfaction _ _ _ |- _] =>
        inversion H;
          subst
      end.
      apply eval_raise;
        auto.

    * apply sat_class.
      match goal with
      | [H : has_class _ _ _ _ |- _ ] =>
        inversion H;
          subst
      end.
      match goal with
      | [α : addr |- _ ] =>
        apply has_cls with (α := α)
      end;
        auto.
      apply eval_raise;
        auto.

    * inversion h;
        subst;
        simpl;
        auto with specw_db.

    * inversion m0;
        subst.
      apply sat_call.
      rewrite raise_value_map;
        auto.
      intros.
      simpl in H0.
      destruct (args x0);
        [|crush].
      destruct (lcl n0);
        [|crush].
      inversion H0;
        subst.
      eauto.

    * inversion e;
        subst;
        auto with specw_db.

    * inversion i;
        subst;
        auto with specw_db.

(*)    * apply not_sat_implies_nsat;
        intro Hcontra.
      match goal with
      | [H : _ ◎ _ ⊨ _ |- _] =>
        inversion H;
          subst
      end.
      inversion H2;
        subst.
      auto.*)



  Admitted.

  Lemma conseq_raise :
    (forall M σ A, M ◎ σ ⊨ A  -> forall n, M ◎ σ ⊨ (A ↑ n)).
  Proof.
    destruct conseq_raise_mutind;
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

  Lemma forall_neg_exists :
    forall {A} (P : A -> Prop), ~ (exists a : A, P a) ->
                       (forall a : A, ~ P a).
    intros.
    destruct (excluded_middle (P a));
      auto.
    contradiction H.
    exists a;
      auto.
  Qed.

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
      apply if_ex1;
      intros x;
      subst_simpl
    | [|- _ ⊢ (∃x.[_]) to1 _ onlyIf _ ] =>
      apply if1_ex1;
      intro x;
      subst_simpl
    | [|- _ ⊢ (∃x.[_]) to _ onlyThrough _ ] =>
      apply ot_ex1;
      intro x;
      subst_simpl
    | [ |- _ ] =>
      fail "no top level existential on the left hand side"
    end.

  Lemma change_class_absurd :
    forall M x C, M ⊢ (a_class (e_ x) C) to1 ¬ (a_class (e_ x) C) onlyIf (a_false).
  Proof.
    intros.
    apply if1_if.
    apply if_class.
  Qed.

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

