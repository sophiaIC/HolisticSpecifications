Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** Properties of Linking *)
Lemma moduleLinking_associative :
  forall M1 M2 M12, M1 ⋄ M2 ≜ M12 ->
               forall M3 M23, M2 ⋄ M3 ≜ M23 ->
                         forall M M', M12 ⋄ M3 ≜ M ->
                                 M1 ⋄ M23 ≜ M' ->
                                 M = M'.
Proof.
  intros.
  inversion H;
    inversion H0;
    inversion H1;
    inversion H2;
    subst.

  apply functional_extensionality;
    intro C.
  remember (M1 C) as res1;
    remember (M2 C) as res2;
    remember (M3 C) as res3.
  destruct res1 as [CDef1|];
    destruct res2 as [CDef2|];
    destruct res3 as [CDef3|];
    unfold extend;
    rewrite <- Heqres1;
    auto.
Qed.

Lemma moduleLinking_commutative_1 :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             M_wf M1 ->
             M_wf M2 ->
             M2 ⋄ M1 ≜ M.
Proof.
  intros.
  inversion H;
    subst.

  assert (Hrewrite : extend M1 M2 = extend M2 M1);
    [|rewrite Hrewrite; apply m_link; eauto].
  
  apply functional_extensionality;
    intro C.
  unfold extend.
  remember (M1 C) as r1;
    remember (M2 C) as r2;
    destruct r1 as [def1|];
    destruct r2 as [def2|];
    eauto.
  destruct (eq_dec C ObjectName) as [|Hneq];
    [subst|].
  inversion H0;
    inversion H1;
    subst;
    crush.

  rewrite H2 with (def:=def1) in Heqr2;
    crush.
Qed.

Lemma moduleLinking_commutative_2 :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             forall M', M2 ⋄ M1 ≜ M' ->
                   M_wf M1 ->
                   M_wf M2 ->
                   M = M'.
Proof.
  intros.
  inversion H;
    inversion H0;
    subst.

  apply functional_extensionality;
    intros C.
  unfold extend.
  remember (M1 C) as res1;
    remember (M2 C) as res2.
  destruct res1 as [CDef1|];
    destruct res2 as [CDef2|];
    auto.
  destruct (eq_dec C ObjectName) as [|Hneq];
    [subst|].
  inversion H1;
    inversion H2;
    subst.
  rewrite <- Heqres1 in H5;
    rewrite <- Heqres2 in H11.
  inversion H5;
    inversion H11;
    auto.
  symmetry in Heqres1;
    apply H9 in Heqres1.
  rewrite Heqres1 in Heqres2;
    crush.
  apply H3 in Heqres1;
    auto.
Qed.

Lemma linking_preserves_reduction :
  forall M1 σ1 σ2, M1 ∙ σ1 ⤳ σ2 ->
              forall M2 M, M1 ⋄ M2 ≜ M ->
                      M ∙ σ1 ⤳ σ2.
Proof.
  intros M1 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    eauto with loo_db.

  - eapply r_mth;
      eauto.
    inversion H9;
      subst;
      unfold extend in *;
      eauto.
    rewrite H4;
      auto.

  - eapply r_new;
      eauto.
    inversion H9;
      unfold extend in *;
      subst;
      eauto.
    rewrite H3;
      auto.
Qed.

(*Lemma linking_preserves_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M3 M', M1 ∘ M3 ≜ M' ->
                          forall M4 M'', M2 ∘ M4 ≜ M'' ->
                                    M_wf M1 ->
                                    M_wf M2 ->
                                    M_wf M3 ->
                                    M_wf M4 ->
                                    (exists M''', M' ∘ M'' ≜ M''') ->
                                    M' ⦂ M'' ⦿ σ1 ⤳… σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
  inversion H3;
    inversion H4;
    subst.
  destruct H9 as [M'''].
  apply pr_single with (M:=M''');
    intros;
    eauto.
  inversion H9;
    subst.
  apply linking_preserves_reduction
    with (M1:=extend M1 M2)
         (M2:=extend M3 M4);
    auto.
  inversion H;
    subst;
    auto.
  assert (Hrewrite : extend (extend M1 M2) (extend M3 M4) = extend (extend M1 M3) (extend M2 M4));
    [|rewrite <- Hrewrite; auto; apply m_link; intros].
  apply functional_extensionality;
    intros C.
  remember (M1 C) as res1;
    remember (M2 C) as res2;
    remember (M3 C) as res3;
    remember (M4 C) as res4.
  destruct (eq_dec C ObjectName) as [|Hneq];
    [subst C
    |].
  unfold extend;
    destruct res1 as [Cdef1|];
    destruct res2 as [Cdef2|];
    destruct res3 as [Cdef3|];
    destruct res4 as [Cdef4|];
    rewrite <- Heqres1;
    try rewrite <- Heqres2;
    try rewrite <- Heqres3;
    try rewrite <- Heqres4;
    auto.

  inversion H5; subst; crush.
  rewrite Heqres2, Heqres3;
    inversion H6;
    inversion H7;
    subst.
  rewrite H14, H19;
    auto.

  unfold extend;
    destruct res1 as [Cdef1|];
    destruct res2 as [Cdef2|];
    destruct res3 as [Cdef3|];
    destruct res4 as [Cdef4|];
    rewrite <- Heqres1;
    try rewrite <- Heqres2;
    try rewrite <- Heqres3;
    try rewrite <- Heqres4;
    auto.
  assert (Hclass : extend M1 M3 C = Some Cdef3);
    [unfold extend; rewrite <- Heqres1; auto|].
  apply H12 in Hclass;
    auto;
    unfold extend in Hclass;
    rewrite <- Heqres2 in Hclass;
    crush.
  assert (Hclass : extend M1 M3 C = Some Cdef3);
    [unfold extend; rewrite <- Heqres1; auto|].
  apply H12 in Hclass;
    auto;
    unfold extend in Hclass;
    rewrite <- Heqres2 in Hclass;
    crush.

  unfold extend in H17;
    remember (M1 C) as res1;
    destruct res1 as [Cdef1|].
  assert (M3 C = None);
    [apply H10 with (def:=Cdef1); eauto|].
  remember (M4 C) as res4;
    destruct res4 as [Cdef4|];
    symmetry in Heqres4.
  assert (Htmp : extend M1 M3 C = Some Cdef1);
    [unfold extend; rewrite <- Heqres1; auto|apply H12 in Htmp; auto].
  unfold extend in Htmp.
  rewrite Heqres4 in Htmp.
  destruct (M2 C);
    crush.
  unfold extend;
    crush.
  assert (M4 C = None);
    [apply H15 with (def:=def); auto| ].
  assert (extend M1 M3 C = None);
    [apply H13 with (def:= def); unfold extend; auto; rewrite H17; auto
    |].
  unfold extend in H19;
    rewrite <- Heqres1 in H19.
  unfold extend; rewrite H19, H18;
    auto.
  admit.
  admit.

  apply H2 in H12;
    destruct H12 as [def];
    exists def;
    unfold extend;
    crush.

  destruct H8 as [M'''].
  eapply pr_trans with (M:=M''');
    eauto.
  inversion H8;
    subst;
    auto.
  inversion H;
    subst.
  
  
Abort.*)
