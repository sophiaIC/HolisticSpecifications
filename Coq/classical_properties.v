Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Theorem prop_and_if_sat_and :
  (forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ (a_and A1 A2) ->
                    M1 ⦂ M2 ◎ σ ⊨ A1 /\
                    M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros M1 M2 σ A1 A2 Hsat;
    inversion Hsat;
    auto.
Qed.

Theorem prop_or_if_nsat_and :
  (forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ (a_and A1 A2) ->
                    M1 ⦂ M2 ◎ σ ⊭ A1 \/
                    M1 ⦂ M2 ◎ σ ⊭ A2).
Proof.
  intros M1 M2 σ A1 A2 Hnsat;
    inversion Hnsat;
    auto.
Qed.

Theorem sat_implies_not_nsat_mutind :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                ~ M1 ⦂ M2 ◎ σ ⊭ A) /\

  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                ~ M1 ⦂ M2 ◎ σ ⊨ A).
Proof.
  apply sat_mutind;
    intros;
    intros Hcontra.

  (** Case 1: sat_exp *)
  try solve [inversion Hcontra; crush].

  (** Case 2: sat_eq*)
  inversion Hcontra; subst;
      eval_rewrite;
      crush;
      eauto.

  (** Case 3: sat_class *)
  inversion Hcontra; subst; 
    [eval_rewrite;
     crush|crush; eauto].

  (** Case 4: sat_set *)
  inversion Hcontra; subst;
    interpretation_rewrite;  crush; eauto.

  (** Case 5: sat_and *)  
  try solve [inversion Hcontra; crush].

  (** Case 6: sat_or1 *)  
  try solve [inversion Hcontra; crush].

  (** Case 7: sat_or2 *)  
  try solve [inversion Hcontra; crush].

  (** Case 8: sat_arr1 *)  
  try solve [inversion Hcontra; crush].

  (** Case 9: sat_arr2 *)
  try solve [inversion Hcontra; crush].

  (** Case 10: sat_neg *)
  try solve [inversion Hcontra; crush].

  (** Case 11: sat_all_x *)
  inversion Hcontra; subst;
    contradiction (H y v) with (z:=z);
    auto.

  (** Case 12: sat_ex_x *)
  inversion Hcontra; subst;
    contradiction H; eauto.

  (** Case 13: sat_access1 *)
  inversion Hcontra; subst;
    contradiction (H1 α α); auto.

  (** Case 14: sat_access2 *)
  inversion Hcontra; subst;
    contradiction (H5 α' α α f o); auto.

  (** Case 15: sat_access3 *)
  inversion Hcontra; subst.
  destruct H6 as [Hcontra'|Hcontra'];
    [contradiction (Hcontra' α1 α1); auto
    |contradiction (Hcontra' z α2 i1 i2 ψ ϕ χ s);
     auto].

  (** Case 16: sat_call *)
  inversion Hcontra; subst;
    interpretation_rewrite.
  simpl in H4;
    symmetry in H4;
    inversion H4;
    subst.
  destruct (H7 x' y' s) as [Ha Hb].
  contradiction (Hb (v_addr αy) (v_addr αy)); auto.
  destruct (H7 x' y' s) as [Ha Hb];
    destruct Hb as [x'' Hb];
    destruct Hb as [v1 Hb];
    destruct Hb as [v2 Hb];
    andDestruct.
  simpl in H4;
    symmetry in H4;
    inversion H4;
    subst.
  rewrite Ha in e0;
    inversion e0;
    subst.
  apply compose_v_to_av_equality in H6;
    subst.
  destruct (e1 x'' v1) as [v2'];
    auto;
    andDestruct.
  destruct Hb0 as [v'];
    andDestruct.
  rewrite Ha2 in Ha1;
    inversion Ha1;
    subst.
  contradiction (Hb v' v');
    auto.

  (* external *)
  inversion Hcontra;
    interpretation_rewrite;
    subst;
    crush.
  contradiction (H3 α).

  (* internal *)
  inversion Hcontra;
    interpretation_rewrite;
    subst;
    crush.
  contradiction (H3 α).

  (* in *)
  inversion Hcontra;
    subst.
  restriction_rewrite;
    crush.

  (* next *)
  inversion Hcontra;
    subst.
  inversion H1; subst.
  
  
Admitted.

Theorem sat_implies_not_nsat :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
(*                σ_wf σ ->*)
                ~ M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
  destruct sat_implies_not_nsat_mutind; crush.
Qed.

Theorem nsat_implies_not_sat :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
(*                σ_wf σ ->*)
                ~ M1 ⦂ M2 ◎ σ ⊨ A).
Proof.
  destruct sat_implies_not_nsat_mutind; crush.
Qed.

Lemma sat_excluded_middle :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ A) \/ (M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
Admitted.

Lemma arr_true :
  forall M1 M2 σ A1 A2,
    M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2) ->
    M1 ⦂ M2 ◎ σ ⊨ A1 ->
    M1 ⦂ M2 ◎ σ ⊨ A2.
Proof.
  intros M1 M2 σ A1 A2 Hsat;
    inversion Hsat;
    subst;
    intros;
    auto.

  apply sat_implies_not_nsat_mutind in H3;
    crush.
Qed.

Lemma arr_false :
  forall M1 M2 σ A1 A2,
    M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2) ->
    M1 ⦂ M2 ◎ σ ⊭ A2 ->
    M1 ⦂ M2 ◎ σ ⊭ A1.
Proof.
  intros M1 M2 σ A1 A2 Hsat;
    inversion Hsat;
    subst;
    intros;
    auto.

  apply sat_implies_not_nsat_mutind in H3;
    crush.
Qed.

Lemma and_iff :
  forall M1 M2 σ A1 A2, (M1 ⦂ M2 ◎ σ ⊨ (A1 ∧ A2)) <->
                   (M1 ⦂ M2 ◎ σ ⊨ A1 /\ M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto.
Qed.

Lemma or_iff :
  forall M1 M2 σ A1 A2, (M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)) <->
                   (M1 ⦂ M2 ◎ σ ⊨ A1 \/ M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto.
Qed.

(*Lemma universal_arr_true :
  (forall M1 M2 σ A,
      arising M1 M2 σ ->
      M_wf M1 ->
      M1 ⦂ M2 ◎ σ ⊨ A ->
      forall A', M1 ⦂ M2 ◎ σ ⊨ A ->
            M1 ⊨m (A ⇒ A') ->
            M1 ⦂ M2 ◎ σ ⊨ A').
Proof.
  intros.
  unfold mdl_sat in H3.
  apply H3 in H;
    auto.
  eapply arr_true; eauto.
  inversion H;
    subst.
  SearchAbout config_wf.
  eapply initial_heap_wf in H4;
    eauto.
  apply 
  inversion H3;
    subst.
  
  

  apply sat_arr1.
  
  intros M1 M2 σ A Hsat;
    induction Hsat;
    intros;
    eauto.

  
Qed.*)

Lemma negate_elim_sat :
  (forall A M1 M2 σ, M1 ⦂ M2 ◎ σ ⊨ (¬ ¬ A) ->
                M1 ⦂ M2 ◎ σ ⊨ A).
Proof.
  intros;
    auto.
  inversion H;
    subst.
  inversion H4;
    auto.
Qed.

Lemma negate_elim_nsat :
  (forall A M1 M2 σ, M1 ⦂ M2 ◎ σ ⊭ (¬ ¬ A) ->
                M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
  intros;
    auto.
  inversion H;
    subst.
  inversion H4;
    auto.
Qed.

Lemma negate_intro_sat :
  (forall A M1 M2 σ, M1 ⦂ M2 ◎ σ ⊨ A ->
                M1 ⦂ M2 ◎ σ ⊨ (¬ ¬ A)).
Proof.
  intros;
    auto.
Qed.

Lemma negate_intro_nsat :
  (forall A M1 M2 σ, M1 ⦂ M2 ◎ σ ⊭ A ->
                M1 ⦂ M2 ◎ σ ⊭ (¬ ¬ A)).
Proof.
  intros;
    auto.
Qed.