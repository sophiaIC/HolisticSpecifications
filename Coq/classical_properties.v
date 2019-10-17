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

Theorem sat_nsat_not_mutind :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
(*                σ_wf σ ->*)
                ~ M1 ⦂ M2 ◎ σ ⊭ A) /\

  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
(*                σ_wf σ ->*)
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
    interpretation_rewrite; crush; eauto.

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
  contradiction (Hb v v); auto.
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

  
Admitted.

Lemma sat_excluded_middle :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ A) \/ (M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
Admitted.