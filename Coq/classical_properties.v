Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import function_operations.
Require Import sbst.
Require Import List.
Require Import String.
Open Scope string_scope.
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

(** Lemma 5: Classical (4) *)
(** This is yet to be proven. *)
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

  (** Case 13: sat_all_Σ*)
  inversion Hcontra;
    subst.
  apply H in H1; crush.

  (** Case 13: sat_ex_Σ*)
  inversion Hcontra;
    subst.
  apply H4 in e;
    crush.

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
  admit.

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
  
  (* will *)
  
  
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

(** Lemma 5: Classical (1) *)
(** Yet to be proven *)
Lemma sat_excluded_middle :
  forall M1 M2 σ A, (M1 ⦂ M2 ◎ σ ⊨ A) \/ (M1 ⦂ M2 ◎ σ ⊭ A).
Proof.
Admitted.


(** Lemma 5: Classical (5) *)
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

Lemma arr_prop1 :
  forall M1 M2 σ A1 A2,
    (M1 ⦂ M2 ◎ σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ ⊨ A2) ->
    M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2).
Proof.
  intros.
  destruct sat_excluded_middle
    with (M1:=M1)(M2:=M2)
         (σ:=σ)(A:=A1);
    auto with chainmail_db.
Qed.

Lemma arr_prop2 :
  forall M1 M2 σ A1 A2,
    M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2) ->
    (M1 ⦂ M2 ◎ σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros.
  eapply arr_true; eauto.
Qed.

Lemma arr_prop :
  forall M1 M2 σ A1 A2,
    M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2) <->
    (M1 ⦂ M2 ◎ σ ⊨ A1 ->
     M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    split;
    [apply arr_prop2|apply arr_prop1].
Qed.

Lemma all_x_prop :
  forall M1 M2 σ A,
    M1 ⦂ M2 ◎ σ ⊨ (∀x∙A) <->
    (forall y v, mapp σ y = Some v ->
            forall z, fresh_x_σ z σ A ->
                 M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊨ ([z /s 0]A)).
Proof.
  intros; split; eauto with chainmail_db; intros.
  inversion H;
    subst;
    eauto.
Qed.

Lemma ex_x_prop :
  forall M1 M2 σ A,
    M1 ⦂ M2 ◎ σ ⊨ (∃x∙A) <->
    (exists y v z, mapp σ y = Some v /\
              fresh_x_σ z σ A /\
              M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊨ ([z /s 0] A)).
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
  forall M1 M2 σ A1 A2, (M1 ⦂ M2 ◎ σ ⊨ (A1 ∧ A2)) <->
                   (M1 ⦂ M2 ◎ σ ⊨ A1 /\ M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto with chainmail_db.
Qed.

(** Lemma 5: Classical (3) *)
Lemma or_iff :
  forall M1 M2 σ A1 A2, (M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)) <->
                   (M1 ⦂ M2 ◎ σ ⊨ A1 \/ M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    split;
    intros Ha;
    inversion Ha;
    eauto with chainmail_db.
Qed.

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
    auto with chainmail_db.
Qed.

Lemma negate_intro_nsat :
  (forall A M1 M2 σ, M1 ⦂ M2 ◎ σ ⊭ A ->
                M1 ⦂ M2 ◎ σ ⊭ (¬ ¬ A)).
Proof.
  intros;
    auto with chainmail_db.
Qed.

Lemma will_arr :
  forall M1 M2 σ A1 A2,
    M1 ⦂ M2 ◎ σ ⊨ a_will(A1 ⇒ A2 ∧ A1) ->
    M1 ⦂ M2 ◎ σ ⊨ a_will(A2).
Proof.
  intros.
  inversion H;
    subst.
  inversion H7;
    subst;
    eauto.
  apply sat_will
    with (ϕ:=ϕ)(ψ:=ψ)(χ:=χ)(σ':=σ')(σ'':=σ'');
    auto.
  eapply arr_true;
    eauto.
Qed.

Inductive entails : asrt -> asrt -> Prop :=
| ent : forall A1 A2, (forall χ ϕ ψ M1 M2, M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A1 ->
                                 M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2) ->
                 entails A1 A2.

Definition equiv_a (A1 A2 : asrt): Prop :=
  (entails A1 A2) /\ (entails A2 A1).

Lemma sat_and_nsat_entails_false :
  forall A, entails (A ∧ ¬ A) (a_exp (e_false)).
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
  forall A, entails (a_exp (e_false)) (A ∧ ¬ A).
Proof.
  intros.
  apply ent;
    intros.

  inversion H;
    subst.
  inversion H4.
Qed.

Hint Resolve false_entails_sat_and_nsat : chainmail_db.

(** Lemma 6: (1) *)
Lemma sat_and_nsat_equiv_false :
  forall A, equiv_a (A ∧ ¬ A) (a_exp (e_false)).
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
    inversion H4;
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
    inversion H4;
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
    inversion H5;
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
    inversion H4;
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
    inversion H4;
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
    inversion H5;
    inversion H6;
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
    inversion H4;
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
    inversion H4;
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
    inversion H4;
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
    inversion H5;
    inversion H6;
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

Lemma fresh_not_1 :
  forall x ϕ A, fresh_x x ϕ A ->
           fresh_x x ϕ (¬ A).
Proof.
  intros.
  inversion H;
    subst.
  apply frsh;
    eauto with chainmail_db.
Qed.

Hint Resolve fresh_not_1 : chainmail_db.

Lemma fresh_not_2 :
  forall x ϕ A, fresh_x x ϕ (¬ A) ->
           fresh_x x ϕ A.
Proof.
  intros.
  inversion H;
    subst.
  inversion H1;
    subst.
  apply frsh;
    eauto.
Qed.

Hint Resolve fresh_not_2 : chainmail_db.

Lemma fresh_not_σ_1 :
  forall x σ A, fresh_x_σ x σ A ->
           fresh_x_σ x σ (¬ A).
Proof.
  intros.
  inversion H;
    subst;
    repeat destruct_exists_loo;
    andDestruct;
    subst;
    eauto.
  apply fresh_x_ϕ_implies_σ;
    auto with chainmail_db.
Qed.

Hint Resolve fresh_not_σ_1 : chainmail_db.

Lemma fresh_not_σ_2 :
  forall x σ A, fresh_x_σ x σ (¬ A) ->
           fresh_x_σ x σ A.
Proof.
  intros.
  unfold fresh_x_σ in *;
    repeat destruct_exists_loo;
    andDestruct;
    subst.
  eexists.
  eexists.
  eexists.
  split; eauto with chainmail_db.
Qed.

Hint Resolve fresh_not_σ_2 : chainmail_db.

Lemma not_ex_x_all_not_1 : 
  forall A, entails (¬(∃x∙A)) (∀x∙¬A).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.
  inversion H4;
    subst.

  apply sat_all_x;
    intros.
  apply sat_not.
  eapply H5; eauto with chainmail_db.
  
  
Qed.

Hint Resolve not_ex_x_all_not_1 : chainmail_db.

Lemma not_ex_x_all_not_2 : 
  forall A, entails (∀x∙¬A) (¬(∃x∙A)).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.

  apply sat_not.
  apply nsat_ex_x;
    intros.
  eapply H4 in H0;
    eauto with chainmail_db.

  inversion H0;
    eauto with chainmail_db.
Qed.

Hint Resolve not_ex_x_all_not_2 : chainmail_db.

(** Lemma 6: (10) *)
Lemma not_ex_x_all_not : 
  forall A, equiv_a (¬(∃x∙A)) (∀x∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_ex_x_all_not : chainmail_db.

Lemma not_all_x_ex_not_1 : 
  forall A, entails (¬(∀x∙A)) (∃x∙¬A).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.
  inversion H4;
    subst.

  apply sat_ex_x with (z:=z)(y:=y)(v:=v);
    auto with chainmail_db;
    sbst_simpl.
  
  apply sat_not; auto.
Qed.

Hint Resolve not_all_x_ex_not_1 : chainmail_db.

Lemma not_all_x_ex_not_2 : 
  forall A, entails (∃x∙¬A) (¬(∀x∙A)).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    subst.

  apply sat_not.
  apply nsat_all_x with (y:=y)(z:=z)(v:=v);
    auto with chainmail_db;
    sbst_simpl.
  inversion H6; subst; auto.
Qed.

Hint Resolve not_all_x_ex_not_2 : chainmail_db.

Lemma not_all_x_ex_not : 
  forall A, equiv_a (¬(∀x∙A)) (∃x∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_all_x_ex_not : chainmail_db.

Lemma not_ex_Σ_all_not_1 : 
  forall A, entails (¬(∃S∙A)) (∀S∙¬A).
Proof.
  intros;
    apply ent;
    intros.
  apply sat_all_Σ;
    intros.
  inversion H;
    subst.
  inversion H5;
    subst.
  apply H6 in H0.
  apply sat_not;
    eauto.
Qed.

Hint Resolve not_ex_Σ_all_not_1 : chainmail_db.

Lemma not_ex_Σ_all_not_2 : 
  forall A, entails (∀S∙¬A) (¬(∃S∙A)).
Proof.
  intros;
    apply ent;
    intros.
  inversion H;
    subst.
  apply sat_not, nsat_ex_Σ;
    intros.
  apply H4 in H0.
  inversion H0;
    subst;
    eauto.
Qed.

Hint Resolve not_ex_Σ_all_not_2 : chainmail_db.

(** Lemma 6: (11) *)
Lemma not_ex_Σ_all_not : 
  forall A, equiv_a (¬(∃S∙A)) (∀S∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_ex_Σ_all_not : chainmail_db.

Lemma not_all_Σ_ex_not_1 : 
  forall A, entails (¬(∀S∙A)) (∃S∙¬A).
Proof.
  intros;
    apply ent;
    intros.
  inversion H;
    subst.
  inversion H4;
    subst.
  eapply sat_ex_Σ;
    intros;
    eauto.
  apply sat_not;
    eauto.
Qed.

Hint Resolve not_all_Σ_ex_not_1 : chainmail_db.

Lemma not_all_Σ_ex_not_2 : 
  forall A, entails (∃S∙¬A) (¬(∀S∙A)).
Proof.
  intros;
    apply ent;
    intros.
  inversion H;
    subst.
  eapply sat_not, nsat_all_Σ;
    eauto.
  inversion H5;
    eauto.
Qed.

Hint Resolve not_all_Σ_ex_not_2 : chainmail_db.

(** Lemma 6: (13) *)
Lemma not_all_Σ_ex_not : 
  forall A, equiv_a (¬(∀S∙A)) (∃S∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto with chainmail_db.
Qed.

Hint Resolve not_all_Σ_ex_not : chainmail_db.

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

Lemma entails_implies :
  forall M1 M2 χ ϕ ψ A1, M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A1 ->
                    forall A2, entails A1 A2 ->
                          M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2.
Proof.
  intros.
  inversion H0;
    auto.
Qed.

Hint Resolve entails_implies : chainmail_db.
Hint Rewrite entails_implies : chainmail_db.

Ltac sat_destruct :=
  match goal with
  | [Hand : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply and_iff in Hand;
                                       destruct Hand
  end.

Ltac frsh_auto :=
  match goal with
  | [Hfrsh : fresh_x _ _ (_ ∧ _) |- _] => apply fresh_and_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (_ ⇒ _) |- _] => apply fresh_arr_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (∀x∙ _) |- _] => apply fresh_all_elim in Hfrsh
  | [ |- fresh_x _ _ (_ ∧ _)] => apply fresh_and_intro
  | [ |- fresh_x _ _ (_ ⇒ _)] => apply fresh_arr_intro
  | [ |- fresh_x _ _ (∀x∙_)] => apply fresh_all_intro
  | [ Hfrsh : fresh_x ?x ?σ _ |- fresh_x ?x ?σ _] => auto; try (eapply fresh_notin; eauto)
  end.

Ltac a_intro :=
  match goal with
  | [|- _ ⦂ _ ◎ _ ⊨ (∀x∙ _)] => apply sat_all_x; intros; sbst_simpl
  | [|- _ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] => apply arr_prop1; intros; sbst_simpl
  end.

Ltac a_intros :=
  repeat a_intro.

Ltac a_prop :=
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> and_iff in H;
                                           destruct H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∨ _) |- _] => apply -> or_iff in H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ⇒ _) |- _] => rewrite -> arr_prop in H
         | [H : context[_ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] |- _] => rewrite -> arr_prop in H
         | [H : _ ⦂ _ ◎ _ ⊨ (∀x∙_) |- _] => rewrite all_x_prop in H; sbst_simpl
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∧ _)] => apply sat_and
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∨ _)] => apply <- or_iff
         | [H : entails ?A1 ?A2,
                Ha : ?M1 ⦂ ?M2 ◎ (?χ, ?ϕ::?ψ) ⊨ ?A1 |- _] =>
           notHyp (M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2);
           let H' := fresh in 
           assert (H' : M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2);
           [apply (entails_implies M1 M2 χ ϕ ψ A1 Ha A2 H); eauto|]
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ?A,
                 Hb : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ¬ ?A |- _] =>
           apply sat_implies_not_nsat in Ha
         | [Ha : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ¬ ?A,
                 Hb : ~ ?M1 ⦂ ?M2 ◎ ?σ ⊭ ?A |- _] =>
           inversion Ha; subst; crush
         end.

Lemma and_forall_x_entails_1 :
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

(*Lemma prev_disj_1 :
  forall A1 A2, entails (a_prev (A1 ∨ A2))
                   ((a_prev A1) ∨ (a_prev A2)).
Proof.
  intros.
  apply ent;
    intros.
  destruct (sat_excluded_middle M1 M2 (χ, ϕ::ψ) (a_prev A1));
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

Qed.*)

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

(*Lemma was_not_disj :
  forall A1 A2, entails (a_was (A1 ∨ A2) ∧ (a_was (¬ A1)))
                   (a_was A2).
Proof.
  intros;
    apply ent;
    intros.

  a_prop.
  apply sat_was;
    intros.
  inversion H; subst.
  specialize (H6 σ0 H1).
  destruct H6 as [σ'];
    exists σ';
    intros.
  specialize (H2 H3 H4 σ'' H5);
    a_prop.
  destruct H2; auto.
  inversion H0; subst.
  specialize 
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
  assert (Hasrt : M1 ⦂ M2 ◎ (χ, ϕ :: ψ) ⊨ a_will A2);
    [apply (entails_implies (a_will (A1 ∨ A2) ∧ (¬ a_will A1)) (a_will A2));
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

Hint Resolve will_disj_equiv : chainmail_db.*)

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

Lemma exists_adaptation :
  forall σ1 σ2, σ_wf σ1 ->
           σ_wf σ2 ->
           exists σ, σ1 ◁ σ2 ≜ σ.
Proof.
  
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
Qed.

Print pair_reductions.

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

Inductive reductions : mdl -> config -> config -> Prop :=
| red_single : forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                          reductions M σ1 σ2
| red_trans : forall M σ1 σ2 σ3, reductions M σ1 σ2 ->
                            M ∙ σ2 ⤳ σ3 ->
                            reductions M σ1 σ3.

Hint Constructors reductions : loo_db.

Lemma list_does_not_contain_itself :
  forall {A : Type} (l : list A) a,
    a :: l = l ->
    False.
Proof.
  intros A l;
    induction l;
    intros;
    crush.
Qed.

Inductive substmt : stmt -> stmt -> Prop :=
| sub_eq1 : forall s s', substmt s (s_stmts s s')
| sub_eq2 : forall s s', substmt s (s_stmts s' s)
| sub_trns1 : forall s s1 s2, substmt s s1 ->
                         substmt s (s_stmts s1 s2)
| sub_trns2 : forall s s1 s2, substmt s s2 ->
                         substmt s (s_stmts s1 s2).

Hint Constructors substmt : loo_db.

Parameter stmt_not_strict_substatement_of_itself :
  forall s s', substmt s s' ->
          s = s' ->
          False.

Lemma acyclic_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intro Hcontra;
    subst.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    apply list_does_not_contain_itself in H8; auto.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H7 in H1;
      simpl in *.
    inversion H1; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H8 in H0;
      simpl in *.
    inversion H0; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    rewrite <- H7 in H1;
      simpl in *.
    inversion H1; subst.
    eapply stmt_not_strict_substatement_of_itself;
      eauto with loo_db.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    eapply list_does_not_contain_itself; eauto.

  - match goal with
    | [H : (_, _) = (_, _) |- _] =>
      inversion H; subst;
        simpl in *
    end.
    eapply list_does_not_contain_itself; eauto.
Qed.

Hint Resolve acyclic_reduction : loo_db.

Lemma acyclic_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             σ2 <> σ1.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred.

  - eauto with loo_db.

  - intro Hcontra;
      subst.
  
Admitted.

Lemma acyclic_pair_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ1 <> σ2.
Proof.
Admitted.

Lemma pair_reductions_path_unique :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall σ, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ ->
                      M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                      False.
Proof.
Admitted.

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
    destruct (exists_adaptation σ0 σ) as [someσ Hadapt];
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
    match goal with
    | [H : _ = _ :: _ |- _] =>
      inversion H; subst
    end;
    simpl in *;
    subst.
  unfold update, t_update in H2.
  eq_auto.
  eapply int_x;
    simpl;
    eauto with loo_db.
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
    match goal with
    | [H : _ = _ :: _ |- _] =>
      inversion H; subst
    end;
    simpl in *;
    subst.
  unfold update, t_update in H0.
  apply equal_f with (x0:=x) in H0.
  eq_auto.
  eapply int_x;
    simpl;
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
  match goal with
  | [H : _::_ = _::_ |- _] =>
    inversion H; subst
  end.
  eapply int_x;
    simpl;
    eauto with loo_db.
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
    subst;
    repeat map_rewrite;
    eq_auto.
  - apply fresh_heap_none in H1; crush.
  - crush.
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
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    try solve [left; repeat eexists; eauto with loo_db];
    try solve [right; left; repeat eexists; eauto with loo_db];
    try solve [right; right; repeat eexists; eauto with loo_db].

  - subst.
    apply class_of_same_variable_map
      with
        (χ:=χ)(ϕ:=frm (update x v (vMap ϕ)) (c_stmt s))
        (ψ:=ψ)(ϕ':=update_ϕ_map ϕ x v)(ψ':=ψ)
      in H9;
      auto.
    assert (Htmp : (χ, update_ϕ_map ϕ x v :: ψ) = update_σ_map (χ, ϕ::ψ) x v);
      [auto|rewrite Htmp in H9].
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

  destruct (wf_config_this_has_class σ H0) as [C].
  assert (Hwf : σ_wf σ');
    [eapply reduction_preserves_config_wf; eauto|].
  destruct (wf_config_this_has_class σ' Hwf) as [C'].
  repeat match goal with
         | [Ha : forall _ : cls, classOf this ?σ _ -> _,
              Hb : classOf this ?σ ?C |- _] =>
           specialize (Ha C Hb)
         end.
  eapply reduction_different_classes_implies_method_call_or_rtrn; eauto.
  intro Hcontra;
    subst;
    crush.
Qed.

Lemma pair_reduction_change_implies_method_call :
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
Qed.

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
      repeat map_rewrite;
      eq_auto.
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

Notation "'a♢' n" := (a_hole n)(at level 40).
Notation "'e♢' n" := (e_hole n)(at level 40).
Notation "'a_' x" := (a_bind x)(at level 40).
Notation "'e_' x" := (e_var x)(at level 40).
Notation "e1 '⩦' e2" := (a_eq e1 e2)(at level 40).

Definition guards (x y : a_var) : asrt :=
  match x, y with
  | a_ x', a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a_ x', a♢ n => (∀x∙((¬ ((a♢ 0) access (a♢ (S n)))) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a♢ n, a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  | a♢ n, a♢ m => (∀x∙((¬ ((a♢ 0) access (a♢ (S m)))) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  end.

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

Print σ_wf.

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

Hint Resolve not_stuck_adaptation.

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

Lemma guards_method_call :
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
        (ϕ:=frm ((f ∘ β') ∪ β)
                (c_stmt (s_stmts (s_meth (❲ f' ↦ x0 ❳) (❲ f' ↦ x1 ❳) m (❲ f' ↦ vMap ❳)) (❲ f' ↦ s ❳))))
      as [α H];
      auto.
    +  apply (wf_adaptation)
         with
           (σ1:= (χ1, (frm β c) :: nil))
           (σ2:= (χ', (frm β' (c_stmt (s_stmts (s_meth x0 x1 m vMap) s))) :: ψ'));
         auto.
       * eapply pair_reductions_preserves_config_wf;
           eauto.
       * intros.
         eapply pair_reductions_heap_monotonic; eauto.

    + destruct_exists_loo; andDestruct.
      exists (❲ f' ↦ x1 ❳), m, (❲ f' ↦ vMap ❳ ∘ v_to_av).
      eapply sat_call
        with (χ:=χ')(ψ:=ψ')
             (x':=❲ f' ↦ x0 ❳)
             (y':=❲ f' ↦ x1 ❳)
             (vMap':=❲ f' ↦ vMap ❳)
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

Admitted.

Module ExposeExample.

  (** #<h3># Safe example: #</h3># *)
  (** ---------------------------------------------------- *)
  (** #<code># >MyModule = { #</code># *)
  (** #<code># >  Inside = {} #</code># *)
  (** #<code># >  Boundary = { #</code># *)
  (** #<code># >    field inside : Inside #</code># *)
  (** #<code># >    meth expose() = {return this.inside} #</code># *)
  (** #<code># >  } #</code># *)
  (** #<code># >} #</code># *)
  (** --------------------------------------------------- *)
  (** #<code># we want to prove: #</code># *)
  (**  *)
  (** #<code># >MyModule ⊨  #</code># *)
  (** #<code># >(∀ b, b : Boundary, ∀ i, (b.inside = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
  (** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
  (** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
  (**  *)
  (**  *)

  (** Inside Definition  *)

  Definition Inside := classID 6.

  Definition InsideDef := clazz Inside
                                nil
                                empty
                                empty.

  (** Boundary Definition *)

  Definition Boundary := classID 7.

  Definition inside := fieldID 0.

  Definition expose := methID 0.

  Definition x := bnd 10.

  Definition exposeBody := s_stmts (s_asgn (r_var x) (r_fld this inside))
                                   (s_rtrn x).

  Definition BoundaryDef := clazz Boundary
                                  (inside :: nil)
                                  (update
                                     expose (nil, exposeBody)
                                     empty)
                                  empty.

  (** MyModule Definition *)

  Definition MyModule := (update
                            Boundary BoundaryDef
                            (update
                               Inside InsideDef
                               empty)).


  Theorem expose_example_will :
    MyModule ⊨m (∀x∙∀x∙(((a_class (e♢1) Boundary)
                         ∧
                         ((e_acc_f (e♢1) inside) ⩦ (e♢0))
                         ∧
                         ((guards (a♢1) (a♢0))))
                        ∧
                        (a_will (¬ guards (a♢1) (a♢0)))
                          ⇒
                          (a_will (∃x∙((a♢0) calls (a♢2) ∎ expose ⟨ empty ⟩)) ∨
                           ((a_ this) calls (a♢1) ∎ expose ⟨ empty ⟩)))).
  Proof.
    unfold mdl_sat;
      intros;    
      repeat (a_intros; a_prop);
      simpl in *.
    
    repeat destruct_exists_loo.
    destruct σ as [χ]; simpl in *; subst.

    inversion H6; subst.
    inversion H10; subst.

    - right.
      admit.

    - assert (σ_wf (χ0, ϕ0::ψ0)).
      match goal with
      | [H : update_σ_map _ _ _ = ?σ |- context[?σ]] =>
        rewrite <- H
      end.
      repeat (eapply σ_wf_update; eauto).
      apply arising_wf with (M1:=MyModule)(M2:=M'); auto.
      let someσ := fresh "σ" in
      destruct (exists_adaptation (χ0,ϕ0::ψ0) σ) as [someσ];
        auto.
      apply pair_reduction_preserves_config_wf
        with (M1:=MyModule)(M2:=M')
             (σ1:=(χ0, ϕ0::nil));
        auto.
      eapply σ_wf_top_frame; eauto.

      destruct (sat_excluded_middle MyModule M' σ0 (guards (a_ z) (a_ z0))) as [Hsat|Hnsat].

      + destruct will_change_pair_reduction
          with (M1:=MyModule)(M2:=M')
               (A:=guards (a_ z) (a_ z0))
               (σ1:=σ)(σ1':=σ0)
               (σ2:=σ')(σ2':=σ'')
               (σ:=(χ0,ϕ0::ψ0));
          eauto with loo_db.
        * crush.
        * repeat destruct_exists_loo;
            andDestruct.
          left.
          let Ha := fresh "H" in
          let Hb := fresh "H" in
          destruct (pair_reductions_alt_definition MyModule M' σ σ1)
            as [Ha Hb];
            match goal with
            | [H : MyModule ⦂ M' ⦿ σ ⤳⋆ σ1 |- _] =>
              specialize (Ha H);
                destruct Ha
            end.

          ** destruct (pair_reduction_change_implies_method_call MyModule M' σ σ1);
               eauto with loo_db.
             *** repeat destruct_exists_loo;
                   andDestruct;
                   subst.
                 apply sat_will with (χ:=χ0)(ψ:=ψ0)(ϕ:=ϕ0)(σ':=(χ1,ϕ1::ψ1))(σ'':=σ0);
                   eauto with loo_db.
                 rewrite H9; auto.
                 admit.

             *** admit.

          ** admit.

        * admit.

      + admit.

  Admitted.

  (**
     expose_example_was does not work, because there is no way to ensure that 
     some frame in the stack below the identified frame in the past does not
     have access to inside. Thus, access could be granted purely by returning 
     from some method call. expose_example_will works because will restricts
     the stack to just the top frame, thus removing the possibility of returning
     to some lower frame.
   *)

  Theorem expose_example_was :
    MyModule ⊨m (∀x∙∀x∙((a_was (((a_class (e♢1) Boundary)
                                 ∧
                                 ((e_acc_f (e♢1) inside) ⩦ (e♢0)))
                                ∧
                                ((guards (a♢1) (a♢0))))
                         ∧
                         (¬ guards (a♢1) (a♢0)))
                          ⇒
                          a_was(∃x∙((a♢0) calls (a♢2) ∎ expose ⟨ empty ⟩)))).
  Proof.
    unfold mdl_sat;
      intros.
    repeat (a_intros; a_prop).
    simpl in *.    

    inversion H5; subst.
    apply sat_was; intros.
    specialize (H11 σ0);
      repeat auto_specialize.
    destruct H11 as [σ' Htmp];
      destruct Htmp as [σ''];
      andDestruct.
    inversion Hb; subst.

    assert (Hwf : σ_wf σ');
      [eauto with loo_db|].

    destruct (was_change_pair_reduction MyModule M')
      with (σ:=(update_σ_map (update_σ_map σ z v) z0 v0))
           (σ':=σ')(A:=¬ guards (a_ z) (a_ z0))(σ'':=σ'')
      as [Hwas|Hwas];
      auto;
      [apply sat_not, nsat_not; auto| |destruct Hwas as [Hwas|Hwas]].

    - destruct Hwas as [σ1 Htmp];
        destruct Htmp as [σ1' Htmp];
        destruct Htmp as [σ2 Htmp];
        destruct Htmp as [σ2' Htmp];
        andDestruct.
      exists σ1, σ1';
        repeat split; eauto with loo_db.
      destruct (pair_reduction_change_implies_method_call MyModule M' σ1 σ2)
        as [Hcont|Hcont];
        eauto with loo_db;
        [|destruct Hcont as [Hcont|Hcont]].
      * destruct Hcont as [χ1 Hcont];
          destruct Hcont as [ϕ1 Hcont];
          destruct Hcont as [ψ1 Hcont];
          destruct Hcont as [x' Hcont];
          destruct Hcont as [y' Hcont];
          destruct Hcont as [m Hcont];
          destruct Hcont as [ps Hcont];
          destruct Hcont as [s Hcont];
          andDestruct;
          subst.

        admit.

      * admit.

      * admit.

    - destruct Hwas as [σ1 Htmp];
        destruct Htmp as [σ1' Htmp];
        andDestruct.
      exists σ1, σ1';
        repeat split; eauto with loo_db.
    
  Abort.

End ExposeExample.

(*Module SafeExample.

  (** #<h3># Safe example: #</h3># *)
  (** ---------------------------------------------------- *)
  (** #<code># >MyModule = { #</code># *)
  (** #<code># >  Inside = {} #</code># *)
  (** #<code># >  Boundary = { #</code># *)
  (** #<code># >    field inside : Inside #</code># *)
  (** #<code># >    meth expose() = {return this.inside} #</code># *)
  (** #<code># >  } #</code># *)
  (** #<code># >} #</code># *)
  (** --------------------------------------------------- *)
  (** #<code># we want to prove: #</code># *)
  (**  *)
  (** #<code># >MyModule ⊨  #</code># *)
  (** #<code># >(∀ b, b : Boundary, ∀ i, (b.inside = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
  (** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
  (** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
  (**  *)
  (**  *)

  (** Treasure Definition  *)

  Definition Treasure := classID 6.

  Definition TreasureDef := clazz Treasure
                                  nil
                                  empty
                                  empty.

  (** Safe Definition *)

  Definition Safe := classID 7.

  Definition treasure := fieldID 0.

  Definition open := methID 0.

  Definition x := bnd 10.

  Definition openBody := s_stmts (s_asgn (r_var x) (r_fld this treasure))
                                 (s_rtrn x).

  Definition SafeDef := clazz Safe
                              (treasure :: nil)
                              (update
                                 open (nil, openBody)
                                 empty)
                              empty.

  (** Owner Definition *)

  Definition Owner := classID 8.

  Definition safe := fieldID 1.

  Definition open_safe := methID 1.

  Definition y := bnd 11.

  Definition openSafeBody := s_stmts (s_asgn (r_var y) (r_fld this safe))
                                     (s_stmts (s_meth y y open empty)
                                              (s_rtrn y)).

  Definition OwnerDef := clazz Owner
                                (safe :: nil)
                                (update open_safe (nil, openSafeBody)
                                        empty)
                                empty.

  (** MyModule Definition *)

  Definition MyModule := (update Owner OwnerDef
                                 (update
                                    Safe SafeDef
                                    (update
                                       Treasure TreasureDef
                                       empty))).  

  Lemma safe_example_will_was_abort :
    MyModule ⊨m (∀x∙∀x∙∀x∙((a_class (e♢ 2) Owner) ∧
                           (a_class (e♢ 1) Safe) ∧
                           ((e_acc_f (e♢ 1) treasure) ⩦ e♢ 0) ∧
                           ((e_acc_f (e♢ 2) safe) ⩦ e♢ 1) ∧
                           (guards (a♢ 2) (a♢ 1)) ∧
                           (guards (a♢ 1) (a♢ 0))
                             ⇒
                             (a_will ((guards (a♢ 1) (a♢ 0)) ∨
                                      (a_was ((a♢ 2) calls (a♢ 1) ∎ open ⟨ empty ⟩)))))).
  Proof.
    unfold mdl_sat; intros.
    a_intros; sbst_simpl; simpl in *.
    a_contra.
    eapply will_neg in H8.
  Abort.

  Lemma safe_may_not_be_exposed :
    MyModule ⊨m (∀x∙∀x∙(a_was ((a_class (e♢ 1) Owner) ∧
                               (a_class (e♢ 0) Safe) ∧
                               ((e_acc_f (e♢ 1) safe) ⩦ e♢ 0) ∧
                               (guards (a♢ 1) (a♢ 0)))
                              ⇒
                              (guards (a♢ 1) (a♢ 0)))).
  Proof.
    unfold mdl_sat;
      intros;
      repeat (a_intros; sbst_simpl; a_prop);
      simpl in *.
    a_contra.
    destruct σ as [χ ψ']; simpl in *.
    destruct H0 as [ϕ Htmp];
      destruct Htmp as [ψ];
      subst.
    unfold update_σ_map in *;
      simpl in *.
    eapply (entails_implies) in H6;
      [|apply not_all_x_ex_not_1].
    SearchAbout a_will.
    Print reduction.
  Admitted.
  

  Lemma safe_example_was :
    MyModule ⊨m (∀x∙∀x∙∀x∙(a_was ((a_class (e♢ 2) Owner) ∧
                                  (a_class (e♢ 1) Safe) ∧
                                  ((e_acc_f (e♢ 1) treasure) ⩦ e♢ 0) ∧
                                  ((e_acc_f (e♢ 2) safe) ⩦ e♢ 1) ∧
                                  (guards (a♢ 2) (a♢ 1)) ∧
                                  (guards (a♢ 1) (a♢ 0))) ∧
                           (¬ guards (a♢ 1) (a♢ 0))
                             ⇒
                             (a_was ((a♢ 2) calls (a♢ 1) ∎ open ⟨ empty ⟩)))).
  Proof.
    unfold mdl_sat;
      intros;
      repeat (a_intros; sbst_simpl; a_prop);
      simpl in *.
    
    
    
  Qed.

  Lemma safe_example_will :
    MyModule ⊨m (∀x∙∀x∙∀x∙((a_class (e♢ 2) Owner) ∧
                           (a_class (e♢ 1) Safe) ∧
                           ((e_acc_f (e♢ 1) treasure) ⩦ e♢ 0) ∧
                           ((e_acc_f (e♢ 2) safe) ⩦ e♢ 1) ∧
                           (guards (a♢ 2) (a♢ 1)) ∧
                           (guards (a♢ 1) (a♢ 0)) ∧
                           (a_will (¬ guards (a♢ 1) (a♢ 0)))
                             ⇒
                             (((a♢ 2) calls (a♢ 1) ∎ open ⟨ empty ⟩) ∨
                              (a_will ((a♢ 2) calls (a♢ 1) ∎ open ⟨ empty ⟩))))).
  Proof.
    unfold mdl_sat; intros.
    repeat (*a_prop; a_intros; sbst_simpl; simpl in .*)
    
    eapply will_neg in H8.
  Qed.


End SafeExample.*)
      
Fixpoint syntactic_depth (A : asrt) : nat :=
  match A with
  | A1 ⇒ A2 => 1 + (syntactic_depth A1) + (syntactic_depth A2)
  | A1 ∨ A2 => 1 + (syntactic_depth A1) + (syntactic_depth A2)
  | A1 ∧ A2 => 1 + (syntactic_depth A1) + (syntactic_depth A2)
  | ¬ A => 1 + (syntactic_depth A)
  | (∀x∙ A) => 1 + (syntactic_depth A)
  | (∀S∙ A) => 1 + (syntactic_depth A)
  | (∃x∙ A) => 1 + (syntactic_depth A)
  | (∃S∙ A) => 1 + (syntactic_depth A)
  | a_next A => 1 + (syntactic_depth A)
  | a_will A => 1 + (syntactic_depth A)
  | a_prev A => 1 + (syntactic_depth A)
  | a_was A => 1 + (syntactic_depth A)
  | a_in A _ => 1 + (syntactic_depth A)
  | _ => 0
  end.

Lemma syntactic_depth_eq_raise :
  forall A n, syntactic_depth A = (syntactic_depth (A ↑ n)).
Proof.
  intros A;
    induction A;
    intros;
    simpl;
    auto.
Qed.

Require Import Coq.Program.Wf.

Lemma substitution_entails :
  forall A1 A2, entails A1 A2 ->
           forall z, notin_Ax A1 z ->
                notin_Ax A2 z ->
                entails ([z /s 0] A1) ([z /s 0] A2).
Proof.
  intros
Qed.

(** <h2>Thoughts on access, expose, temporal operators:</h2> *)

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