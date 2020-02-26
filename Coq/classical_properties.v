Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import function_operations.
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
  - repeat destruct_exists;
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
    repeat destruct_exists;
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
    repeat destruct_exists;
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
  forall A1 A2, entails A1 A2 ->
           forall M1 M2 χ ϕ ψ, M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A1 ->
                          M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2.
Proof.
  intros A1 A2 Hent;
    inversion Hent;
    auto.
Qed.

Class Raiseable (A : Type) :=
  {
    raise : A -> nat -> A
  }.

Notation "a '↑' n" := (raise a n)(at level 40).

Instance raiseNat : Raiseable nat :=
  {
    raise n m := if leb m n
                 then (S n)
                 else n
  }.

Instance raiseExp : Raiseable exp :=
  {
    raise :=
      fix raise' e n :=
        match e with
        | e_hole m => e_hole (m ↑ n)
        | e_eq e1 e2 => e_eq (raise' e1 n) (raise' e2 n)
        | e_if e1 e2 e3 => e_if (raise' e1 n) (raise' e2 n) (raise' e3 n)
        | e_acc_f e' f => e_acc_f (raise' e' n) f
        | e_acc_g e1 g e2 => e_acc_g (raise' e1 n) g (raise' e2 n)
        | _ => e
        end
  }.

Instance raiseAVar : Raiseable a_var :=
  {
    raise x n := match x with
                 | a_hole m => a_hole (m ↑ n)
                 | _ => x
                 end
  }.

Instance raiseFn {A B : Type}`{Eq A}`{Raiseable B} : Raiseable (partial_map A B) :=
  {
    raise f n := fun x => bind (f x) (fun y => Some (y ↑ n))
  }.

Instance raiseAsrt : Raiseable asrt :=
  {
    raise :=
      fix raise' A n :=
        match A with
        | a_exp e => a_exp (e ↑ n)
        | a_eq e1 e2 => a_eq (e1 ↑ n) (e2 ↑ n)
        | a_class e C => a_class (e ↑ n) C
        | a_set e Σ => a_set (e ↑ n) Σ

        | A1 ⇒ A2 => (raise' A1 n) ⇒ (raise' A2 n)
        | A1 ∧ A2 => (raise' A1 n) ∧ (raise' A2 n)
        | A1 ∨ A2 => (raise' A1 n) ∨ (raise' A2 n)
        | ¬ A' => ¬ (raise' A' n)

        | ∀x∙ A' => ∀x∙ (raise' A' (S n))
        | ∃x∙ A' => ∃x∙ (raise' A' (S n))
        | ∀S∙ A' => ∀S∙ (raise' A' (S n))
        | ∃S∙ A' => ∃S∙ (raise' A' (S n))

        | x access y => (x ↑ n) access (y ↑ n)
        | x calls y ∎ m ⟨ vMap ⟩ => (x ↑ n) calls (y ↑ n) ∎ m ⟨ vMap ↑ n ⟩

        | a_next A' => a_next (raise' A' n)
        | a_will A' => a_will (raise' A' n)
        | a_prev A' => a_prev (raise' A' n)
        | a_was A' => a_was (raise' A' n)

        | a_in A' Σ => a_in (raise' A' n) Σ

        | x external => (x ↑ n) external
        | x internal => (x ↑ n) internal
        end
  }.

Lemma sbst_x_neg :
  forall (x : var) n A, ([x /s n] ¬A) = (¬ ([x /s n]A)).
Proof.
  auto.
Qed.

Lemma sbst_x_arr :
  forall (x : var) n A1 A2, ([x /s n] (A1 ⇒ A2)) = (([x /s n]A1) ⇒ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_and :
  forall (x : var) n A1 A2, ([x /s n] (A1 ∧ A2)) = (([x /s n]A1) ∧ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_exp :
  forall (x : var) n e, ([x /s n] (a_exp e)) = (a_exp ([x /s n] e)).
Proof.
  auto.
Qed.

Lemma sbst_x_aeq :
  forall (x : var) n e1 e2, ([x /s n] (a_eq e1 e2)) = (a_eq ([x /s n] e1) ([x /s n] e2)).
Proof.
  auto.
Qed.

Lemma sbst_x_class :
  forall (x : var) n e C, ([x /s n] (a_class e C)) = (a_class ([x /s n] e) C).
Proof.
  auto.
Qed.

Lemma sbst_x_set :
  forall (x : var) n e Σ, ([x /s n] (a_set e Σ)) = (a_set ([x /s n] e) Σ).
Proof.
  auto.
Qed.

Lemma sbst_x_or :
  forall (x : var) n A1 A2, ([x /s n] (A1 ∨ A2)) = (([x /s n]A1) ∨ ([x /s n]A2)).
Proof.
  auto.
Qed.

Lemma sbst_x_all_x :
  forall (x : var) n A, ([x /s n] (∀x∙A)) = ((∀x∙[x /s S n] A)).
Proof.
  auto.
Qed.
          
Lemma sbst_x_all_Σ :
  forall (x : var) n A, ([x /s n] (∀S∙A)) = ((∀S∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_ex_x :
  forall (x : var) n A, ([x /s n] (∃x∙A)) = ((∃x∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_ex_Σ :
  forall (x : var) n A, ([x /s n] (∃S∙A)) = ((∃S∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_all_x :
  forall (x : varSet) n A, ([x /s n] (∀x∙A)) = ((∀x∙[x /s n] A)).
Proof.
  auto.
Qed.
          
Lemma sbst_Σ_all_Σ :
  forall (x : varSet) n A, ([x /s n] (∀S∙A)) = ((∀S∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_ex_x :
  forall (x : varSet) n A, ([x /s n] (∃x∙A)) = ((∃x∙[x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_Σ_ex_Σ :
  forall (x : varSet) n A, ([x /s n] (∃S∙A)) = ((∃S∙[x /s S n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_next :
  forall (x : var) n A, ([x /s n] (a_next A)) = (a_next ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_will :
  forall (x : var) n A, ([x /s n] (a_will A)) = (a_will ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_prev :
  forall (x : var) n A, ([x /s n] (a_prev A)) = (a_prev ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_was :
  forall (x : var) n A, ([x /s n] (a_was A)) = (a_was ([x /s n] A)).
Proof.
  auto.
Qed.

Lemma sbst_x_acc :
  forall (x : var) n y z, ([x /s n] (y access z)) = (([x /s n] y) access ([x /s n] z)).
Proof.
  auto.
Qed.

Lemma sbst_x_call :
  forall (x : var) n y z m vMap, ([x /s n] (y calls z ∎ m ⟨ vMap ⟩)) = (([x /s n] y) calls ([x /s n] z) ∎ m ⟨ ([x /s n] vMap) ⟩).
Proof.
  auto.
Qed.

Lemma sbst_x_in :
  forall (x : var) n A Σ, ([x /s n] (a_in A Σ)) = (a_in ([x /s n] A) Σ).
Proof.
  auto.
Qed.

Lemma sbst_Σ_in :
  forall (x : varSet) n A Σ, ([x /s n] (a_in A Σ)) = (a_in ([x /s n] A) ([x /s n] Σ)).
Proof.
  auto.
Qed.

Lemma sbst_x_extrn :
  forall (x : var) n y, ([x /s n] (y external)) = (([x /s n] y) external).
Proof.
  auto.
Qed.

Lemma sbst_x_intrn :
  forall (x : var) n y, ([x /s n] (y internal)) = (([x /s n] y) internal).
Proof.
  auto.
Qed.

Ltac sbst_simpl :=
  match goal with
  | [H : context[[_ /s _] (a_exp _)] |- _] => rewrite sbst_x_exp in H
  | [H : context[[_ /s _] (a_eq _ _)] |- _] => rewrite sbst_x_aeq in H
  | [H : context[[_ /s _] (a_class _ _)] |- _] => rewrite sbst_x_class in H
  | [H : context[[_ /s _] (a_set _ _)] |- _] => rewrite sbst_x_set in H

  | [H : context[[_ /s _] (¬ _)] |- _] => rewrite sbst_x_neg in H
  | [H : context[[_ /s _] (_ ∨ _)] |- _] => rewrite sbst_x_or in H
  | [H : context[[_ /s _] (_ ∧ _)] |- _] => rewrite sbst_x_and in H
  | [H : context[[_ /s _] (_ ⇒ _)] |- _] => rewrite sbst_x_arr in H

  | [H : context[[_ /s _] (a_next _)] |- _] => rewrite sbst_x_next in H
  | [H : context[[_ /s _] (a_will _)] |- _] => rewrite sbst_x_will in H
  | [H : context[[_ /s _] (a_prev _)] |- _] => rewrite sbst_x_prev in H
  | [H : context[[_ /s _] (a_was _)] |- _] => rewrite sbst_x_was in H

  | [H : context[[_ /s _] (∀x∙_)] |- _] => rewrite sbst_x_all_x in H
  | [H : context[[_ /s _] (∀S∙_)] |- _] => rewrite sbst_x_all_Σ in H
  | [H : context[[_ /s _] (∃x∙_)] |- _] => rewrite sbst_x_ex_x in H
  | [H : context[[_ /s _] (∃S∙_)] |- _] => rewrite sbst_x_ex_Σ in H

  | [H : context[[_ /s _] (_ access _)] |- _] => rewrite sbst_x_acc in H
  | [H : context[[_ /s _] (_ calls _ ∎ _ ⟨ _ ⟩)] |- _] => rewrite sbst_x_call in H

  | [H : context[[_ /s _] (a_in _ _)] |- _] => rewrite sbst_x_in in H
  | [H : context[[_ /s _] (_ external)] |- _] => rewrite sbst_x_extrn in H
  | [H : context[[_ /s _] (_ internal)] |- _] => rewrite sbst_x_intrn in H

  | [|- context[[_ /s _] (a_exp _)]] => rewrite sbst_x_exp
  | [|- context[[_ /s _] (a_eq _ _)]] => rewrite sbst_x_aeq
  | [|- context[[_ /s _] (a_class _ _)]] => rewrite sbst_x_class
  | [|- context[[_ /s _] (a_set _ _)]] => rewrite sbst_x_set

  | [|- context[[_ /s _] (¬ _)]] => rewrite sbst_x_neg
  | [|- context[[_ /s _] (_ ∨ _)]] => rewrite sbst_x_or
  | [|- context[[_ /s _] (_ ∧ _)]] => rewrite sbst_x_and
  | [|- context[[_ /s _] (_ ⇒ _)]] => rewrite sbst_x_arr

  | [|- context[[_ /s _] (a_next _)]] => rewrite sbst_x_next
  | [|- context[[_ /s _] (a_will _)]] => rewrite sbst_x_will
  | [|- context[[_ /s _] (a_prev _)]] => rewrite sbst_x_prev
  | [|- context[[_ /s _] (a_was _)]] => rewrite sbst_x_was

  | [|- context[[_ /s _] (∀x∙_)]] => rewrite sbst_x_all_x
  | [|- context[[_ /s _] (∀S∙_)]] => rewrite sbst_x_all_Σ
  | [|- context[[_ /s _] (∃x∙_)]] => rewrite sbst_x_ex_x
  | [|- context[[_ /s _] (∃S∙_)]] => rewrite sbst_x_ex_Σ

  | [|- context[[_ /s _] (_ access _)]] => rewrite sbst_x_acc
  | [|- context[[_ /s _] (_ calls _ ∎ _ ⟨ _ ⟩)]] => rewrite sbst_x_call

  | [|- context[[_ /s _] (a_in _ _)]] => rewrite sbst_x_in
  | [|- context[[_ /s _] (_ external)]] => rewrite sbst_x_extrn
  | [|- context[[_ /s _] (_ internal)]] => rewrite sbst_x_intrn
  end.

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
         | [H : _ ⦂ _ ◎ _ ⊨ (∀x∙_) |- _] => rewrite all_x_prop in H; repeat sbst_simpl
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∧ _)] => apply sat_and
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∨ _)] => apply <- or_iff
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
      repeat destruct_exists;
      andDestruct;
      repeat sbst_simpl;
      repeat (a_intros; a_prop). (* x1 is fresh in A, and subst/raise with weakening gives the desired result *)
    admit.

  - apply ex_x_prop in H;
      repeat destruct_exists;
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
  destruct H; a_prop; eauto with chainmail_db.
  inversion H; eauto with chainmail_db.
Qed.

Hint Resolve arr_cnf_1 arr_cnf_2 : chainmail_db.

Lemma arr_cnf_equiv :
  forall A1 A2, equiv_a ((A1 ∧ A2) ∨ (¬ A1))
                   (A1 ⇒ A2).
Proof.
  split; auto with chainmail_db.
Qed.

Hint Resolve arr_cnf_equiv : chainmail_db.

Ltac cnf_auto :=
  match goal with
  | [H : context[_ ∧ (∃x∙_)] |- _] => rewrite and_exists_x_entails_1 in H
  | [H : context[(∃x∙_) ∧ _] |- _] => rewrite and_commutative' in H
  | [H : context[_ ∧ (∀x∙_)] |- _] => rewrite and_forall_x_entails_1 in H
  | [H : context[(∀x∙_) ∧ _] |- _] => rewrite and_commutative' in H

  | [H : context[_ ∨ (∃x∙_)] |- _] => rewrite or_exists_x_entails_1 in H
  | [H : context[(∃x∙_) ∨ _] |- _] => rewrite or_commutative' in H
  | [H : context[_ ∨ (∀x∙_)] |- _] => rewrite or_forall_x_entails_1 in H
  | [H : context[(∀x∙_) ∨ _] |- _] => rewrite or_commutative' in H

  | [H : context[_ ⇒ _] |- _] => rewrite arr_cnf_1 in H

  | [|- context[_ ∧ (∃x∙_)]] => rewrite and_exists_x_entails_1
  | [|- context[(∃x∙_) ∧ _]] => rewrite and_commutative'
  | [|- context[_ ∧ (∀x∙_)]] => rewrite and_forall_x_entails_1
  | [|- context[(∀x∙_) ∧ _]] => rewrite and_commutative'

  | [|- context[_ ∨ (∃x∙_)]] => rewrite or_exists_x_entails_1
  | [|- context[(∃x∙_) ∨ _]] => rewrite or_commutative'
  | [|- context[_ ∨ (∀x∙_)]] => rewrite or_forall_x_entails_1
  | [|- context[(∀x∙_) ∨ _]] => rewrite or_commutative'

  | [|- context[_ ⇒ _]] => rewrite arr_cnf_1
  end.