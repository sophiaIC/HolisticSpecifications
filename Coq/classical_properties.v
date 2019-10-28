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

(** Lemma 5: Classical (2) *)
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

(** Lemma 5: Classical (3) *)
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

Inductive entails : asrt -> asrt -> Prop :=
| ent : forall A1 A2, (forall σ M1 M2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                             M1 ⦂ M2 ◎ σ ⊨ A2) ->
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

Hint Resolve sat_and_nsat_entails_false.

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

Hint Resolve false_entails_sat_and_nsat.

(** Lemma 6: (1) *)
Lemma sat_and_nsat_equiv_false :
  forall A, equiv_a (A ∧ ¬ A) (a_exp (e_false)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Lemma or_commutative' :
  forall A1 A2, entails (A1 ∨ A2) (A2 ∨ A1).
Proof.
  intros;
    apply ent;
    intros.

  inversion H;
    eauto.
Qed.

Hint Resolve or_commutative'.

(** Lemma 6: (4) *)
Lemma or_commutative :
  forall A1 A2, equiv_a (A1 ∨ A2) (A2 ∨ A1).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve or_commutative.

Lemma and_commutative' :
  forall A1 A2, entails (A1 ∧ A2) (A2 ∧ A1).
Proof.
  intros;
    eapply ent;
    intros;
    eauto.
  inversion H;
    eauto.
Qed.

Hint Resolve and_commutative'.

(** Lemma 6: (3) *)
Lemma and_commutative :
  forall A1 A2, equiv_a (A1 ∧ A2) (A2 ∧ A1).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve and_commutative.

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
    eauto.
Qed.

Hint Resolve or_associative_1.

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
    eauto.
Qed.

Hint Resolve or_associative_2.

(** Lemma 6: (5) *)
Lemma or_associative:
  forall A1 A2 A3, equiv_a ((A1 ∨ A2) ∨ A3) (A1 ∨ (A2 ∨ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve or_associative.

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
    eauto.
Qed.

Hint Resolve and_distributive_1.

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
    eauto.
Qed.

Hint Resolve and_distributive_2.

(** Lemma 6: (6) *)
Lemma and_distributive:
  forall A1 A2 A3, equiv_a ((A1 ∨ A2) ∧ A3) ((A1 ∧ A3) ∨ (A2 ∧ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve and_distributive.

Lemma or_distributive_1:
  forall A1 A2 A3, entails ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
Proof.
  intros;
    apply ent;
    intros;
    inversion H;
    subst;
    eauto;
    inversion H4;
    eauto.
Qed.

Hint Resolve or_distributive_1.

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
    eauto.
Qed.

Hint Resolve or_distributive_2.

(** Lemma 6: (7) *)
Lemma or_distributive:
  forall A1 A2 A3, equiv_a ((A1 ∧ A2) ∨ A3) ((A1 ∨ A3) ∧ (A2 ∨ A3)).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve or_distributive.

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
    eauto.
Qed.

Hint Resolve neg_distributive_and_1.

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
    eauto.
Qed.

Hint Resolve neg_distributive_and_2.

(** Lemma 6: (8) *)
Lemma neg_distributive_and:
  forall A1 A2, equiv_a (¬(A1 ∧ A2))  (¬A1 ∨ ¬A2).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve neg_distributive_and.

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
    eauto.
Qed.

Hint Resolve neg_distributive_or_1.

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
    eauto.
Qed.

Hint Resolve neg_distributive_or_2.

(** Lemma 6: (9) *)
Lemma neg_distributive_or:
  forall A1 A2, equiv_a (¬(A1 ∨ A2)) (¬A1 ∧ ¬A2).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve neg_distributive_or.

Lemma subst_neg :
  forall x n A, ([x /s n] ¬A) = (¬ ([x /s n]A)).
Proof.
  auto.
Qed.

Lemma fresh_not_1 :
  forall x σ A, fresh_x x σ A ->
           fresh_x x σ (¬ A).
Proof.
  intros.
  inversion H;
    subst.
  apply frsh;
    eauto.
Qed.

Hint Resolve fresh_not_1.

Lemma fresh_not_2 :
  forall x σ A, fresh_x x σ (¬ A) ->
           fresh_x x σ A.
Proof.
  intros.
  inversion H;
    subst.
  inversion H1;
    subst.
  apply frsh;
    eauto.
Qed.

Hint Resolve fresh_not_2.

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
  eapply H5; eauto.
Qed.

Hint Resolve not_ex_x_all_not_1.

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
    eauto.

  inversion H0;
    eauto.
Qed.

Hint Resolve not_ex_x_all_not_2.

(** Lemma 6: (10) *)
Lemma not_ex_x_all_not : 
  forall A, equiv_a (¬(∃x∙A)) (∀x∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve not_ex_x_all_not.

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

Hint Resolve not_ex_Σ_all_not_1.

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

Hint Resolve not_ex_Σ_all_not_2.

(** Lemma 6: (11) *)
Lemma not_ex_Σ_all_not : 
  forall A, equiv_a (¬(∃S∙A)) (∀S∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve not_ex_Σ_all_not.

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

Hint Resolve not_all_Σ_ex_not_1.

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

Hint Resolve not_all_Σ_ex_not_2.

(** Lemma 6: (13) *)
Lemma not_all_Σ_ex_not : 
  forall A, equiv_a (¬(∀S∙A)) (∃S∙¬A).
Proof.
  intros;
    unfold equiv_a;
    intros;
    split;
    eauto.
Qed.

Hint Resolve not_all_Σ_ex_not.

(** Properties of Linking *)
Lemma moduleLinking_associative :
  forall M1 M2 M12, M1 ∘ M2 ≜ M12 ->
               forall M3 M23, M2 ∘ M3 ≜ M23 ->
                         forall M M', M12 ∘ M3 ≜ M ->
                                 M1 ∘ M23 ≜ M' ->
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
  forall M1 M2 M, M1 ∘ M2 ≜ M ->
             M_wf M1 ->
             M_wf M2 ->
             M2 ∘ M1 ≜ M.
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
  forall M1 M2 M, M1 ∘ M2 ≜ M ->
             forall M', M2 ∘ M1 ≜ M' ->
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
    rewrite <- Heqres2 in H10.
  inversion H5;
    inversion H10;
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
              forall M2 M, M1 ∘ M2 ≜ M ->
                      M ∙ σ1 ⤳ σ2.
Proof.
  intros M1 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    eauto.

  eapply r_mth;
    eauto.
  inversion H11;
    subst;
    unfold extend in *;
    eauto.
  rewrite H6;
    auto.

  eapply r_new;
    eauto.
  inversion H12;
    unfold extend in *;
    subst;
    eauto.
  rewrite H5;
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