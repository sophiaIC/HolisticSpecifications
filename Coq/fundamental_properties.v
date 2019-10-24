Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** #<h1># Basic Arithmetic Assertions: #</h1># *)

(** Law of the Excluded Middle: *)
Parameter excluded_middle : forall P, P \/ ~P.

Lemma prop_not_and_distr :
  forall A B, ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros.
  destruct (excluded_middle A);
    destruct (excluded_middle B);
    crush.
Qed.

Lemma prop_implies_not :
  forall (A B : Prop), (A -> ~B) -> (B -> ~A).
Proof.
  crush.
Qed.

Lemma prop_not_sat_and_distr :
  forall M1 M2 σ A1 A2, ~M1 ⦂ M2 ◎ σ ⊨ (a_and A1 A2) ->
                   (~M1 ⦂ M2 ◎ σ ⊨ A1) \/
                   (~ M1 ⦂ M2 ◎ σ ⊨ A2).
Proof.
  intros;
    apply prop_not_and_distr;
    intros Hcontra;
    destruct Hcontra as [Ha Hb];
    crush.
Qed.

Lemma forall_exists_neg :
  forall {A : Type} P, (forall (x : A), ~ P) ->
                  ~ (exists (a : A), P).
Proof.
  intros; crush.
Qed.

Lemma exists_neg_forall :
  forall {A : Type} (P : A -> Prop),
    ~ (exists (a : A), P a) ->
    (forall (a : A), ~ P a).
Proof.
  intros; intros Hcontra.
  contradiction H.
  exists a; auto.
Qed.

Lemma reduction_preserves_well_formed_heap :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             χ_wf M (fst σ1) ->
             χ_wf M (fst σ2).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    try solve [crush];
    subst;
    apply heap_wf;
    intros;
    subst.

  (*field assign reduce*)
  simpl in H.
  unfold update, t_update in H.
  destruct (eq_dec α0 α) as [Heq|Hneq];
    [subst; rewrite eqb_refl in H; auto
    |apply neq_eqb in Hneq; rewrite Hneq in H;
     inversion H11; subst; apply (H7 α0); auto].
  inversion H11; subst.
  destruct (H7 α o (cname o)) as [CDef Hwf]; auto;
    destruct Hwf as [Hwf1 Hwf2];
    destruct Hwf2 as [Hwf2 Hwf3].
  exists CDef; split;
    [inversion H; subst; auto
    |split;
     [intros
     |inversion H; subst; auto]].
  inversion H; subst; simpl.
  destruct (eq_dec f0 f) as [Heq|Hneq];
    [destruct f0; subst; rewrite <- beq_nat_refl; exists (v_addr α'); auto
    |destruct f0, f;
     assert (Hneq' : n <> n0);
     [intros Hcontra; subst; crush| apply Nat.eqb_neq in Hneq'; rewrite Hneq'; auto]].

  (*new object initialization*)
  simpl in *.
  unfold update, t_update in H0.
  destruct (eq_dec α0 α) as [Heq|Hneq];
    [subst; rewrite eqb_refl in H0
    |apply neq_eqb in Hneq; rewrite Hneq in H0;
     inversion H12; subst; apply (H9 α0); auto].
  exists CDef;
    split; [inversion H0; subst; auto
           |split;
            [intros
            |inversion H0; subst; auto]].
  inversion H0; subst; simpl.
  assert (Hin : fMap f = None -> ~ In f (c_flds CDef));
    [auto|].
  remember (fMap f) as res.
  destruct res as [y|];
    [
    |contradiction Hin; auto].
  destruct (H8 f y) as [v];
    auto.
  exists v; unfold compose; rewrite <- Heqres; auto.
Qed.

Lemma linking_unique :
  forall M1 M2 M, M1 ∘ M2 ≜ M ->
             forall M', M1 ∘ M2 ≜ M' ->
                   M' = M.
Proof.
  intros M1 M2 M Hlink1 M' Hlink2;
    inversion Hlink1; inversion Hlink2;
      subst;
      auto.
Qed.

Ltac link_unique_auto :=
  match goal with
  | [H1 : ?M1 ∘ ?M2 ≜ ?M, H2 : ?M1 ∘ ?M2 ≜ ?M' |-_] =>
    assert (M' = M);
    [eapply linking_unique;
     eauto|subst M']
  end.

Ltac reduce_heap_wf_auto :=
  match goal with
  | [Hred : ?M ∙ ?σ1 ⤳ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply reduction_preserves_well_formed_heap; eauto
  end.

Lemma reductions_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto;
    link_unique_auto;
    reduce_heap_wf_auto.
Qed.

Ltac reduces_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳… ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply reductions_preserves_heap_wf; eauto
  end.

Lemma pair_reduction_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.
  link_unique_auto.
  reduce_heap_wf_auto.
  reduces_heap_wf_auto.
Qed.

Ltac pair_reduce_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply pair_reduction_preserves_heap_wf; eauto
  end.

Lemma pair_reductions_preserves_heap_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      χ_wf M (fst σ1) ->
                      χ_wf M (fst σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto;
    try solve pair_reduce_heap_wf_auto.
  eapply IHHred; eauto;
    pair_reduce_heap_wf_auto.
Qed.

Ltac pair_reduces_heap_wf_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σ1 ⤳⋆ ?σ2 |- χ_wf ?M (fst ?σ2)] =>
    eapply pair_reductions_preserves_heap_wf; eauto
  end.

Lemma M_wf_ObjectDefn :
  forall M, M_wf M ->
       M ObjectName = Some ObjectDefn.
Proof.
  intros M Hwf; inversion Hwf; crush.
Qed.

Ltac obj_defn_rewrite :=
  match goal with
  | [H : M_wf ?M |- context[?M ObjectName]] => rewrite (M_wf_ObjectDefn M H)
  end.

Ltac empty_auto :=
  match goal with
  | [H : context [empty _] |- _] => unfold empty, t_empty in H; crush
  | [|- context [empty _]] => unfold empty, t_empty; crush
  end.

Ltac update_auto :=
  match goal with
  | [H : (update ?a _ _) ?a = Some ?b' |- _] => unfold update, t_update in H;
                                              subst; rewrite eqb_refl in H;
                                              inversion H; subst
  | [Hneq : ?a <> ?a', H : (update ?a _ _) ?a' = Some _ |- _] => unfold update, t_update in H;
                                                              apply neq_eqb in Hneq;
                                                              rewrite Hneq in H
  | [Hneq : ?a' <> ?a, H : (update ?a _ _) ?a' = Some _ |- _] => unfold update, t_update in H;
                                                              apply neq_eqb in Hneq;
                                                              rewrite Hneq in H
  | [H : (update ?a _ _) ?a' = Some ?b' |- _] => unfold update, t_update in H;
                                               let Heq := fresh "Heq" in
                                               let Hneq := fresh "Hneq" in
                                               destruct (eq_dec a' a) as [Heq|Hneq];
                                               [subst; rewrite eqb_refl in H;
                                                inversion H; subst
                                               |apply neq_eqb in Hneq;
                                                rewrite Hneq in H]

  | [H : context[(update ?a _ _) ?a]  |- _] => unfold update, t_update in H;
                                             subst; rewrite eqb_refl in H
  | [Hneq : ?a <> ?a', H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                                               apply neq_eqb in Hneq;
                                                               rewrite Hneq in H
  | [Hneq : ?a' <> ?a, H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                                               apply neq_eqb in Hneq;
                                                               rewrite Hneq in H
  | [H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                              let Heq := fresh "Heq" in
                                              let Hneq := fresh "Hneq" in
                                              destruct (eq_dec a' a) as [Heq|Hneq];
                                              [subst; rewrite eqb_refl in H
                                              |apply neq_eqb in Hneq;
                                               rewrite Hneq in H]
                                                     
  | [|- (update ?a _ _) ?a = Some _] => unfold update, t_update;
                                      subst; rewrite eqb_refl
  | [Hneq : ?a <> ?a' |- (update ?a _ _) ?a' = Some _] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [Hneq : ?a' <> ?a |- (update ?a _ _) ?a' = Some _] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [|- (update ?a _ _) ?a' = Some ?b'] => unfold update, t_update;
                                         let Heq := fresh "Heq" in
                                         let Hneq := fresh "Hneq" in
                                         destruct (eq_dec a' a) as [Heq|Hneq];
                                         [subst; rewrite eqb_refl
                                         |apply neq_eqb in Hneq;
                                          rewrite Hneq]
                                                
  | [|- context[(update ?a _ _) ?a]] => unfold update, t_update;
                                      subst; rewrite eqb_refl
  | [Hneq : ?a <> ?a' |- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [Hneq : ?a' <> ?a |- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [|- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                       let Heq := fresh "Heq" in
                                       let Hneq := fresh "Hneq" in
                                       destruct (eq_dec a' a) as [Heq|Hneq];
                                       [subst; rewrite eqb_refl
                                       |apply neq_eqb in Hneq;
                                        rewrite Hneq]
  end;
  auto.

Ltac pmap_simpl :=
  repeat (try empty_auto;
          try update_auto).

Lemma initial_heap_wf :
  forall σ, initial σ ->
       forall M, M_wf M ->
            χ_wf M (fst σ).
Proof.
  intros σ Hinit;
    destruct Hinit as [α Hinit];
    destruct Hinit as [ϕ Hinit];
    andDestruct;
    subst;
    intros.
  apply heap_wf;
    intros.
  simpl in H0; inversion H0; subst.
  update_auto;
    [exists ObjectDefn;
     split; simpl; auto;
     try solve [obj_defn_rewrite; auto];
     crush
    |empty_auto].
Qed.

Ltac initial_heap_wf_auto :=
  match goal with
  | [H : initial ?σ |- χ_wf ?M (fst ?σ)] => eapply initial_heap_wf; eauto
  end.

Lemma linked_wf :
  forall M1 M2 M, M1 ∘ M2 ≜ M ->
             M_wf M1 ->
             M_wf M2 ->
             M_wf M.
Proof.
  intros M1 M2 M Hlink Hwf1 Hwf2;
    inversion Hlink; subst;
      inversion Hwf1; subst;
        inversion Hwf2; subst.
  apply module_wf;
    auto; intros.
  unfold extend;
    destruct (M1 ObjectName); auto.
  unfold extend in H5.
  remember (M1 C) as x;
    destruct x; crush.
Qed.

Ltac linking_wf :=
  match goal with
  | [H1 : M_wf ?M1, H2 : M_wf ?M2, Hlink : ?M1 ∘ ?M2 ≜ ?M |- M_wf ?M] => eapply linked_wf; eauto
  end.

Lemma arising_heap_wf :
  forall M1 M2 σ, arising M1 M2 σ ->
             M_wf M1 ->
             M_wf M2 ->
             forall M, M1 ∘ M2 ≜ M ->
                  χ_wf M (fst σ).
Proof.
  intros.
  inversion H; subst.
  pair_reduces_heap_wf_auto.
  initial_heap_wf_auto.
  linking_wf.
Qed.

Lemma exists_dom_finite :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    exists d, dom m d.
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    [exists nil; auto|].

  destruct IHHfinite as [d Hdom].
  destruct (excluded_middle (In a d)) as [Hin|Hnin];
    [exists d|exists (a::d)]; auto.

Qed.

Lemma update_neq_empty :
  forall {A B : Type}`{Eq A} (a : A)(b : B) m,
    update a b m <> empty.
Proof.
  intros; intros Hcontra.
  assert (Heq : update a b m a = None);
    [rewrite Hcontra; pmap_simpl|pmap_simpl].
  crush.
Qed.

Ltac update_empty_contra :=
  match goal with
  | [H : update ?a ?b ?m = empty |- _] => contradiction (update_neq_empty a b m)
  | [H : empty = update ?a ?b ?m |- _] => symmetry in H; contradiction (update_neq_empty a b m)
  end.

Lemma dom_empty_is_nil :
  forall {A B : Type}`{Eq A} (m : partial_map A B) d,
    dom m d ->
    m = empty ->
    d = nil.
Proof.
  intros A B HeqClass m d H;
    intros;
    subst;
    inversion H;
    subst;
    auto;
    update_empty_contra.
Qed.

Lemma partial_map_dec :
  forall {A B : Type} `{Eq A} a (m : partial_map A B), {exists b, m a = Some b} + {m a = None}.
Proof.
  intros.
  destruct (m a) as [b|]; [left; exists b|]; crush.
Qed.

(*Lemma update_dom :
  forall {A B : Type}`{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a b, (dom (update a b m) d) \/ (dom (update a b m) (a::d)).
Proof.
  intros A B HeqCl m d Hdom;
    induction Hdom;
    intros.
  destruct (partial_map_dec a m) as [Hsome|Hnone];
    [left|right].
  apply d_map; intros; auto; [|pmap_simpl; try solve [crush]].
  pmap_simpl;
    [destruct Hsome as [b']
    |pmap_simpl]; eauto.
  exists b; auto.

  apply d_map;
    intros.
  pmap_simpl; crush;
    right; eapply H; eauto.
  pmap_simpl; [exists b; auto|].
  inversion H2; subst;
    [apply eqb_neq in Hneq; crush
    |crush].

  apply u_con;
    auto.
  intro Hcontra.
  apply H0 in Hcontra; crush.
Qed.*)

(*Lemma dom_update :
  forall {A B : Type} `{Eq A} (m : partial_map A B) a b d,
    dom (update a b m) d ->
    (dom m d) \/ (exists d', dom m d' /\ (d = a :: d')).
Proof.
  intros;
    inversion H0;
    subst.

  destruct (partial_map_dec a m);
    [left|right].

  apply d_map; intros; auto.
  destruct (eq_dec a0 a) as [Heq|Hneq];
    [subst; apply (H1 a b);
     pmap_simpl;
     auto
    |eapply H1; pmap_simpl; eauto].
  destruct (eq_dec a0 a) as [Heq|Hneq];
    [subst;
     pmap_simpl;
     auto
    |eapply H2 in H4; pmap_simpl; auto].

  destruct d as [|a' d'];
    [assert (Hin : In a nil);
     [apply (H1 a b); eauto; pmap_simpl; auto|crush]
    |exists d'; split].
  apply d_map;
    intros;
    auto.

  destruct (eq_dec a a0) as [Heq|Hneq];
    [subst; crush|].
  assert (Hin : In a0 (a'::d'));
    [apply H1 with (b0:=b0);
     pmap_simpl; crush
    |inversion Hin; subst; auto].

Qed.*)
    

Lemma zip_length_exists :
  forall {A B : Type} (l1 : list A) (l2 : list B),
    length l1 = length l2 ->
    exists z, zip l1 l2 z.
Proof.
  intros A B l1;
    induction l1 as [|a l];
    intros.
  exists nil;
    destruct l2;
    [auto|inversion H].
  destruct l2 as [|b l'];
    [inversion H
    |simpl in H;
     destruct (IHl l') as [z Hzip];
     auto].
  exists ((a,b)::z); auto.
Qed.

Lemma fresh_in_empty :
  forall {A : Type} x, @fresh_in_map A x empty.
Proof.
  unfold fresh_in_map;
    intros.
  pmap_simpl.
Qed.

Hint Resolve fresh_in_empty.

Lemma map_implies_in_dom :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a b, m a = Some b ->
           In a d.
Proof.
  intros A B HeqClass m d Hdom;
    induction Hdom;
    intros;
    try solve [pmap_simpl; crush; eauto].
Qed.

Lemma in_dom_implies_in_map :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a, In a d ->
    exists b, m a = Some b.
Proof.
  intros A B HeqClass m d Hdom;
    induction Hdom;
    intros;
    pmap_simpl;
    try solve [eexists; eauto].

  inversion H0;
    subst;
    [apply eqb_neq in Hneq;
     crush
    |eapply IHHdom; eauto].

Qed.

Lemma fresh_in_map_not_in_dom :
  forall {A : Type} (m : partial_map var A) d,
    dom m d ->
    forall x, fresh_in_map x m <-> ~ In x d.
Proof.
  intros A m d Hdom;
    induction Hdom;
    intros;
    split;
    auto;
    unfold fresh_in_map;
    intros;
    auto.

  apply IHHdom;
    unfold fresh_in_map;
    intros;
    destruct (eq_dec a y) as [Heq|Hneq];
    [subst; apply (H0 y b)
    |apply (H0 y a0)];
    pmap_simpl; crush.

  intros Hcontra;
    subst;
    pmap_simpl;
    apply map_implies_in_dom
    with (a1:=y)(b0:=a0)
    in Hdom;
    crush.

  intros Hcontra;
    inversion Hcontra;
    subst;
    [destruct (H0 x b); pmap_simpl; auto|];
    destruct (in_dom_implies_in_map m d) with (a:=x);
    auto;
    destruct (eq_dec x a) as [Heq|Hneq];
    [subst;
     contradiction (H0 a b);
     auto; pmap_simpl
    |contradiction (H0 x x0);
     auto; pmap_simpl].

  intros Hcontra;
    subst.
  pmap_simpl;
    [contradiction H0;
     crush
    |].
  assert (Hnin : ~ In y d);
    [intros Hcontra;
     crush
    |apply <- IHHdom in Hnin].
  unfold fresh_in_map in Hnin;
    apply Hnin in H1;
    crush.
Qed.

Inductive lt_map {A : Type} : nat -> partial_map var A -> Prop :=
| lt_empty : lt_map 0 empty
| lt_update1 : forall n b m n', lt_map n' m ->
                           n < n' ->
                           lt_map n' (update (bind n) b m)
| lt_update2 : forall n b m n', lt_map n' m ->
                           n' <= n ->
                           lt_map (S n) (update (bind n) b m).

Hint Constructors lt_map.

Lemma exists_limit_for_finite_map :
  forall {A : Type} (m : partial_map var A),
    finite m ->
    exists n, lt_map n m.
Proof.
  intros A m Hfinite;
    induction Hfinite;
    [exists 0; auto|destruct IHHfinite as [n]].
  
  destruct a as [n'].
  destruct (le_lt_dec n n') as [Hle|Hlt];
    [exists (S n'); eapply lt_update2|exists n; apply lt_update1]; eauto.
Qed.

Lemma lt_map_implies_var_lt :
  forall {A : Type} n (m : partial_map var A),
    lt_map n m ->
    forall n' b, m (bind n') = Some b ->
            n' < n.
Proof.
  intros A n m Hlt;
    induction Hlt;
    intros;
    pmap_simpl.
  destruct (eq_dec n'0 n);
    [subst|];
    pmap_simpl.
  unfold update, t_update in H0;
    rewrite neq_eqb in H0; [eauto|crush].
  destruct (eq_dec n'0 n);
    [subst|];
    pmap_simpl.
  unfold update, t_update in H0;
    rewrite neq_eqb in H0; [eauto|crush].
  apply IHHlt in H0; crush.
Qed.

Lemma lt_fresh_in_map :
  forall {A : Type} n (m : partial_map var A),
    lt_map n m -> forall n', n <= n' -> fresh_in_map (bind n') m.
Proof.
  intros A n m Hlt;
    induction Hlt;
    auto;
    unfold fresh_in_map in *;    
    intros;
    pmap_simpl;
    try solve [crush];
    eauto.

  destruct y as [n''].
  eapply lt_map_implies_var_lt in Hlt;
    eauto;
    crush.
Qed.

Lemma fresh_var_finite :
  forall {A : Type} (m : partial_map var A),
    finite m ->
    exists x, fresh_in_map x m.
Proof.
  intros;
    destruct (exists_limit_for_finite_map m) as [n];
    auto;
    exists (bind n);
    eapply lt_fresh_in_map;
    eauto.
Qed.

Lemma fresh_var_finite2 :
  forall {A : Type} (m1 : partial_map var A),
    finite m1 ->
    forall (m2 : partial_map var A), finite m2 ->
                                exists x, fresh_in_map x m1 /\
                                     fresh_in_map x m2.
Proof.
  intros.
  destruct (exists_limit_for_finite_map m1) as [n1];
    destruct (exists_limit_for_finite_map m2) as [n2];
    auto.
  destruct (le_lt_dec n1 n2) as [Hle|Hlt];
    [exists (bind n2)|exists (bind n1)];
    split;
    eapply lt_fresh_in_map;
    eauto;
    crush.
Qed.

Inductive lt_var : nat -> var -> Prop :=
| lt_bind : forall n n', n' < n ->
                    lt_var n (bind n').

Hint Constructors lt_var.

Lemma exists_limit_var :
  forall x, exists n, lt_var n x.
Proof.
  intros x;
    destruct x as [n'];
    exists (S n');
    crush.
Qed.

Lemma exists_limit_for_list :
  forall l, exists n, forall x, In x l ->
                 lt_var n x.
Proof.
  intros l;
    induction l as [|x l'];
    [exists 0; crush|destruct x as [n']].
  destruct IHl' as [n Hltx].
  destruct (le_lt_dec n n') as [Hle|Hlt];
    [exists (S n')|exists n];
    intros.
  inversion H; subst; crush.
  apply Hltx in H0.
  inversion H0; subst; crush.
  crush.
Qed.

Lemma fresh_var_finite3 :
  forall {A : Type} (m1 : partial_map var A),
    finite m1 ->
    forall (m2 : partial_map var A), finite m2 ->
                                forall d, exists x, fresh_in_map x m1 /\
                                          fresh_in_map x m2 /\
                                          ~ In x d.
Proof.
  intros.
  destruct (exists_limit_for_finite_map m1) as [n1];
    destruct (exists_limit_for_finite_map m2) as [n2];
    destruct (exists_limit_for_list d) as [n3];
    auto.
  destruct (le_lt_dec n1 n2) as [Hle1|Hlt1].
  destruct (le_lt_dec n1 n3) as [Hle2|Hlt2].
  
  destruct (le_lt_dec n3 n2) as [Hle3|Hlt3];

    try solve [exists (bind n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bind n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n3 n2) as [Hle3|Hlt3];

    try solve [exists (bind n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bind n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n1 n3) as [Hle2|Hlt2];

    try solve [exists (bind n1); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bind n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
Qed.

Lemma dom_implies_finite :
  forall {A : Type} (m : partial_map var A) d,
    dom m d ->
    finite m.
Proof.
  intros A m d Hdom;
    induction Hdom;
    crush.
Qed.

(** TODO: *)
Parameter fresh_var_list_finite :
  forall {A : Type} (m1 : partial_map var A) (d : list var),
    dom m1 d ->
    forall (m2 : partial_map var A) s,
      finite m2 ->
      exists d' D,
        (forall z, In z d' -> fresh_in_map z m1) /\
        (forall z, In z d' -> fresh_in_map z m2) /\
        (forall z, In z d' -> ~ in_stmt z s) /\
        unique d' /\
        zip d' d D.

Ltac finite_auto :=
  repeat match goal with
         | [H : context[finite_σ _] |- _] => unfold finite_σ in H
         | [H : context[finite_ψ _] |- _] => unfold finite_ψ in H
         | [H : context[finite_ϕ _] |- _] => unfold finite_ϕ in H
         | [|- context[finite_σ _]] => unfold finite_σ
         | [|- context[finite_ψ _]] => unfold finite_ψ
         | [|- context[finite_ϕ _]] => unfold finite_ϕ
         end.

Ltac not_stuck_auto :=
  repeat match goal with
         | [H : context[not_stuck_σ _] |- _] => unfold not_stuck_σ in H
         | [H : context[not_stuck_ϕ _] |- _] => unfold not_stuck_ϕ in H
         | [|- context[not_stuck_σ _]] => unfold not_stuck_σ
         | [|- context[not_stuck_ϕ _]] => unfold not_stuck_ϕ
         end.

Ltac waiting_auto :=
  repeat match goal with
         | [H : context[waiting_σ _] |- _] => unfold waiting_σ in H
         | [H : context[waiting_ψ _] |- _] => unfold waiting_ψ in H
         | [H : context[waiting_ϕ _] |- _] => unfold waiting_ϕ in H
         | [|- context[waiting_σ _]] => unfold waiting_σ
         | [|- context[waiting_ψ _]] => unfold waiting_ψ
         | [|- context[waiting_ϕ _]] => unfold waiting_ϕ
         end.

Lemma dom_unique :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    unique d.
Proof.
  intros A B HeqClass m d Hdom;
    induction Hdom;
    auto.
Qed.

Lemma adaptation_exists :
  forall σ1 σ2, finite_σ σ1 ->
           finite_σ σ2 ->
           not_stuck_σ σ2 ->
           forall χ1 ϕ1 ψ1
             χ2 ϕ2 ψ2,
             σ1 = (χ1, ϕ1::ψ1) ->
             σ2 = (χ2, ϕ2::ψ2) ->
             exists σ, σ1 ◁ σ2 ≜ σ.
Proof.
  intros.
  
  unfold not_stuck_σ, not_stuck_ϕ in H1.
  destruct H1 as [ϕ' Hnstuck];
    destruct Hnstuck as [ψ' Hnstuck];
    andDestruct.
  inversion Hb; subst; simpl in *;
    inversion Ha; subst.
  
  remember (vMap ϕ1) as β1.
  destruct (exists_dom_finite β1) as [zs]; auto;
    [subst; finite_auto; 
     apply H; crush|].
  remember (vMap ϕ') as β2.
  
  destruct (fresh_var_list_finite β1 zs H1 β2 s) as [zs' Hfresh];
    [finite_auto; crush
    |destruct Hfresh as [D Hfresh];
     andDestruct].

  (exists (χ2, (frm (updates D β1 β2) (c_stmt (rename_s s D)))::ψ')).
  apply a_adapt
    with
      (ϕ:=ϕ1)(ϕ':=ϕ')(contn:=contn ϕ1)
      (β:=β1)(β':=β2)(β'':=updates D β1 β2)
      (zs:=zs)(zs':=zs')(s:=s)
      (s':=rename_s s D)(Zs:=D);
    auto;
    try solve [crush].
  destruct ϕ1;
    f_equal;
    auto.
  destruct ϕ';
    f_equal;
    auto.

  eapply dom_unique; eauto.
  
Qed.

Inductive finite_normal_form {A B : Type} `{Eq A} : partial_map A B -> Prop :=
| norm_empty : finite_normal_form empty
| norm_update : forall a b m, finite_normal_form m ->
                         m a = None ->
                         finite_normal_form (update a b m).

Hint Constructors finite_normal_form.

Lemma compose_normal_form :
  forall {A B : Type}`{Eq A}`{Eq B} (m1 : partial_map A B),
    finite_normal_form m1 ->
    forall {C : Type} (m2 : partial_map B C),
    exists m3, finite_normal_form m3 /\ m3 = compose m1 m2.
Proof.
  intros A B HeqClassA HeqClassB m1 Hnorm;
    induction Hnorm;
    intros;
    auto.

  exists empty; auto.

  destruct (IHHnorm C m2) as [m3 IH];
    destruct IH as [IH1 IH2].
  destruct (partial_map_dec b m2)
    as [HSome|HNone];
    [destruct HSome as [c HSome]|].
  unfold compose;
    exists (update a c m3);
    split;
    [apply norm_update;
     subst m3;
     unfold compose; [auto|crush]|].
    apply functional_extensionality;
    intros a';
    pmap_simpl;
    crush.
  exists m3;
    split;
    auto.
  subst; unfold compose; auto.
  apply functional_extensionality;
    intros c;
    pmap_simpl;
    crush.
Qed.

Lemma update_finite_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite_normal_form m ->
    forall a b, exists m', finite_normal_form m' /\ m' = (update a b m).
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    intros;
    [exists (update a b empty); auto|].

  destruct (IHHfinite a0 b0) as [m' Hnorm];
    destruct Hnorm as [Hnorm Heqm'].

  destruct (eq_dec a0 a) as [Heq|Hneq];
    [subst a0
    |].

  exists m'; split; auto;
    apply functional_extensionality;
    intros a';
    subst;
    pmap_simpl.

  exists (update a b m');
    split.

  destruct (partial_map_dec a m') as [HSome|HNone];
    [destruct HSome as [b' HSome]; subst; pmap_simpl; crush
    |apply norm_update; auto].

  apply functional_extensionality; intros a'; pmap_simpl; subst.
  rewrite neq_eqb; auto.
  destruct (eq_dec a' a0) as [Heqa'|Hneqa'];
    [subst; pmap_simpl|pmap_simpl].
Qed.

Lemma finite_exists_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    exists m', finite_normal_form m' /\ m' = m.
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    [exists empty; auto|].

  apply update_finite_normal_form; crush.
Qed.

Lemma finite_normal_form_implies_finite :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite_normal_form m ->
    finite m.
Proof.
  intros A B HeqClass m Hnorm;
    induction Hnorm;
    auto.
Qed.

Lemma finite_implies_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    finite_normal_form m.
Proof.
  intros.
  destruct (finite_exists_normal_form m);
    andDestruct;
    subst;
    auto.
Qed.

Hint Resolve finite_implies_normal_form finite_exists_normal_form finite_normal_form_implies_finite
     compose_normal_form.

Lemma finite_map_composition :
  forall {A B : Type}`{Eq A}`{Eq B} (m1 : partial_map A B),
    finite m1 ->
    forall {C : Type} (m2 : partial_map B C),
      finite (compose m1 m2).
Proof.
  intros.
  destruct (compose_normal_form m1 (finite_implies_normal_form m1 H1) m2); eauto.
  andDestruct; subst.
  apply finite_normal_form_implies_finite; auto.
Qed.

Ltac peek_pop_simpl :=
  match goal with
  | [H : peek ?ψ = Some ?ϕ |- _] => let ϕ' := fresh "ϕ'" in
                                  let ψ' := fresh "ψ'" in
                                  destruct ψ as [|ϕ' ψ'];
                                  simpl in H;
                                  inversion H;
                                  subst
  | [H : pop ?ψ = Some ?ψ' |- _] => let ϕ' := fresh "ϕ'" in
                                  let ψ'' := fresh "ψ''" in
                                  destruct ψ as [|ϕ' ψ'];
                                  simpl in H;
                                  inversion H;
                                  subst
  end.

Lemma reduction_preserves_config_finiteness :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             finite_σ σ1 ->
             finite_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    finite_auto;
    simpl in *;
    intros;
    auto.

  destruct H as [Ha|Ha];
    [|destruct Ha as [Ha|Ha]];
    subst;
    simpl;
    [apply fin_update;
     apply finite_map_composition;
     auto
    | |];
    peek_pop_simpl;
    crush.

  peek_pop_simpl;
  unfold update_ψ_map, update_ϕ_map in H0;
    inversion H0;
    subst;
    [simpl; apply fin_update|];
    apply H9; crush.

  destruct H; [subst; simpl|]; eauto.

  peek_pop_simpl.
  destruct H0; crush.

  unfold update_ϕ_contn, update_ϕ_map in H; simpl in H;
    destruct H; crush.

  peek_pop_simpl.
  unfold update_ϕ_contn, update_ϕ_map in H; simpl in H;
    destruct H; crush.
  apply fin_update.
  peek_pop_simpl.
  simpl in H1;
    inversion H1; subst; crush.

  peek_pop_simpl.
  apply H9; crush.
Qed.

Hint Resolve reduction_preserves_config_finiteness.

Lemma reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    crush;
    eauto.
Qed.

Hint Resolve reductions_preserves_config_finiteness.

Lemma pair_reduction_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    subst;
    intros;
    crush;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_finiteness.

Lemma pair_reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    subst;
    intros;
    eauto.
Qed.

Hint Resolve pair_reductions_preserves_config_finiteness.

Lemma reduction_preserves_config_not_stuck :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             not_stuck_σ σ1 ->
             not_stuck_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    unfold not_stuck_σ in *;
    simpl in *;
    try solve [eexists; crush; eauto].

  exists ϕ'', (ϕ'::ψ'); split;
    unfold not_stuck_ϕ;
    subst;
    simpl in *;
    eauto.

  subst σ'; simpl;
    exists ϕ', ψ;
    split;
    auto;
    subst ϕ';
    unfold not_stuck_ϕ;
    simpl;
    auto.

  subst σ'; simpl;
    exists ϕ', ψ';
    split;
    auto;
    subst ϕ';
    unfold not_stuck_ϕ;
    simpl;
    auto.

  exists ϕ'', ψ;
    split;
    auto;
    subst ϕ'';
    unfold not_stuck_ϕ;
    simpl;
    auto.

  exists ϕ'', ψ'';
    split;
    auto;
    subst ϕ'';
    unfold not_stuck_ϕ;
    simpl;
    auto.
Qed.

Hint Resolve reduction_preserves_config_not_stuck.

Lemma reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve reductions_preserves_config_not_stuck.

Lemma pair_reduction_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_not_stuck.

Lemma pair_reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reductions_preserves_config_not_stuck.

Lemma reduction_preserves_config_waiting :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             waiting_σ σ1 ->
             waiting_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    unfold waiting_σ in *;
    simpl in *;
    try solve [eexists; crush; eauto].

  exists ϕ'', (ϕ'::ψ'); split;
    unfold waiting_ψ, waiting_ϕ in *;
    subst;
    intros;
    eauto;
    crush.

  exists ϕ'', ψ;
    split;
    auto;
    subst ϕ'';
    unfold waiting_ψ, waiting_ϕ in *;
    simpl;
    auto;
    crush.

  exists ϕ'', ψ'';
    split;
    auto;
    subst ϕ'';
    unfold waiting_ψ, waiting_ϕ in *;
    simpl;
    auto;
    crush.
  peek_pop_simpl; crush.
Qed.

Hint Resolve reduction_preserves_config_waiting.

Lemma reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve reductions_preserves_config_waiting.

Lemma pair_reduction_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_waiting.

Lemma pair_reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reductions_preserves_config_waiting.

Lemma has_self_update_ϕ :
  forall χ ϕ, has_self_ϕ χ ϕ ->
       forall x v, x <> this ->
              has_self_ϕ χ (update_ϕ_map ϕ x v).
Proof.
  intros χ ϕ Hself;
    inversion Hself;
    intros;
    subst.
  destruct H as [α Ha];
    destruct Ha as [o Ha];
    andDestruct.
  apply self_frm.
  exists α, o; simpl;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.
Qed.

Lemma has_self_update_σ :
  forall σ, has_self_σ σ ->
       forall x v, x <> this ->
              has_self_σ (update_σ_map σ x v).
Proof.
  intros σ Hself;
    inversion Hself;
    intros;
    subst.
  apply self_config;
    intros;
    simpl in *.
  unfold update_ψ_map in H0;
    destruct ψ as [|ϕ' ψ'];
    [crush|inversion H0; subst].
  apply has_self_update_ϕ;
    auto.
  apply H, in_eq.

  apply H, in_cons; auto.
Qed.

Lemma has_self_update_ϕ_contn :
  forall χ ϕ, has_self_ϕ χ ϕ ->
       forall c, has_self_ϕ χ (update_ϕ_contn ϕ c).
Proof.
  intros.
  inversion H;
    subst.
  destruct H0 as [α Ha];
    destruct Ha as [o];
    andDestruct.
  apply self_frm;
  exists α, o; simpl; auto.
Qed.

Lemma has_self_update_σ_contn :
  forall σ, has_self_σ σ ->
       forall c, has_self_σ (update_σ_contn σ c).
Proof.
  intros σ Hself;
    inversion Hself;
    intros;
    subst.
  apply self_config;
    intros;
    simpl in *.
  
  unfold update_ψ_contn in H0;
    destruct ψ as [|ϕ' ψ'];
    [crush|inversion H0; subst].
  apply has_self_update_ϕ_contn.
  apply H, in_eq.
  apply H, in_cons;
    auto.
Qed.

Lemma reduction_preserves_config_has_self :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             has_self_σ σ1 ->
             has_self_σ σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros Hself;
    inversion Hself;
    subst;
    eauto.

  inversion H12; subst.

  (* s_meth *)
  apply self_config;
    intros ϕ' Hin;
    inversion Hin;
    auto;
    [subst|].
  apply self_frm;
    exists α, o;
    split;
    auto.
  inversion H;
    subst.
  peek_pop_simpl;
    simpl in H1;
    inversion H1;
    subst.
  assert (Hinϕ : In ϕ (ϕ::ψ'));
    [apply in_eq|apply H11 in Hinϕ].
  apply self_frm;
    inversion Hinϕ;
    auto.
  apply H11;
    peek_pop_simpl;
    simpl in *;
    inversion H1;
    auto.

  (* var asgn *)
  apply has_self_update_σ;
    auto.

  (* field asgn*)
  inversion H12;
    subst.
  apply self_config;
    intros.
  inversion H;
    subst;
    remember {| cname := cname o; flds := update f (v_addr α') (flds o); meths := meths o |} as o'.
  assert (Hin : In ϕ (ϕ::ψ));
    [apply in_eq|apply H11 in Hin].
  destruct Hin.
  destruct H7 as [α0 Ha];
    destruct Ha as [o0];
    andDestruct.
  apply self_frm.
  exists α0.
  destruct (eq_dec α0 α) as [|Hneq];
    [subst α0;
     exists o'
    |simpl;
     exists o0];
     split;
     simpl;
     auto;
     unfold update, t_update;
     [rewrite eqb_refl; auto
     |rewrite neq_eqb; auto].  
  assert (Hin : In ϕ0 (ϕ::ψ));
    [apply in_cons; auto|apply H11 in Hin].
  destruct Hin.
  destruct H8 as [α0 Ha];
    destruct Ha as [o0];
    andDestruct.
  apply self_frm.
  exists α0.
  destruct (eq_dec α0 α) as [|Hneq];
    [subst α0;
     exists o'
    |simpl;
     exists o0];
     split;
     simpl;
     auto;
     unfold update, t_update;
     [rewrite eqb_refl; auto
     |rewrite neq_eqb; auto].

  (* new *)
  inversion H13;
    subst.
  apply self_config;
    intros.
  inversion H0;
    subst;
    remember {| cname := C; flds := compose fMap (vMap ϕ); meths := c_meths CDef |} as o'.
  apply self_frm; simpl.
  assert (Hin : In ϕ ψ);
    [peek_pop_simpl;
     simpl in *;
     inversion H1;
     subst;
     crush|
     apply H12 in Hin].
  destruct Hin as [χ ϕ Ha];
    destruct Ha as [α0 Ha];
    destruct Ha as [o0];
    andDestruct.
  exists α0.
  destruct (eq_dec α0 α) as [|Hneq];
    [subst α0;
     exists o'
    |simpl;
     exists o0];
     simpl;
     auto;
     unfold update, t_update;
     [rewrite neq_eqb; auto
     |rewrite neq_eqb; auto];
     split;
     auto;
     [rewrite eqb_refl
     |rewrite neq_eqb; auto];
     auto.

  apply self_frm.
  unfold update, t_update.
  peek_pop_simpl;
    simpl in H1;
    inversion H1;
    subst.
  assert (Hin : In ϕ0 (ϕ::ψ'));
    [apply in_cons; auto
    |apply H12 in Hin;
     destruct Hin as [χ ϕ' Ha];
     destruct Ha as [α0 Ha];
     destruct Ha as [o0];
     andDestruct].
  exists α0.
  remember {| cname := C; flds := compose fMap (vMap ϕ); meths := c_meths CDef |} as o'.
  destruct (eq_dec α0 α) as [|Hneq];
    [subst α0;
     exists o'
    |exists o0];
     [rewrite eqb_refl; auto
     |rewrite neq_eqb; auto];
     auto.

  (* ret 1 *)
  apply self_config;
    intros.
  inversion H6;
    subst.
  inversion H;
    subst.
  apply has_self_update_ϕ_contn, has_self_update_ϕ;
    auto.
  apply H5, in_cons, in_eq.
  apply H5, in_cons, in_cons;
    auto.

  (* ret 2*)
  apply self_config;
    intros.
  peek_pop_simpl;
    simpl in *;
    inversion H0;
    inversion H1;
    inversion H2;
    inversion H3;
    subst.
  inversion H10;
    subst.
  inversion H;
    subst.
  apply has_self_update_ϕ_contn, has_self_update_ϕ;
    auto.
  apply H9.
  peek_pop_simpl.
  simpl in H1;
    inversion H1;
    subst.
  apply in_cons, in_eq.
  peek_pop_simpl;
    inversion H12;
    subst.
  apply H9, in_cons, in_cons;
    auto.
Qed.

Hint Resolve reduction_preserves_config_has_self.

Lemma reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve reduction_preserves_config_has_self.

Lemma pair_reduction_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
  eapply reduction_preserves_config_has_self;
    eauto.
  eapply reductions_preserves_config_has_self;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_has_self.

Lemma pair_reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reductions_preserves_config_has_self.

Lemma reduction_preserves_config_wf :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             σ_wf σ1 ->
             σ_wf σ2.
Proof.
  intros M σ1 σ2 Hred Hwf;
    inversion Hred;
    subst;
    apply config_wf;
    inversion Hwf;
    eauto;
    subst.
Qed.

Hint Resolve reduction_preserves_config_wf.

Lemma reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
             σ_wf σ1 ->
             σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    eauto.
Qed.

Hint Resolve reductions_preserves_config_wf.

Lemma pair_reduction_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_config_wf.

Lemma pair_reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto.
Qed.

Hint Resolve pair_reductions_preserves_config_wf.

Lemma config_head_wf :
  forall σ, σ_wf σ ->
       forall χ ϕ ψ, σ = (χ, ϕ::ψ) ->
                σ_wf (χ, ϕ::nil).
Proof.
  intros;
    subst.
  inversion H;
    subst;
    apply config_wf;
    finite_auto; not_stuck_auto; waiting_auto;
      try solve [crush].
  apply self_config;
    intros ϕ' Hin;
    inversion Hin;
    subst;
    inversion H0;
    subst.
  apply H5, in_eq.
  inversion H4.
  
  exists ϕ, nil; split; auto; crush.
  exists ϕ, nil; split; auto; crush.
Qed.

Hint Resolve config_head_wf.

Lemma config_wf_decompose :
  forall σ, σ_wf σ ->
       exists χ ϕ ψ, σ = (χ, ϕ::ψ).
Proof.
  intros σ Hwf;
    inversion Hwf;
    subst;
    not_stuck_auto.
  destruct H1 as [ϕ Hns];
    destruct Hns as [ψ];
    andDestruct.
  exists (fst σ), ϕ, ψ; destruct σ; crush.
Qed.

Theorem eval_unique :
  forall M σ e v1, M ∙ σ ⊢ e ↪ v1 ->
              forall v2, M ∙ σ ⊢ e ↪ v2 ->
                    v2 = v1.
Proof.
  intros M σ e v1 Heval;
    induction Heval;
    intros;
    try solve [inversion H; subst; [eauto| eauto];
               apply IHHeval1 in H6; inversion H6].

  (** Case 1: eval v *)
  inversion H; eauto.

  (** Case 2: eval x *)
  inversion H0; subst; crush.

  (** Case 3: e.f *)
  inversion H1; subst; crush.
  apply IHHeval in H4; subst; crush.

  (** Case 4: e0.g(e) *)
  inversion H2; subst.
  apply IHHeval1 in H6; inversion H6; subst.
  rewrite H7 in H; inversion H; subst.
  rewrite H8 in H0; inversion H0; subst.
  rewrite H11 in H1; inversion H1; subst.
  apply IHHeval2 in H13; subst.
  apply IHHeval3 in H14; subst; auto.

  (** Case 5: e1 = e2 *) 
  inversion H; subst; eauto.
  apply IHHeval1 in H2; apply IHHeval2 in H5; subst; crush.

  (** Case 6: e1 ≠ e2 *)
  inversion H0; subst; eauto.
  apply IHHeval1 in H5; apply IHHeval2 in H7; subst; crush.
Qed.

Hint Rewrite eval_unique.

Ltac eval_rewrite :=
  repeat match goal with
         | [H1 : ?M ∙ ?σ ⊢ ?e ↪ ?v1, H2 : ?M ∙ ?σ ⊢ ?e ↪ ?v2 |- _] =>
           eapply (eval_unique M σ e v1 H1) in H2;
           eauto;
           subst
         end.

Lemma unique_interpretation_x :
  forall x σ v1, ⌊ x ⌋ σ ≜ v1 ->
            forall v2, ⌊ x ⌋ σ ≜ v2 ->
                  v2 = v1.
Proof.
  intros x σ v1 Hint1 v2 Hint2;
    inversion Hint1;
    inversion Hint2;
    subst.
  rewrite H6 in H0;
    inversion H0;
    subst.
  rewrite H7 in H1;
    inversion H1;
    subst;
    auto.
Qed.

Lemma unique_interpretation_Σ :
  forall Σ σ αs1, ⌊ Σ ⌋ σ ≜′ αs1 ->
            forall αs2, ⌊ Σ ⌋ σ ≜′ αs2 ->
                   αs2 = αs1.
Proof.
  intros x σ α1 Hint1;
    induction Hint1;
    intros αs2 Hint2;
    inversion Hint2;
    subst;
    auto.
  eapply (unique_interpretation_x x σ α) in H2;
    subst;
    eauto.
  rewrite (IHHint1 αs0); auto.
Qed.

Ltac interpretation_rewrite :=
  repeat match goal with
         | [H1 : ⌊ ?x ⌋ ?σ ≜ ?v1, H2 : ⌊ ?x ⌋ ?σ ≜ ?v2 |- _] =>
           eapply (unique_interpretation_x x σ v1 H1) in H2;
           eauto;
           subst
         | [H1 : ⌊ ?Σ ⌋ ?σ ≜′ ?αs1, H2 : ⌊ ?Σ ⌋ ?σ ≜′ ?αs2 |- _] =>
           eapply (unique_interpretation_Σ Σ σ αs1 H1) in H2;
           eauto;
           subst
         end.

Lemma wf_σ_explode :
  forall σ, σ_wf σ ->
       exists χ ψ ϕ, σ = (χ, ϕ::ψ) /\
                finite (vMap ϕ) /\
                (forall ϕ', In ϕ' ψ ->
                       finite (vMap ϕ')) /\
                not_stuck (contn ϕ) /\
                (forall ϕ', In ϕ' ψ ->
                       waiting (contn ϕ')).
Proof.
  intros σ Hwf;
    inversion Hwf;
    subst;
    destruct σ as [χ ψ];
    finite_auto;
    not_stuck_auto;
    waiting_auto;
    crush;
    eexists;
    eexists;
    eexists;
    split;
    eauto;
    split;
    eauto.
Qed.

Ltac config_wf_destruct :=
  match goal with
  | [H : σ_wf ?σ |-_] =>
    apply wf_σ_explode in H;
    let χ := fresh "χ" in
    let ψ := fresh "ψ" in
    let ϕ := fresh "ϕ" in
    let Hwf := fresh "Hwf" in
    destruct H as [χ Hwf];
    destruct Hwf as [ψ Hwf];
    destruct Hwf as [ϕ Hwf];
    let Htmp := fresh "Htmp" in
    let Hfiniteϕ := fresh "Hfiniteϕ" in
    let Hfiniteψ := fresh "Hfiniteψ" in
    let Hnot_stuck := fresh "Hnot_stuck" in
    let Hwaiting := fresh "Hwaiting" in
    destruct Hwf as [Htmp Hwf];
    destruct Hwf as [Hfiniteϕ Hwf];
    destruct Hwf as [Hfiniteψ Hwf];
    destruct Hwf as [Hnot_stuck Hwaiting];
    subst σ
  end.

Definition one_to_one {A B : Type} `{Eq A} (m : partial_map A B) : Prop :=
  forall a1 a2 b, m a1 = Some b ->
             m a2 = Some b ->
             a1 = a2.

(** TODO: *)
Parameter function_neq_exists_neq_mapping  :
    forall {A B : Type} (f1 f2 : A -> B),
      f1 <> f2 ->
      exists a, f1 a <> f2 a.

(*Lemma compose_equality :
  forall {A B C : Type} `{Eq A} `{Eq B} (m1 m2 : partial_map A B) (m : partial_map B C),
    compose m1 m = compose m2 m ->
    one_to_one m ->
    m1 = m2.
Proof.
  intros.
  destruct (excluded_middle (m1 = m2));
    auto.
  destruct (function_neq_exists_neq_mapping m1 m2) as [a Ha];
    auto.
  apply equal_f with (x:=a) in H1.
  unfold compose in H1.
  destruct (m1 a) as [b1|];
    destruct (m2 a) as [b2|].

  remember (m b1) as res1;
    remember (m b2) as res2;
    symmetry in Heqres1;
    symmetry in Heqres2.
  destruct (res1) as [c1|];
    destruct (res2) as [c2|];
    try solve [inversion H1].
  inversion H1; subst c1.
  apply (H2 b1 b2) in Heqres1; crush.
  
  
  contradiction H3.
  
  apply functional_extensionality;
    intros a.
  
Qed.*)

(** This theorem is not currently provable since there is not restriction on what the fresh variables could be. I can change this so that the fresh variables are deterministic during adaptation *)
Theorem adaptation_unique :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall σ', σ1 ◁ σ2 ≜ σ' ->
                   σ' = σ.
Proof.
  intros σ1 σ2 σ Hadapt1 σ' Hadapt2;
    inversion Hadapt1;
    inversion Hadapt2;
    subst.
  peek_pop_simpl; simpl in *.
  inversion H; subst.
  inversion H16; subst;
    auto.
Admitted.


Ltac adapt_rewrite :=
  repeat match goal with
         | [H1 : ?σ1 ◁ ?σ2 ≜ ?σ, H2 : ?σ1 ◁ ?σ2 ≜ ?σ' |- _] =>
           eapply (adaptation_unique σ1 σ2 σ H1) in H2;
           eauto;
           subst
         end.

Lemma pair_reductions_transitive :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ3 ->
                       M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Lemma notin_updates :
  forall {A B : Type} `{Eq A} zs zs' (Zs : list (A * A)),
    zip zs zs' Zs ->
    forall z, ~ In z zs ->
         forall (β β' : partial_map A B), updates Zs β β' z = β z.
Proof.
  intros A B HeqClass zs;
    induction zs;
    intros zs' Zs Hzip;
    inversion Hzip;
    subst;
    intros;
    simpl;
    auto.

  destruct (eq_dec z a) as [Heq|Hneq];
    [subst; contradiction H; apply in_eq
    |rewrite neq_eqb; auto;
     eapply IHzs; auto;
     [inversion Hzip; eauto
     |intro Hcontra; contradiction H; apply in_cons; auto]].
Qed.

Lemma adaptation_preserves_mapping :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall z (v : value), common.map σ1 z = Some v ->
                              common.map σ z = Some v.
Proof.
  intros.
  inversion H;
    subst.

  unfold common.map, configMapStack, common.map in *; simpl.
  destruct σ1 as [χ ψ]; simpl in H0.
  destruct ψ as [|ϕ ψ]; simpl in H0;
    [inversion H0| ].
  simpl in *.
  inversion H1; subst; simpl in *.
  destruct (in_dec (eq_dec) z zs').
  apply H5 in i.
  unfold fresh_in_map in i.
  apply i in  H0; crush.
  erewrite notin_updates; eauto.
Qed.

(* fresh  *)

Lemma update_fresh_preserves_map :
  forall x σ A, fresh_x x σ A ->
           forall z v v', common.map σ z = Some v ->
                     common.map (update_σ_map σ x v') z = Some v.
Proof.
  intros x σ A Hfrsh;
    inversion Hfrsh;
    subst;
    intros.

  destruct σ as [χ ψ];
    destruct ψ as [|ϕ ψ].

  unfold common.map, configMapStack, common.map, stackMap in *;
    simpl in *;
    crush.

  unfold common.map, configMapStack, common.map, stackMap in *;
    simpl in *.
  unfold update, t_update;
    destruct (eq_dec z x) as [|Hneq];
    [subst; crush
    |rewrite neq_eqb; auto].
Qed.

Lemma fresh_and_elim :
  forall x σ A1 A2,
    fresh_x x σ (A1 ∧ A2) ->
    fresh_x x σ A1 /\ fresh_x x σ A2.
Proof.
  intros.
  inversion H;
    subst.

  inversion H1;
    subst;
    auto.
Qed.

Lemma fresh_and_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ∧ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto.
Qed.

Lemma fresh_arr_elim :
  forall x σ A1 A2,
    fresh_x x σ (A1 ⇒ A2) ->
    fresh_x x σ A1 /\ fresh_x x σ A2.
Proof.
  intros.
  inversion H;
    subst.

  inversion H1;
    subst;
    auto.
Qed.

Lemma fresh_arr_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ⇒ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto.
Qed.

Lemma fresh_all_elim :
  forall x σ A,
    fresh_x x σ (∀x∙A) ->
    fresh_x x σ A.
Proof.
  intros.
  inversion H;
    subst;
    inversion H1;
    auto.
Qed.

Lemma fresh_all_intro :
  forall x σ A,
    fresh_x x σ A ->
    fresh_x x σ (∀x∙A).
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma fresh_notin :
  forall x σ A1 A2,
    fresh_x x σ A1 ->
    notin_Ax A2 x ->
    fresh_x x σ A2.
Proof.
  intros x σ A1 A2 Hfrsh Hnotin.
  inversion Hfrsh; auto.
Qed.

(* update map *)

Lemma map_update_σ :
  forall σ z v, (exists ϕ ψ, snd σ = ϕ :: ψ) ->
           common.map (update_σ_map σ z v) z = Some v.
Proof.
  intros.
  unfold common.map, configMapStack, common.map, stackMap.
  destruct σ as [χ ψ];
    destruct ψ as [|ϕ ψ];
    simpl.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ Ha];
    crush.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
Qed.

Lemma reduction_preserves_addr_classes :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall (α : addr) o1,
               common.map σ1 α = Some o1 ->
               exists o2, common.map σ2 α = Some o2 /\
                     cname o2 = cname o1.
Proof.
  intros M σ1 σ2 Hred;
    destruct Hred;
    intros;
    subst;
    eauto;
    unfold common.map, configMapHeap in *;
    simpl in *.

  destruct (eq_dec α0 α) as [|Hneq];
    [subst|].
  exists {| cname := cname o; flds := update f (v_addr α') (flds o); meths := meths o |};
    simpl;
    unfold update, t_update;
    rewrite eqb_refl;
    split;
    simpl;
    crush.

  exists o1;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.

  destruct (eq_dec α0 α) as [|Hneq];
    [subst; crush|].

  exists o1;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.
  
Qed.

Hint Resolve reduction_preserves_addr_classes.
Hint Rewrite reduction_preserves_addr_classes.

Lemma reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall (α : addr) o1,
                   common.map σ1 α = Some o1 ->
                   exists o2, common.map σ2 α = Some o2 /\
                   cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.

  destruct IHHred with (α:=α)(o1:=o1) as [o Hclass];
    eauto; auto;
      andDestruct.

  edestruct reduction_preserves_addr_classes as [o' Hclass1];
    eauto.

  andDestruct.

  eexists; split; eauto; crush.
Qed.

Hint Resolve reductions_preserves_addr_classes.
Hint Rewrite reductions_preserves_addr_classes.

Lemma pair_reduction_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall (α : addr) o1,
                   common.map σ1 α = Some o1 ->
                   exists o2, common.map σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Hint Resolve pair_reduction_preserves_addr_classes.
Hint Rewrite pair_reduction_preserves_addr_classes.

Lemma pair_reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall (α : addr) o1,
                   common.map σ1 α = Some o1 ->
                   exists o2, common.map σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.

  destruct (pair_reduction_preserves_addr_classes M1 M2 σ1 σ)
    with
      (α:=α)(o1:=o1)
    as [o Hclass1];
    auto;
    andDestruct.

  edestruct IHHred as [o' Hclass2];
    eauto;
    andDestruct.

  eexists; split; eauto; crush.
  
Qed.

Hint Resolve pair_reductions_preserves_addr_classes.
Hint Rewrite pair_reductions_preserves_addr_classes.

Lemma reductions_implies_method_call :
  forall M1 M2 σ1 σ2,
    M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
    σ_wf σ1 ->
    exists χ ϕ ψ,
      σ1 = (χ, ϕ::ψ) /\
      ((exists x y m ps, contn ϕ = c_stmt (s_meth x y m ps) \/
                    exists s, contn ϕ = c_stmt (s_stmts (s_meth x y m ps) s)) \/
       (exists x, contn ϕ = c_stmt (s_rtrn x) \/
                    exists s, contn ϕ = c_stmt (s_stmts (s_rtrn x) s))).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    auto.
  inversion H0;
    subst.

  (*meth call*)
  exists χ, ϕ, ψ';
    split;
    [|left;
      exists x, y, m, ps; eauto].
  peek_pop_simpl;
    simpl in H5;
    inversion H5;
    subst;
    auto.

  (* var asgn *)
  inversion H8;
    subst.
  remember (cname o0) as C.
  destruct H2 with (C:=C) as [CDef].
  apply cls_of with (α:=α0)(χ:=χ)(o:=o0);
    auto.
  peek_pop_simpl.
  apply int_x with (ψ:=update_ϕ_map ϕ x v :: ψ')
                   (ϕ:=update_ϕ_map ϕ x v);
    auto.
  unfold update_ϕ_map, update, t_update; simpl.
  destruct x as [n];
    destruct n as [|n'];
    [crush|].
  inversion H4;
    subst;
    auto.
  simpl in *;
    inversion H14;
    subst;
    auto.
  rewrite H1 in H12;
    auto;
    crush.

  (* f asgn *)
  inversion H7;
    subst;
    simpl in *.
  remember (cname o0) as C.
  destruct H2 with (C:=C) as [CDef].
  remember ({| cname := cname o; flds := update f (v_addr α') (flds o); meths := meths o |})
    as o'.
  destruct (eq_dec α0 α) as [|Hneq];
    [subst α0;
     apply cls_of
       with
         (α:=α)
         (χ:=update α o' χ)
         (o:=o');
     auto
    |apply cls_of
       with
         (α:=α0)
         (χ:=update α o' χ)
         (o:=o0);
     auto].
  apply int_x with (ψ:={| vMap := vMap ϕ; contn := c_stmt s |} :: ψ)
                   (ϕ:={| vMap := vMap ϕ; contn := c_stmt s |});
    auto;
    simpl.
  inversion H3;
    subst;
    simpl in *.
  inversion H13;
    subst;
    auto.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
  subst;
    simpl;
    crush.

  apply int_x with (ψ:={| vMap := vMap ϕ; contn := c_stmt s |} :: ψ)
                   (ϕ:={| vMap := vMap ϕ; contn := c_stmt s |});
    auto;
    simpl.
  inversion H3;
    subst;
    simpl in *.
  inversion H13;
    subst;
    auto.
  unfold update, t_update;
    rewrite neq_eqb;
    auto.

  rewrite H1 in H11;
    crush.
  
  (* new *)
  intros.
  remember (update α {| cname := C; flds := compose fMap (vMap ϕ); meths := c_meths CDef |} χ,
            {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} :: ψ') as σ'.
  assert (Hthis : has_self_σ σ');
    [eapply reduction_preserves_config_has_self;
     inversion H4;
     subst;
     eauto|].
  subst;
    inversion Hthis;
    subst.
  remember {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} as σ'.
  assert (Hin : In σ' (σ'::ψ'));
    [apply in_eq|apply H14 in Hin].
  inversion Hin;
    subst;
    simpl in *.
  destruct H13 as [α' Ha];
    destruct Ha as [o'];
    andDestruct.
  unfold update, t_update in Ha;
    rewrite neq_eqb in Ha;
    auto.
  peek_pop_simpl.
  destruct (eq_dec α' α) as [|Hneq];
    [subst
    |].
  inversion H4;
    subst.
  inversion H13;
    subst.
  assert (Hin' : In ϕ (ϕ::ψ'0));
    [apply in_eq|apply H19 in Hin'].
  inversion Hin';
    subst.
  destruct H18 as [α0 Hx];
    destruct Hx as [o0];
    andDestruct.
  rewrite Ha0 in Ha;
    inversion Ha;
    subst.
  crush.

  unfold update, t_update in Hb;
    rewrite neq_eqb in Hb;
    auto.
  remember {| cname := C; flds := compose fMap (vMap ϕ); meths := c_meths CDef |} as oα.
  destruct o' as [C' fs ms].
  destruct (H2 C') as [CDef'].
  remember {| cname := C'; flds := fs; meths := ms |} as o'.
  apply cls_of with (α:=α')(χ:=update α oα χ)(o:=o');
    auto.
  remember {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} as ϕ'.
  apply int_x with (ψ:=ϕ'::ψ')(ϕ:=ϕ');
    auto.
  subst; simpl;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.
  subst; simpl;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.
  crush.
  rewrite H1 in H13;
    auto;
    [crush|].
  
  remember {| cname := C'; flds := fs; meths := ms |} as o'.
  apply cls_of with (α:=α')(χ:=χ)(o:=o');
    auto;
    [|crush].
  apply int_x with (ϕ:=ϕ)(ψ:=ϕ::ψ'0);
    auto.

  (* ret 1 *)
  intros Hwf;
    inversion Hwf;
    subst.
  exists χ, ϕ, (ϕ'::ψ);
    split;
    [auto|eauto].

  (* ret 1 *)
  intros Hwf;
    inversion Hwf;
    subst.
  repeat peek_pop_simpl;
    simpl in *.
  exists χ, ϕ, ψ';
    split;
    [auto|eauto].
Qed.
