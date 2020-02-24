Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** #<h1># Basic Arithmetic Assertions: #</h1># *)

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

  - (*field assign reduce*)
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
      [destruct f0; subst; rewrite <- beq_nat_refl; exists v; auto
      |destruct f0, f;
       assert (Hneq' : n <> n0);
       [intros Hcontra; subst; crush| apply Nat.eqb_neq in Hneq'; rewrite Hneq'; auto]].

  - (*new object initialization*)
    simpl in *.
    unfold update, t_update in H0.
    destruct (eq_dec α0 α) as [Heq|Hneq];
      [subst; rewrite eqb_refl in H0
      |apply neq_eqb in Hneq; rewrite Hneq in H0;
       inversion H9; subst; apply (H6 α0); auto].
    exists CDef;
      split; [inversion H0; subst; auto
             |split;
              [intros
              |inversion H0; subst; auto]].
    inversion H0; subst; simpl.
    assert (Hin : fMap f = None -> ~ In f (c_flds CDef));
      [intros;
       apply not_in_map_implies_not_in_dom with (m:=fMap); auto
      |].
    remember (fMap f) as res.
    destruct res as [y|];
      [
      |contradiction Hin; auto].
    destruct (H5 f y) as [v];
      auto.
    exists v; auto.
Qed.

Lemma linking_unique :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             forall M', M1 ⋄ M2 ≜ M' ->
                   M' = M.
Proof.
  intros M1 M2 M Hlink1 M' Hlink2;
    inversion Hlink1; inversion Hlink2;
      subst;
      auto.
Qed.

Ltac link_unique_auto :=
  match goal with
  | [H1 : ?M1 ⋄ ?M2 ≜ ?M, H2 : ?M1 ⋄ ?M2 ≜ ?M' |-_] =>
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
                 forall M, M1 ⋄ M2 ≜ M ->
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
                 forall M, M1 ⋄ M2 ≜ M ->
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
                 forall M, M1 ⋄ M2 ≜ M ->
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
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
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
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush.
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush; eauto.
Qed.

Ltac linking_wf :=
  match goal with
  | [H1 : M_wf ?M1, H2 : M_wf ?M2, Hlink : ?M1 ⋄ ?M2 ≜ ?M |- M_wf ?M] => eapply linked_wf; eauto
  end.

Lemma arising_heap_wf :
  forall M1 M2 σ, arising M1 M2 σ ->
             M_wf M1 ->
             M_wf M2 ->
             forall M, M1 ⋄ M2 ≜ M ->
                  χ_wf M (fst σ).
Proof.
  intros.
  inversion H; subst.
  pair_reduces_heap_wf_auto.
  initial_heap_wf_auto.
  linking_wf.
Qed.

Lemma le_le_addr :
  forall α1 α2, le_α α1 α2 ->
           le_α α2 α1 ->
           α1 = α2.
Proof.
  intros α1 α2 Hle1 Hle2.
  inversion Hle1;
    inversion Hle2;
    crush.
Qed.

Hint Resolve le_le_addr : loo_db.
Hint Rewrite le_le_addr : loo_db.

Lemma heap_max_unique :
  forall (χ : heap) α, max_χ χ α ->
         forall α', max_χ χ α' ->
               α' = α.
Proof.
  intros χ α Hmax1 α' Hmax2.
  inversion Hmax1; inversion Hmax2;
    subst.
  crush.
  eauto with loo_db.
Qed.

Hint Resolve heap_max_unique : loo_db.
Hint Rewrite heap_max_unique : loo_db.

Lemma fresh_heap_unique :
  forall χ α1 α2, fresh_χ χ α1 ->
             fresh_χ χ α2 ->
             α1 = α2.
Proof.
  intros χ α1 α2 Hfrsh1 Hfrsh2;
    inversion Hfrsh1;
    inversion Hfrsh2;
    subst.
  match goal with
  | [H1 : max_χ ?χ ?α1,
          H2 : max_χ ?χ ?α2 |- _] => apply heap_max_unique with (α:=α2) in H1; subst; auto
  end.
Qed.

Hint Resolve fresh_heap_unique : loo_db.
Hint Rewrite fresh_heap_unique : loo_db.

Lemma fresh_heap_none :
  forall χ α, fresh_χ χ α ->
         χ α = None.
Proof.
  intros χ α Hfrsh;
    inversion Hfrsh;
    subst.
  inversion H; subst.
  apply not_some_implies_none;
    intros;
    intro Hcontra.
  apply H1 in Hcontra.
  inversion Hcontra; subst; simpl in *.
  crush.
Qed.

Hint Resolve fresh_heap_none : loo_db.
Hint Rewrite fresh_heap_none : loo_db.

Lemma fresh_heap_some_contradict :
  forall χ α, fresh_χ χ α ->
         forall o, ~ χ α = Some o.
Proof.
  intros χ α Hfrsh; intros; intro Hcontra.
  apply fresh_heap_none in Hfrsh; crush.  
Qed.

Hint Resolve fresh_heap_some_contradict : loo_db.

Lemma fresh_heap_some_contradiction :
  forall χ α, fresh_χ χ α ->
         forall o, χ α = Some o ->
              forall P, P.
Proof.
  intros χ α Hfrsh o; intros.
  apply fresh_heap_some_contradict with (o:=o) in Hfrsh;
    crush.
Qed.

(*Lemma zip_length_exists :
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
Qed.*)

Lemma fresh_in_empty :
  forall {A : Type} x, @fresh_in_map A x empty.
Proof.
  unfold fresh_in_map;
    intros.
  pmap_simpl.
Qed.

Hint Resolve fresh_in_empty : loo_db.

Lemma fresh_in_map_not_in_dom :
  forall {A : Type} (m : partial_map var A) d,
    dom m d ->
    forall x, fresh_in_map x m <-> ~ In x d.
Proof.
  intros A m d Hdom x;
    split;
    intros.

  - eapply not_in_map_implies_not_in_dom; eauto.

  - eapply not_in_dom_implies_not_in_map; eauto.
Qed.

Inductive lt_map {A : Type} : nat -> partial_map var A -> Prop :=
| lt_empty : lt_map 0 empty
| lt_update1 : forall n b m n', lt_map n' m ->
                           n < n' ->
                           lt_map n' (update (bnd n) b m)
| lt_update2 : forall n b m n', lt_map n' m ->
                           n' <= n ->
                           lt_map (S n) (update (bnd n) b m).

Hint Constructors lt_map : loo_db.

Lemma exists_limit_for_finite_map :
  forall {A : Type} (m : partial_map var A),
    finite m ->
    exists n, lt_map n m.
Proof.
  intros A m Hfinite;
    induction Hfinite;
    [exists 0; auto with loo_db|destruct IHHfinite as [n]].
  
  destruct a as [n'].
  destruct (le_lt_dec n n') as [Hle|Hlt];
    [exists (S n'); eapply lt_update2|exists n; apply lt_update1]; eauto.
Qed.

Lemma lt_map_implies_var_lt :
  forall {A : Type} n (m : partial_map var A),
    lt_map n m ->
    forall n' b, m (bnd n') = Some b ->
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
    lt_map n m -> forall n', n <= n' -> fresh_in_map (bnd n') m.
Proof.
  intros A n m Hlt;
    induction Hlt;
    auto with loo_db;
    unfold fresh_in_map in *;    
    intros.

  - repeat map_rewrite;
      simpl.
    match goal with
    | [Ha : ?n2 < ?n3,
            Hb : ?n3 <= ?n1 |-context[?n1 =? ?n2]] =>
      let Hneq := fresh in
      assert (Hneq : n1 <> n2);
        [crush
        |apply Nat.eqb_neq in Hneq;
         rewrite Hneq; eauto]
    end.

  - repeat map_rewrite;
      simpl.
    match goal with
    | [Ha : S ?n2 <= ?n1 |-context[?n1 =? ?n2]] =>
      let Hneq := fresh in
      assert (Hneq : n1 <> n2);
        [crush
        |apply Nat.eqb_neq in Hneq;
         rewrite Hneq]
    end.
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
    exists (bnd n);
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
    [exists (bnd n2)|exists (bnd n1)];
    split;
    eapply lt_fresh_in_map;
    eauto;
    crush.
Qed.

Inductive lt_var : nat -> var -> Prop :=
| lt_bind : forall n n', n' < n ->
                    lt_var n (bnd n').

Hint Constructors lt_var : loo_db.

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

    try solve [exists (bnd n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n3 n2) as [Hle3|Hlt3];

    try solve [exists (bnd n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n1 n3) as [Hle2|Hlt2];

    try solve [exists (bnd n1); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
Qed.

(*Lemma dom_implies_finite :
  forall {A : Type} (m : partial_map var A) d,
    dom m d ->
    finite m.
Proof.
  intros A m d Hdom;
    induction Hdom;
    crush.
Qed.*)
      
(*Lemma fresh_var_map :
  forall {A : Type} (β1 β2 : partial_map var A),
    finite_normal_form β1 ->
    finite_normal_form β2 ->
    forall s, exists f,
        disjoint_dom f β1 /\
        disjoint_dom f β2 /\
        (forall z z', f z = Some z' -> ~ in_stmt z s) /\
        onto f β2.
Proof.
  intros A β1 β2 Hfin;
    induction Hfin
Qed.*)

Lemma adaptation_exists :
  forall χ1 ϕ1 ψ1
    χ2 ϕ2 ψ2, finite_ϕ ϕ1 ->
              finite_ϕ ϕ2 ->
              not_stuck_ϕ ϕ2 ->
              forall σ1 σ2, σ1 = (χ1, ϕ1::ψ1) ->
                       σ2 = (χ2, ϕ2::ψ2) ->
                       exists σ, σ1 ◁ σ2 ≜ σ.
Proof.
  intros; subst.

  inversion H1; subst.

  remember (vMap ϕ1) as β1.
  remember (vMap ϕ2) as β2.
  let H := fresh in
  (destruct (@disjointedness_for_finite_variable_maps value value β1)
     with (g:=β2)(s:=s)
    as [f H];
   try solve [finite_auto; subst; eauto with map_db];
   destruct H as [f'];
   andDestruct).

  exists (χ2, (frm (f ∘ β2 ∪ β1) (c_stmt (❲ f' ↦ s ❳))::ψ2)).
  apply a_adapt
    with
      (χ:=χ1)(ψ:=ψ1)(ϕ:=ϕ1)(ϕ':=ϕ2)(c:=contn ϕ1)
      (β:=β1)(β':=β2)(f':=f')
      (s:=s)
      (f:=f);
    auto with map_db.
  - destruct ϕ1; crush.
  - destruct ϕ2; crush.
Qed.

(*Ltac peek_pop_simpl :=
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
  end.*)

Lemma dom_finite :
  forall {A B : Type} `{Eq A} D (ps : partial_map A B),
    dom ps D ->
    finite ps.
Proof.
  intros A B HeqA D;
    induction D as [|a D'];
    intros ps Hdom;
    [unfold dom in *;
     andDestruct
    |].

  assert (ps = empty);
    [|subst; auto with map_db].
  apply functional_extensionality;
    intros a;
    repeat map_rewrite.
  apply not_some_implies_none;
    intros b.
  intro Hcontra.
  match goal with
  | [Hmap : ?m ?a = Some ?b,
            H : forall a' b', ?m a' = Some b' -> In a' nil  |- _] => apply H in Hmap; crush
  end.

  unfold dom in Hdom;
    andDestruct.
  destruct (Ha0 a (in_eq a D')) as [b Hmap].

  assert (Hps : ps = update a b (t_update ps a None));
    [apply functional_extensionality;
     intros a';
     repeat map_rewrite|subst].
  destruct (eq_dec a' a) as [|Hneq];
    subst;
    eq_auto.
  rewrite Hps.
  apply fin_update.
  apply IHD'; unfold dom;
    repeat split; intros;
      try solve [match goal with
                 | [Huniq : unique (_::?D) |- unique ?D] => inversion Huniq; auto with map_db
                 end];
      repeat map_rewrite.
  destruct (eq_dec a0 a) as [|Hneq];
    subst;
    eq_auto;
    [crush|].
  match goal with
  | [H : forall a' b', ?m a' = Some b' -> In a' (?a::?D),
       Hmap : ?m ?a0 = Some ?b,
       Hneq : ?a0 <> ?a |- _] => apply H in Hmap; inversion Hmap; crush
  end.

  match goal with
  | [Hin : In ?a0 ?D,
           H : forall a', In a' (?a::?D) ->
                     exists b', ?m a' = Some b',
       Huniq : unique (?a::?D)
                           |- _] =>
    let b := fresh "b" in
    destruct (H a0 (in_cons a a0 D Hin)) as [b];
      destruct (eq_dec a a0);
      subst;
      eq_auto;
      [inversion Huniq; crush|crush]
  end.
Qed.

Hint Resolve dom_finite : loo_db.

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

  - destruct H0 as [Ha|Ha];
      [|destruct Ha as [Ha|Ha]];
      subst;
      simpl;
      [apply fin_update;
       apply finite_map_composition;
       auto
      | |];
      try solve [crush;
                 eauto];
      eauto with loo_db.

  - unfold update_ψ_map, update_ϕ_map in H0;
      inversion H0;
      subst;
      [simpl; apply fin_update|];
      apply H8; crush.

  - destruct H; [subst; simpl|]; eauto.

  - destruct H0; crush.

  - unfold update_ϕ_contn, update_ϕ_map in H; simpl in H;
      destruct H; crush.

  - unfold update_ϕ_contn, update_ϕ_map in H; simpl in H;
      destruct H; crush.
Qed.

Hint Resolve reduction_preserves_config_finiteness : loo_db.

Lemma reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    crush;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_finiteness : loo_db.

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
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_finiteness : loo_db.

Lemma pair_reductions_preserves_config_finiteness :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 finite_σ σ1 ->
                 finite_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    subst;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_finiteness : loo_db.

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

  - exists ϕ'', (ϕ'::ψ); split;
      unfold not_stuck_ϕ;
      subst;
      simpl in *;
      eauto with loo_db.

  - exists ϕ', ψ;
      subst;
      simpl in *;
      split;
      auto;
      unfold not_stuck_ϕ;
      simpl in *;
      auto with loo_db.

  - subst σ'; simpl;
      exists ϕ', ψ;
      split;
      auto;
      subst ϕ';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.

  - exists ϕ'', ψ;
      split;
      auto;
      subst;
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db;
      crush.

  - exists ϕ'', ψ;
      split;
      auto;
      subst ϕ'';
      unfold not_stuck_ϕ;
      simpl;
      auto with loo_db.
Qed.

Hint Resolve reduction_preserves_config_not_stuck : loo_db.

Lemma reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_not_stuck : loo_db.

Lemma pair_reduction_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_not_stuck : loo_db.

Lemma pair_reductions_preserves_config_not_stuck :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 not_stuck_σ σ1 ->
                 not_stuck_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_not_stuck : loo_db.

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

  - exists ϕ'', (ϕ'::ψ); split;
      unfold waiting_ψ, waiting_ϕ in *;
      subst;
      intros;
      auto;
      match goal with
      | [H : In ?ϕ0 _ |- waiting (contn ?ϕ0)] => destruct H; subst; crush
      end.

  - exists ϕ'', ψ; subst;
      split;
      auto;
      unfold waiting_ψ, waiting_ϕ in *;
      intros;
      simpl in *;
      auto;
      crush.

  - exists ϕ'', ψ; subst;
      split;
      auto;
      unfold waiting_ψ, waiting_ϕ in *;
      intros;
      simpl;
      auto;
      crush.

Qed.

Hint Resolve reduction_preserves_config_waiting : loo_db.

Lemma reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_waiting : loo_db.

Lemma pair_reduction_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_waiting : loo_db.

Lemma pair_reductions_preserves_config_waiting :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 waiting_σ σ1 ->
                 waiting_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_waiting : loo_db.

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

  - (* meth *)
    inversion H10; subst.
    apply self_config;
      intros ϕ' Hin;
      inversion Hin;
      auto;
      [subst|].
    apply self_frm;
      exists α, o;
      split;
      auto.
    inversion H0;
      subst.
    assert (Hinϕ : In ϕ (ϕ::ψ));
      [apply in_eq|apply H9 in Hinϕ].
    apply self_frm;
      inversion Hinϕ;
      auto.
    apply H9;
      simpl in *;
      inversion H1;
      auto.

  - (* var asgn *)
    apply has_self_update_σ;
      auto.

  - (* field asgn*)
    inversion H12;
      subst.
    apply self_config;
      intros.
    inversion H;
      subst;
      remember {| cname := cname o; flds := update f v (flds o); meths := meths o |} as o'.
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

  - (* new *)
    inversion H10;
      subst.
    apply self_config;
      intros.
    inversion H0;
      subst;
      remember {| cname := C; flds := fMap ∘ (vMap ϕ); meths := c_meths CDef |} as o'.
    + apply self_frm; simpl.
      assert (Hin : In ϕ (ϕ::ψ));
        [apply in_eq
        |apply H9 in Hin].
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

    + apply self_frm.
      unfold update, t_update.
      assert (Hin : In ϕ0 (ϕ::ψ));
        [apply in_cons; auto
        |apply H9 in Hin;
         destruct Hin as [χ ϕ' Ha];
         destruct Ha as [α0 Ha];
         destruct Ha as [o0];
         andDestruct].
      exists α0.
      destruct (eq_dec α0 α) as [|Hneq];
        [subst α0;
         exists o'
        |exists o0];
        [rewrite eqb_refl; auto
        |rewrite neq_eqb; auto];
        auto.

  - (* ret 1 *)
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

  - (* ret 2*)
    apply self_config;
      intros.
    inversion H6;
      subst.
    inversion H;
      subst.
    apply has_self_update_ϕ_contn, has_self_update_ϕ;
      auto.
    apply H5.
    apply in_cons, in_eq.
    apply H5, in_cons, in_cons;
      auto.
Qed.

Hint Resolve reduction_preserves_config_has_self : loo_db.

Lemma reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reduction_preserves_config_has_self : loo_db.

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

Hint Resolve pair_reduction_preserves_config_has_self : loo_db.

Lemma pair_reductions_preserves_config_has_self :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 has_self_σ σ1 ->
                 has_self_σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_has_self : loo_db.

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
    eauto with loo_db;
    subst.
Qed.

Hint Resolve reduction_preserves_config_wf : loo_db.

Lemma reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
             σ_wf σ1 ->
             σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    eauto with loo_db.
Qed.

Hint Resolve reductions_preserves_config_wf : loo_db.

Lemma pair_reduction_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_config_wf : loo_db.

Lemma pair_reductions_preserves_config_wf :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 σ_wf σ1 ->
                 σ_wf σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred Hwf;
    induction Hred;
    eauto with loo_db.
Qed.

Hint Resolve pair_reductions_preserves_config_wf : loo_db.

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

Hint Resolve config_head_wf : loo_db.

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

Lemma initial_wf :
  forall σ, initial σ ->
       σ_wf σ.
Proof.
  intros σ Hinit;
    inversion Hinit.
  destruct H as [ϕ];
    andDestruct;
    subst.
  apply config_wf;
    auto.
  
  apply self_config;
    intros.
  inversion H;
    [subst|crush].
  apply self_frm.
  exists x, ObjectInstance;
    split;
    auto.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
  
  waiting_auto.
  exists ϕ, nil;
    simpl;
    split;
    intros;
    crush.
Qed.

Hint Resolve initial_wf : loo_db.

Lemma arising_wf :
  forall M1 M2 σ, arising M1 M2 σ ->
             σ_wf σ.
Proof.
  intros M1 M2 σ Harise.
  inversion Harise;
    subst.
  eapply pair_reductions_preserves_config_wf; eauto with loo_db.
Qed.

Hint Resolve arising_wf : loo_db.

Lemma limited_config_wf :
  forall χ ϕ ψ, σ_wf (χ, ϕ::ψ) ->
           σ_wf (χ, ϕ::nil).
Proof.
  intros.
  inversion H;
    subst.
  apply config_wf.
  
  apply self_config;
    intros.
  inversion H0;
    subst.
  inversion H4;
    subst;
    [|crush].
  apply H6, in_eq.

  finite_auto;
    simpl;
    intros.
  inversion H4;
    subst;
    [|crush].
  apply H1;
    simpl;
    auto.

  not_stuck_auto.
  destruct H2 as [ϕ' Ha];
    destruct Ha as [ψ'];
    andDestruct;
    simpl in *.
  inversion Ha;
    subst.
  exists ϕ', nil;
    split;
    auto.
  
  waiting_auto.
  destruct H3 as [ϕ' Ha];
    destruct Ha as [ψ'];
    andDestruct;
    simpl in *;
    inversion Ha;
    subst.
  repeat eexists; eauto; intros.
  crush.

Qed.

Hint Resolve limited_config_wf : loo_db.

Lemma waiting_update_σ_map :
  forall σ, waiting_σ σ ->
       forall x v, waiting_σ (update_σ_map σ x v).
Proof.
  intros.
  waiting_auto;
    simpl in *.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ];
    andDestruct.
  rewrite Ha.
  exists (update_ϕ_map ϕ x v), ψ;
    split;
    unfold update_ψ_map; simpl;
    auto.
Qed.

Hint Resolve waiting_update_σ_map : loo_db.

Lemma not_stuck_update_σ_map :
  forall σ, not_stuck_σ σ ->
       forall x v, not_stuck_σ (update_σ_map σ x v).
Proof.
  intros.
  not_stuck_auto;
    simpl in *.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ];
    andDestruct.
  rewrite Ha.
  exists (update_ϕ_map ϕ x v), ψ;
    split;
    unfold update_ψ_map; simpl;
    auto.
Qed.

Hint Resolve not_stuck_update_σ_map : loo_db.

Lemma finite_update_ϕ_map :
  forall ϕ, finite_ϕ ϕ ->
       forall x v, finite_ϕ (update_ϕ_map ϕ x v).
Proof.
  intros.
  finite_auto.

  apply fin_update;
    auto.
  
Qed.

Hint Resolve finite_update_ϕ_map : loo_db.

Lemma finite_update_σ_map :
  forall σ, finite_σ σ ->
       forall x v, finite_σ (update_σ_map σ x v).
Proof.
  intros.
  destruct σ as [χ ψ].
  unfold finite_σ, finite_ψ.
  simpl.
  unfold update_ψ_map.
  destruct ψ as [|ϕ ψ'];
    intros;
    [crush|].
  inversion H0;
    subst.
  apply finite_update_ϕ_map.
  finite_auto.
  apply H;
    simpl;
    auto.

  finite_auto.
  apply H;
    simpl;
    auto.
Qed.

Hint Resolve finite_update_σ_map : loo_db.

Lemma has_self_update_ϕ_map :
  forall χ ϕ, has_self_ϕ χ ϕ ->
         forall x v ψ A, fresh_x x (χ, ϕ::ψ) A ->
                    has_self_ϕ χ (update_ϕ_map ϕ x v).
Proof.
  intros.

  inversion H;
    subst.
  apply self_frm.
  destruct H1 as [α Htmp];
    destruct Htmp as [o];
    andDestruct.
  exists α, o;
    split;
    auto.
  unfold update_ϕ_map, update, t_update;
    simpl.
  destruct x as [n];
    destruct n as [|n'];
    auto.
  inversion H0;
    subst;
    simpl in *.
  unfold mapp, stackMap, mapp in H1;
    unfold this in Ha; rewrite Ha in H1;
      crush.
Qed.

Hint Resolve has_self_update_ϕ_map : loo_db.

Lemma has_self_update_σ_map :
  forall σ, has_self_σ σ ->
       forall x v A, fresh_x x σ A ->
                has_self_σ (update_σ_map σ x v).
Proof.
  intros σ;
    intros.
  destruct σ as [χ ψ].
  
  apply self_config;
    intros;
    simpl in *.
  destruct ψ as [|ϕ' ψ'];
    [crush|simpl in *].
  destruct H1; subst.

  apply has_self_update_ϕ_map with (ψ:=ψ')(A:=A);
    auto.
  inversion H;
    subst.
  apply H2, in_eq.
  
  inversion H;
    subst.
  apply H3, in_cons; auto.
  
Qed.

Hint Resolve has_self_update_σ_map : loo_db.

Lemma wf_update_σ_map :
  forall σ, σ_wf σ ->
       forall x α A, fresh_x x σ A ->
                σ_wf (update_σ_map σ x α).
Proof.
  intros σ Hwf; intros.
  inversion Hwf;
    subst.
  apply config_wf;
    eauto with loo_db.
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

Hint Rewrite eval_unique : loo_db.

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
  rewrite H4 in H;
    inversion H;
    subst.
  rewrite H5 in H0;
    inversion H0;
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

(* need to change definition of restriction *)
Parameter unique_restriction :
  forall σ Σ σ1, σ ↓ Σ ≜ σ1 ->
            forall σ2, σ ↓ Σ ≜ σ2 ->
                  σ2 = σ1.

Ltac restriction_rewrite :=
  repeat match goal with
         | [H1 : ?σ ↓ ?Σ ≜ ?σ1, H2 : ?σ ↓ ?Σ ≜ ?σ2 |- _] =>
           eapply (unique_restriction σ Σ σ1 H1) in H2;
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
                              
Parameter adaptation_unique :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall σ', σ1 ◁ σ2 ≜ σ' ->
                   σ' = σ.


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
    eauto with loo_db.
Qed.

(*Lemma notin_updates :
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
Qed.*)

Lemma adaptation_preserves_mapping :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall z (v : value), mapp σ1 z = Some v ->
                              mapp σ z = Some v.
Proof.
  intros.
  inversion H;
    subst.

  repeat map_rewrite; simpl.
  apply extend_some_2; auto.
  apply disjoint_dom_symmetry.
  eapply disjoint_composition; auto with map_db.
Qed.

(* fresh  *)

Lemma update_fresh_preserves_map :
  forall x σ A, fresh_x x σ A ->
           forall z v v', mapp σ z = Some v ->
                     mapp (update_σ_map σ x v') z = Some v.
Proof.
  intros x σ A Hfrsh;
    inversion Hfrsh;
    subst;
    intros.

  destruct σ as [χ ψ];
    destruct ψ as [|ϕ ψ].

  unfold mapp, configMapStack, mapp, stackMap in *;
    simpl in *;
    crush.

  unfold mapp, configMapStack, mapp, stackMap in *;
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
    auto with chainmail_db.
Qed.

Lemma fresh_and_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ∧ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto with chainmail_db.
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
    auto with chainmail_db.
Qed.

Lemma fresh_arr_intro :
  forall x σ A1 A2,
    fresh_x x σ A1 /\ fresh_x x σ A2 ->
    fresh_x x σ (A1 ⇒ A2).
Proof.
  intros.
  andDestruct.
  inversion Ha; inversion Hb; subst.
  apply frsh; auto with chainmail_db.
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
    auto with chainmail_db.
Qed.

Lemma fresh_all_intro :
  forall x σ A,
    fresh_x x σ A ->
    fresh_x x σ (∀x∙A).
Proof.
  intros.
  inversion H; subst; auto with chainmail_db.
Qed.

Lemma fresh_notin :
  forall x σ A1 A2,
    fresh_x x σ A1 ->
    notin_Ax A2 x ->
    fresh_x x σ A2.
Proof.
  intros x σ A1 A2 Hfrsh Hnotin.
  inversion Hfrsh; auto with chainmail_db.
Qed.

(* update map *)

Lemma map_update_σ :
  forall σ z v, (exists ϕ ψ, snd σ = ϕ :: ψ) ->
           mapp (update_σ_map σ z v) z = Some v.
Proof.
  intros.
  unfold mapp, configMapStack, mapp, stackMap.
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
               mapp σ1 α = Some o1 ->
               exists o2, mapp σ2 α = Some o2 /\
                     cname o2 = cname o1.
Proof.
  intros M σ1 σ2 Hred;
    destruct Hred;
    intros;
    subst;
    eauto;
    unfold mapp, configMapHeap in *;
    simpl in *.

  - (* asgn fld*)
    destruct (eq_dec α0 α) as [|Hneq];
      [subst|].
    + exists {| cname := cname o; flds := update f v (flds o); meths := meths o |};
        simpl;
        unfold update, t_update;
        rewrite eqb_refl;
        split;
        simpl;
        crush.

    + exists o1;
        unfold update, t_update;
        rewrite neq_eqb;
        auto.

  - destruct (eq_dec α0 α) as [|Hneq];
      [subst; eapply fresh_heap_some_contradiction; eauto|].

    + exists o1;
        unfold update, t_update;
        rewrite neq_eqb;
        auto.
  
Qed.

Hint Resolve reduction_preserves_addr_classes : loo_db.
Hint Rewrite reduction_preserves_addr_classes : loo_db.

Lemma reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                   cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.

  destruct IHHred with (α:=α)(o1:=o1) as [o Hclass];
    eauto; auto;
      andDestruct.

  edestruct reduction_preserves_addr_classes as [o' Hclass1];
    eauto.

  andDestruct.

  eexists; split; eauto; crush.
Qed.

Hint Resolve reductions_preserves_addr_classes : loo_db.
Hint Rewrite reductions_preserves_addr_classes : loo_db.

Lemma pair_reduction_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_preserves_addr_classes : loo_db.
Hint Rewrite pair_reduction_preserves_addr_classes : loo_db.

Lemma pair_reductions_preserves_addr_classes :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall (α : addr) o1,
                   mapp σ1 α = Some o1 ->
                   exists o2, mapp σ2 α = Some o2 /\
                         cname o2 = cname o1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.

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

Hint Resolve pair_reductions_preserves_addr_classes : loo_db.
Hint Rewrite pair_reductions_preserves_addr_classes : loo_db.

Lemma reductions_implies_method_call :
  forall M1 M2 σ1 σ2,
    M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
    σ_wf σ1 ->
    exists χ ϕ ψ,
      σ1 = (χ, ϕ::ψ) /\
      ((exists x y m ps, (exists C CDef, classOf y σ1 C /\ M1 C = Some CDef /\
                    (exists zs s, CDef.(c_meths) m = Some (zs, s))) /\
                    (contn ϕ = c_stmt (s_meth x y m ps) \/
                     exists s, contn ϕ = c_stmt (s_stmts (s_meth x y m ps) s))) \/
       (exists x, (exists C, classOf this σ1 C /\ M1 C = None) /\
             (contn ϕ = c_stmt (s_rtrn x) \/
              exists s, contn ϕ = c_stmt (s_stmts (s_rtrn x) s)))).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    auto.
  inversion H0;
    subst;
    intros.

  - (*meth call*)
    exists χ, ϕ, ψ;
      split;
      [auto|left;
        exists x, y, m, ps; eauto].
    split;
      eauto.
    exists (cname o), C;
      split;
      auto.
    apply (cls_of) with (α:=α)(χ:=χ)(o:=o);
      auto.
    split; [|eauto].
    inversion H;
      subst.
    unfold extend in H8.
    remember (M1 (cname o)) as M1Lookup.
    destruct M1Lookup as [CDef|];
      auto.
    destruct (H2 (cname o)) as [CDef HCDef]; [|crush].
    apply cls_of with (α:=α)(χ:=χ)(o:=o);
      auto.
    remember {| vMap := update this (v_addr α) (ps ∘ (vMap ϕ)); contn := c_stmt s |} as ϕ'.
    remember {| vMap := vMap ϕ; contn := c_hole x s' |} as ϕ''.
    apply int_x with (ϕ:=ϕ')(ψ:=ϕ''::ψ);
      simpl;
      auto.
    subst ϕ';
      simpl.
    unfold update, t_update;
      rewrite eqb_refl;
      auto.
    
  - (* var asgn *)
    inversion H7;
      subst;
      simpl in *.
    remember (cname o0) as C.
    destruct (H2 C) as [CDef].
    apply cls_of with (α:=α0)(χ:=χ)(o:=o0);
      auto.
    apply int_x with (ψ:=ψ)
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
      inversion H11;
      subst;
      simpl in *;
      crush.
    apply H1 in H7; crush.

  - (* f asgn *)
    inversion H7;
      subst;
      simpl in *.
    remember (cname o0) as C.
    destruct H2 with (C:=C) as [CDef].
    remember ({| cname := cname o; flds := update f v (flds o); meths := meths o |})
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
    + apply int_x with (ψ:=ψ)
                       (ϕ:={| vMap := vMap ϕ; contn := c_stmt s |});
        simpl;
        auto.
      inversion H11;
        subst; simpl in *;
          crush.
    + update_auto.
    + crush.
    + apply int_x with (ψ:=ψ)
                       (ϕ:={| vMap := vMap ϕ; contn := c_stmt s |});
        auto;
        simpl.
      inversion H11;
        subst;
        simpl in *;
        crush.
    + update_auto.

    + rewrite H1 in H12;
        crush.
    
  - (* new *)
    intros.
    remember (update α {| cname := C; flds := fMap ∘ (vMap ϕ); meths := c_meths CDef |} χ,
              {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} :: ψ) as σ'.
    assert (Hthis : has_self_σ σ');
      [eapply reduction_preserves_config_has_self;
       inversion H4;
       subst;
       eauto|].
    subst;
      inversion Hthis;
      subst.
    remember {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} as σ'.
    assert (Hin : In σ' (σ'::ψ));
      [apply in_eq|apply H11 in Hin].
    inversion Hin;
      subst;
      simpl in *.
    destruct H10 as [α' Ha];
      destruct Ha as [o'];
      andDestruct.
    unfold update, t_update in Ha;
      rewrite neq_eqb in Ha;
      auto.
    destruct (eq_dec α' α) as [|Hneq];
      [subst
      |].
    + inversion H4;
        subst.
      inversion H10;
        subst.
      assert (Hin' : In ϕ (ϕ::ψ));
        [apply in_eq|apply H16 in Hin'].
      inversion Hin';
        subst.
      destruct H15 as [α0 Hx];
        destruct Hx as [o0];
        andDestruct.
      rewrite Ha0 in Ha;
        inversion Ha;
        subst.
      eapply fresh_heap_some_contradiction; eauto.

    + unfold update, t_update in Hb;
        rewrite neq_eqb in Hb;
        auto.
      remember {| cname := C; flds := fMap ∘ (vMap ϕ); meths := c_meths CDef |} as oα.
      destruct o' as [C' fs ms].
      destruct (H2 C') as [CDef'].
      * remember {| cname := C'; flds := fs; meths := ms |} as o'.
        apply cls_of with (α:=α')(χ:=update α oα χ)(o:=o');
          auto.
        -- remember {| vMap := update x (v_addr α) (vMap ϕ); contn := c_stmt s |} as ϕ'.
           apply int_x with (ψ:=ψ)(ϕ:=ϕ');
             auto.
           subst; simpl;
             unfold update, t_update;
             rewrite neq_eqb;
             auto.
        -- subst; simpl;
             unfold update, t_update;
             auto.
        -- repeat map_rewrite.
           eq_auto.
        -- crush.
      * rewrite H1 in H10;
          auto;
          [crush|].
        
        remember {| cname := C'; flds := fs; meths := ms |} as o'.
        apply cls_of with (α:=α')(χ:=χ)(o:=o');
          auto;
          [|crush].
        apply int_x with (ϕ:=ϕ)(ψ:=ψ);
          auto.

  - (* ret 1 *)
    rename H3 into Hwf;
      inversion Hwf;
      subst.
    exists χ, ϕ, (ϕ'::ψ);
      split;
      [auto|right; eauto].
    exists x; split; auto.
    inversion H3;
      subst.
    assert (Hin : In ϕ (ϕ :: ϕ' :: ψ));
      [apply in_eq|apply H12 in Hin].
    inversion Hin;
      subst.
    destruct H11 as [α' Htmp];
      destruct Htmp as [o];
      andDestruct.
    assert (classOf this (χ, ϕ::ϕ'::ψ) (cname o)).
    apply cls_of with (α:=α')(χ:=χ)(o:=o);
      auto.
    apply int_x with (ψ:=ϕ' :: ψ)(ϕ:=ϕ);
      auto.
    eauto.

  - (* ret 1 *)
    rename H3 into Hwf;
      inversion Hwf;
      subst.
    exists χ, ϕ, (ϕ'::ψ);
      split;
      [auto|right; eauto].
    exists x; split; auto.
    inversion H3;
      subst.
    assert (Hin : In ϕ (ϕ :: (ϕ'::ψ)));
      [apply in_eq|apply H12 in Hin].
    inversion Hin;
      subst.
    destruct H11 as [α' Htmp];
      destruct Htmp as [o];
      andDestruct.
    assert (classOf this (χ, ϕ::ϕ'::ψ) (cname o)).
    apply cls_of with (α:=α')(χ:=χ)(o:=o);
      auto.
    apply int_x with (ψ:=ϕ'::ψ)(ϕ:=ϕ);
      auto.
    eauto.
    eauto.
Qed.

Hint Resolve reductions_implies_method_call : loo_db.

Lemma pair_reduction_implies_method_call :
  forall M1 M2 σ1 σ2,
    M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
    σ_wf σ1 ->
    exists χ ϕ ψ,
      σ1 = (χ, ϕ::ψ) /\
      ((exists x y m ps, (exists C CDef, classOf y σ1 C /\ M1 C = Some CDef /\
                    (exists zs s, CDef.(c_meths) m = Some (zs, s))) /\
                    (contn ϕ = c_stmt (s_meth x y m ps) \/
                     exists s, contn ϕ = c_stmt (s_stmts (s_meth x y m ps) s))) \/
       (exists x, (exists C, classOf this σ1 C /\ M1 C = None) /\
             (contn ϕ = c_stmt (s_rtrn x) \/
              exists s, contn ϕ = c_stmt (s_stmts (s_rtrn x) s)))).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve pair_reduction_implies_method_call : loo_db.

Parameter fresh_exists_for_expression :
  forall e, exists x, notin_exp e x.

Parameter fresh_exists_for_assertion :
  forall A, exists x, notin_Ax A x.


Parameter fresh_x_exists_for_finite_config :
  forall σ, finite_σ σ ->
       forall A, exists x, fresh_x x σ A.

Parameter fresh_address_rename_equality_heap :
  forall α1 α2 (χ : heap),  χ α1 = None ->
                       χ α2 = None ->
                       forall o, update α1 o χ = update α2 o χ.

Parameter fresh_address_rename_equality_state :
  forall α1 α2 (χ : heap),  χ α1 = None ->
                       χ α2 = None ->
                       forall m (x:var), update x (v_addr α1) m = update x (v_addr α2) m.
              
                
               

Lemma reduction_unique :
  forall M σ σ1, M ∙ σ ⤳ σ1 ->
            forall σ2, M ∙ σ ⤳ σ2 ->
                  σ2 = σ1.
Proof.
  intros M σ σ1 Hred;
    induction Hred;
    intros.

  - (* meth *)
    simpl in *;
      subst.
    inversion H2;
      subst;
      crush.
    inversion H9;
      subst;
      crush.
    inversion H8; subst.
    rewrite H1 in H10.
    inversion H10; subst.
    interpretation_rewrite.
    crush.

  - (* vAssgn *)
    inversion H8;
      subst;
      crush.
    inversion H10; subst.
    rewrite H1 in H11;
      inversion H11;
      subst.
    interpretation_rewrite;
      crush.

  - (* fAssgn *)
    simpl in *.
    inversion H11;
      subst;
      crush.
    inversion H12; subst.
    rewrite H13 in H0;
      inversion H0;
      subst.
    interpretation_rewrite.
    crush.

  - (* new *)
    inversion H9;
      subst;
      crush.
    inversion H11; subst.
    rewrite H1 in H12;
      inversion H12;
      subst;
      crush.
    match goal with
    | [H1 : fresh_χ ?χ ?αa,
            H2 : fresh_χ ?χ ?αb |- _] =>
      apply fresh_heap_unique with (α1:=αa) in H2;
        subst;
        auto
    end.
    crush.

  - (* ret1 *)
    subst.
    inversion H5;
      subst;
      crush.
    inversion H; subst.
    rewrite H0 in H4;
      inversion H4;
      subst.
    interpretation_rewrite.
    crush.


  - crush.
    inversion H5;
      subst;
      crush.
    inversion H;
      subst.
    rewrite H0 in H4;
      inversion H4;
      subst.
    interpretation_rewrite.
    crush.

Qed.

Hint Resolve reduction_unique : loo_db.

(*
Lemma pair_reduction_unique :
  forall M1 M2 σ σ1, M1 ⦂ M2 ⦿ σ ⤳ σ1 ->
                forall σ2, M1 ⦂ M2 ⦿ σ ⤳ σ2 ->
                      σ2 = σ1.
Proof.
  intros M1 M2 σ σ1 Hred;
    induction Hred;
    intros;
    eauto.
  inversion H3;
    subst.
Qed.*)