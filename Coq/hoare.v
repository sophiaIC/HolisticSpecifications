Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import exp.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(*Inductive condition : Type :=
| cond : (config -> Prop) -> condition
| cond_and : condition -> condition -> condition
| cond_or : condition -> condition -> condition.

Notation "P '⩟' Q" := (cond_and P Q)(at level 40).
Notation "P '⊻' Q" := (cond_or P Q)(at level 40).

Fixpoint app (P : condition)(σ : config) :=
  match goal with
  | cond Q => Q σ
  | Q ⩟ R => (app Q σ) /\ (app R σ)
  | Q ⊻ R => (app Q σ) \/ (app R σ) ∀
  end.*)

Inductive pair_reductions_alt : mdl -> mdl -> config -> config -> Prop :=
| pra_single : forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                              pair_reductions_alt M1 M2 σ1 σ2
| pra_trans : forall M1 M2 σ1 σ σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ ->
                               pair_reductions_alt M1 M2 σ σ2 ->
                               pair_reductions_alt M1 M2 σ1 σ2.

Hint Constructors pair_reductions_alt.

Lemma pair_reductions_alt_equiv_1 :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
Proof.
Admitted.

Lemma pair_reductions_alt_equiv_2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 pair_reductions_alt M1 M2 σ1 σ2.
Proof.
Admitted.

Lemma pair_reduction_change_alt :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 forall (P : mdl -> mdl -> config -> Prop),
                   P M1 M2 σ1 ->
                   ~ P M1 M2 σ2 ->
                   exists σ σ', (σ = σ1 \/ pair_reductions_alt M1 M2 σ1 σ) /\
                           M1 ⦂ M2 ⦿ σ ⤳ σ' /\
                           (σ' = σ2 \/ pair_reductions_alt M1 M2 σ' σ2) /\
                           P M1 M2 σ /\
                           ~ P M1 M2 σ'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    auto with loo_db.

  - exists σ1, σ2; repeat split;
      auto.

  - destruct (excluded_middle (P M1 M2 σ)).
    + specialize (IHHred P);
        repeat auto_specialize;
        repeat destruct_exists_loo;
        andDestruct.
      exists σ0, σ3; repeat split; eauto.
      right.
      destruct Ha;
        subst;
        eauto.

    + exists σ1, σ;
        repeat split;
        eauto.
Qed.

Lemma pair_reduction_change :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 forall (P : mdl -> mdl -> config -> Prop),
                   P M1 M2 σ1 ->
                   ~ P M1 M2 σ2 ->
                   exists σ σ', (σ = σ1 \/ M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ) /\
                           M1 ⦂ M2 ⦿ σ ⤳ σ' /\
                           (σ' = σ2 \/ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ2) /\
                           P M1 M2 σ /\
                           ~ P M1 M2 σ'.
Proof.
  intros.
  destruct (pair_reduction_change_alt M1 M2 σ1 σ2)
    with (P:=P)
    as [σ];
    auto.
  apply pair_reductions_alt_equiv_2; auto.
  repeat destruct_exists_loo;
    andDestruct.
  exists σ, σ0;
    repeat split;
    auto.
  + destruct Ha; auto.
    right; apply pair_reductions_alt_equiv_1; auto.
  + destruct Ha1; auto.
    right; apply pair_reductions_alt_equiv_1; auto.
Qed.

Reserved Notation "M '∙' '{pre:' P '}' σ '{post:' Q '}'" (at level 40).
Reserved Notation "M '∙' '{pre:' P '}' σ1 '⤳⋆' σ2 '{post:' Q '}'" (at level 40).
Reserved Notation "M1 '⦂' M2 '⦿' '{pre:' P '}' σ '{post:' Q '}'" (at level 40).

Inductive hoare_triple : mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
| ht_r : forall M σ (P Q : config -> Prop), (forall σ', P σ ->
                                          M ∙ σ ⤳ σ' ->
                                          Q σ') ->
                                   M ∙ {pre: P} σ {post: Q}

where "M '∙' '{pre:' P '}' σ '{post:' Q '}'"
        := (hoare_triple M P σ Q).

Inductive hoare_triples : mdl -> (config -> Prop) -> config -> config -> (config -> Prop) -> Prop :=
| ht_single : forall M P σ1 σ2 Q, M ∙ σ1 ⤳ σ2 ->
                             M ∙ {pre: P} σ1 {post: Q} ->
                             M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q}
| ht_trans : forall M P σ1 σ σ2 P' Q, M ∙ σ1 ⤳ σ ->
                                 M ∙ {pre: P} σ1 {post: P'} ->
                                 M ∙ {pre: P'} σ ⤳⋆ σ2 {post: Q} ->
                                 M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q}
                              

where "M '∙' '{pre:' P '}' σ1 '⤳⋆' σ2 '{post:' Q '}'" := (hoare_triples M P σ1 σ2 Q).

Inductive hoare_triple_pr : mdl -> mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
| ht_pr : forall M1 M2 σ (P Q : config -> Prop), (forall σ', P σ ->
                                               M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                                               Q σ') ->
                                        M1 ⦂ M2 ⦿ {pre: P } σ {post: Q }

where "M1 '⦂' M2 '⦿' '{pre:' P '}' σ '{post:' Q '}'"
        := (hoare_triple_pr M1 M2 P σ Q).

Hint Constructors hoare_triple hoare_triples hoare_triple_pr : loo_db.

Notation "M1 '⦂' M2 '◎' σ0 '…' '̱' '⊨' '{pre:' A1 '}' σ '{post:' A2 '}'" :=
  (M1 ⦂ M2 ⦿ {pre: fun σ => M1 ⦂ M2 ◎ σ0 … σ ⊨ A1} σ {post: fun σ' => M1 ⦂ M2 ◎ σ0 … σ' ⊨ A2})(at level 40).

Inductive contn_is : stmt -> config -> Prop :=
| is_stmt : forall s σ ϕ ψ, snd σ = ϕ :: ψ ->
                       contn ϕ = c_stmt s ->
                       contn_is s σ.

Hint Constructors contn_is : loo_db.

Definition is_assgn : config -> Prop :=
  fun σ => exists r1 r2 s, contn_is (r1 ≔ r2 ;; s) σ.

Definition is_eAssgn : config -> Prop :=
  fun σ => exists x e s, contn_is (x ≔′ e ;; s) σ.

Definition is_fAccess : config -> Prop :=
  fun σ => exists x y f s, contn_is (r_ x ≔ (y ◌ f) ;; s) σ.

Definition is_fAssgn : config -> Prop :=
  fun σ => exists x f y s, contn_is (x ◌ f ≔ (r_ y) ;; s) σ.

Definition is_new : config -> Prop :=
  fun σ => exists x C β s, contn_is (s_new x C β ;; s) σ.

Definition is_if : config -> Prop :=
  fun σ => exists e s1 s2 s, contn_is (s_if e s1 s2 ;; s) σ.

Definition is_rtrn : config -> Prop :=
  fun σ => exists x, (contn_is (s_rtrn x) σ \/
              exists s, contn_is (s_rtrn x ;; s) σ).

(*Definition is_reduced : config -> config -> Prop :=
  fun σ1 σ2 => exists ϕ1 ϕ2 ψ s1 s2, snd σ1 = ϕ1 :: ψ /\
                             snd σ2 = ϕ2 :: ψ /\
                             contn ϕ1 = c_stmt (s1 ;; s2) /\
                             contn ϕ2 = c_stmt s2.*)

Definition ctxUpdated : config -> var -> value -> config -> Prop :=
  fun σ1 x v σ2 => exists ϕ1 ϕ2 ψ, snd σ1 = ϕ1 :: ψ /\
                           snd σ2 = ϕ2 :: ψ /\
                           vMap ϕ2 = update x v (vMap ϕ1).

Definition heapUpdated : config -> addr -> obj -> config -> Prop :=
  fun σ1 α o σ2 => fst σ2 = (update α o (fst σ1)).

Definition fieldHeapUpdated : config -> addr -> fld -> value -> config -> Prop :=
  fun σ1 α f v σ2 => exists o' v', ⟦ α ↦ o' ⟧ ∈ σ1 /\
                           flds o' f = Some v' /\
                           heapUpdated σ1 α (new (cname o') (update f v (flds o'))) σ2.

Definition fieldUpdated : config -> var -> fld -> var -> config -> Prop :=
  fun σ1 x f y σ2 => exists α v, ⌊ x ⌋ σ1 ≜ (v_addr α) /\
                         ⌊ y ⌋ σ2 ≜ v /\
                         fieldHeapUpdated σ1 α f v σ2.

Definition fieldUpdatedValue : config -> var -> fld -> value -> config -> Prop :=
  fun σ1 x f v σ2 => exists α, ⌊ x ⌋ σ1 ≜ (v_addr α) /\
                       fieldHeapUpdated σ1 α f v σ2.

Definition fieldMapsTo : config -> var -> fld -> value -> Prop :=
  fun σ x f v => exists α o, ⌊ x ⌋ σ ≜ (v_addr α) /\
                     ⟦ α ↦ o ⟧ ∈ σ /\
                     flds o f = Some v.

Definition new_object_created : config -> var -> cls -> partial_map fld var -> config -> Prop :=
  fun σ x C ps σ' =>  exists χ ϕ ψ α s, σ = (χ, ϕ :: ψ) /\
                                contn ϕ = c_stmt (s_new x C ps ;; s) /\
                                fresh_χ χ α /\
                                heapUpdated σ α (new C (ps ∘ (vMap ϕ))) σ' /\
                                ctxUpdated σ x (v_addr α) σ'.

Definition heapUnchanged : config -> config -> Prop :=
  fun σ1 σ2 => fst σ1 = fst σ2.

Definition ctxUnchanged : config -> config -> Prop :=
  fun σ1 σ2 => exists ϕ1 ϕ2 ψ, snd σ1 = ϕ1 :: ψ /\
                       snd σ2 = ϕ2 :: ψ /\
                       vMap ϕ1 = vMap ϕ2.

Ltac hoare_auto :=
  intros;
  repeat destruct_exists_loo;
  unfold is_eAssgn in *;
  unfold is_fAccess in *;
  unfold is_fAssgn in *;
  unfold is_if in *;
  unfold is_new in *;
  unfold heapUnchanged in *; simpl in *;
  andDestruct;
  simpl in *;
  subst;
  match goal with
  | [ |- _ ∙ {pre: _} _ {post: _}] =>
    apply ht_r;
    intros
  | [Hcontn : contn_is _ _ |- _] =>
    inversion Hcontn;
    subst;
    clear Hcontn
  | [|- contn_is _ (_, ?ϕ' :: ?ψ')] =>
    eapply is_stmt with (ϕ:=ϕ')(ψ:=ψ');
    eauto
  | [Hred : _ ∙ _ ⤳ _ |- _] =>
    inversion Hred;
    subst;
    clear Hred;
    repeat simpl_crush
  end;
  try solve [repeat (eexists; simpl in *); eauto];
             repeat (destruct_exists_loo; andDestruct).

Lemma eAssgn_hoare :
  forall M σ x e s, M ∙ {pre: contn_is (x ≔′ e ;; s)} σ {post: fun σ' => (contn_is s σ') /\
                                                                 (exists v, ctxUpdated σ x v σ' /\
                                                                       M ∙ σ ⊢ e ↪ v)}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.
Qed.

Lemma eAssgn_heap_unchanged_hoare :
  forall M σ x e s, M ∙ {pre: contn_is (x ≔′ e ;; s)} σ {post: heapUnchanged σ}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.
Qed.

Lemma fAccess_hoare :
  forall M σ x y f s, M ∙
                   {pre: contn_is (r_ x ≔ (y ◌ f) ;; s)}
                   σ
                   {post: fun σ' => contn_is s σ' /\
                                 (exists v, fieldMapsTo σ y f v /\
                                       ctxUpdated σ x v σ')}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.

  repeat eexists; eauto.

  match goal with
    [Hint : ⌊ _ ⌋ _ ≜ _ |- _] =>
    inversion Hint;
      subst
  end;
    simpl in *;
    repeat simpl_crush;
    auto.
  
Qed.

Lemma fAccess_heap_unchanged_hoare :
  forall M σ x y f s, M ∙
                   {pre: contn_is (r_ x ≔ (y ◌ f) ;; s)}
                   σ
                   {post: heapUnchanged σ}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.
Qed.

Lemma fAssgn_hoare :
  forall M σ x f y s, M ∙
                   {pre: contn_is (x ◌ f ≔ (r_ y) ;; s)}
                   σ
                   {post: fun σ' => contn_is s σ' /\
                                 fieldUpdated σ x f y σ'}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.
  split;
    try hoare_auto.

  repeat eexists; eauto;
    try solve [repeat match goal with
                        [Hint : ⌊ _ ⌋ _ ≜ _ |- _] =>
                        inversion Hint;
                        subst;
                        clear Hint
                      end;
               simpl in *;
               repeat simpl_crush;
               auto].
Qed.

Lemma fAssgn_ctx_unchanged_hoare :
  forall M σ x f y s, M ∙
                   {pre: contn_is (x ◌ f ≔ (r_ y) ;; s)}
                   σ
                   {post: ctxUnchanged σ}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto.
Qed.

Lemma new_hoare :
  forall M σ x C β s, M ∙
                   {pre: contn_is (s_new x C β ;; s)}
                   σ
                   {post: fun σ' => contn_is s σ' /\
                                 new_object_created σ x C β σ'}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    repeat hoare_auto;
    split;
    try solve [repeat (eexists; eauto);
               eauto].
Qed.

Lemma if_true_hoare :
  forall M σ e s1 s2 s, M ∙ {pre: fun σ => contn_is (s_if e s1 s2 ;; s) σ /\
                                   M ∙ σ ⊢ e ↪ v_true}
                     σ
                     {post: contn_is (merge s1 s)}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    intros.
  repeat hoare_auto.
  eval_rewrite; crush.
Qed.

Lemma if_false_hoare :
  forall M σ e s1 s2 s, M ∙ {pre: fun σ => contn_is (s_if e s1 s2 ;; s) σ /\
                                   M ∙ σ ⊢ e ↪ v_false}
                     σ
                     {post: contn_is (merge s2 s)}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    intros.
  repeat hoare_auto.
  eval_rewrite; crush.
Qed.

Lemma if_heap_unchanged_hoare :
  forall M σ, M ∙ {pre: is_if} σ {post: heapUnchanged σ}.
Proof.
  intros M σ;
    destruct σ as [χ ψ];
    intros.
  repeat hoare_auto.
Qed.

Lemma if_ctx_unchanged_hoare :
  forall M σ, M ∙ {pre: is_if} σ {post: ctxUnchanged σ}.
Proof.
  intros M σ;
    destruct σ;
    repeat hoare_auto.
Qed.

Lemma hoare_triple_inversion :
  forall M P σ Q, M ∙ {pre: P} σ {post: Q} ->
             forall σ', M ∙ σ ⤳ σ' ->
                   P σ -> Q σ'.
Proof.
  intros M P σ Q Hhoare;
    inversion Hhoare;
    eauto.
Qed.

Ltac hoare_inversion_1 :=
  match goal with
  | [Hhoare : ?M ∙ {pre: ?P} ?σ {post: ?Q},
              Hred : ?M ∙ ?σ ⤳ ?σ' |- _ ] =>
    notHyp (Q σ');
    assert (Q σ');
    [eapply hoare_triple_inversion; eauto|]
  end.

Lemma hoare_triples_inversion :
  forall M P σ1 σ2 Q, M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q} ->
                 P σ1 -> Q σ2.
Proof.
  intros M P σ1 σ2 Q Hhoare;
    induction Hhoare;
    intros;
    eauto with loo_db;
    hoare_inversion_1; eauto.
Qed.

Ltac hoare_inversion_2 :=
  match goal with
  | [Hhoare : ?M ∙ {pre: ?P} ?σ {post: ?Q},
              Hred : ?M ∙ ?σ ⤳⋆ ?σ' |- _ ] =>
    notHyp (Q σ');
    assert (Q σ');
    [eapply hoare_triples_inversion; eauto|]
  end.

Lemma hoare_triple_pr_inversion :
  forall {M1 M2 P σ Q}, M1 ⦂ M2 ⦿ {pre: P} σ {post: Q} ->
                   forall {σ'}, M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                           P σ -> Q σ'.
Proof.
  intros M1 M2 P σ Q Hhoare;
    inversion Hhoare;
    subst;
    intros;
    eauto.
Qed.

Lemma hoare_triples_pr_transitive :
  forall M P σ1 σ2 Q, M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q} ->
                 forall σ3 Q', M ∙ {pre: Q} σ2 ⤳⋆ σ3 {post: Q'} ->
                          M ∙ {pre: P} σ1 ⤳⋆ σ3 {post: Q'}.
Proof.
  intros M P σ1 σ2 Q Hhoare;
    induction Hhoare;
    intros;
    simpl;
    eauto;
    eapply ht_trans; eauto.
Qed.

Ltac hoare_inversion :=
  match goal with
  | [Hhoare : ?M ∙ {pre: ?P} ?σ {post: ?Q},
              Hred : ?M ∙ ?σ ⤳ ?σ' |- _ ] =>
    notHyp (Q σ');
    assert (Q σ');
    [eapply hoare_triple_inversion; eauto|]
  | [Hhoare : ?M ∙ {pre: ?P} ?σ ⤳⋆ ?σ' {post: ?Q} |- _ ] =>
    notHyp (Q σ');
    assert (Q σ');
    [eapply hoare_triples_inversion; eauto|]
  | [Hhoare : ?M1 ⦂ ?M2 ⦿ {pre: ?P} ?σ {post: ?Q},
              Hred : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σ' |- _ ] =>
    notHyp (Q σ');
    assert (Q σ');
    [eapply hoare_triple_pr_inversion; eauto|]
  end.

Lemma reduction_trace_unique :
  forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
             forall σ3, M ∙ σ1 ⤳⋆ σ3 ->
                   (M ∙ σ2 ⤳⋆ σ3) \/
                   (σ2 = σ3) \/
                   (M ∙ σ3 ⤳⋆ σ2).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros σ Hred';
    subst.

  - inversion Hred';
      unique_reduction_auto;
      eauto.

  - inversion Hred';
      subst;
      unique_reduction_auto;
      eauto.
Qed.

Lemma reductions_transitive :
  forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
             forall σ3, M ∙ σ2 ⤳⋆ σ3 ->
                   M ∙ σ1 ⤳⋆ σ3.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto with loo_db.
Qed.

Hint Resolve reductions_transitive : loo_db.
Hint Rewrite reductions_transitive : loo_db.

Lemma internal_reductions_is_reducions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M, M1 ⋄ M2 ≜ M ->
                      M ∙ σ1 ⤳⋆ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    link_unique_auto;
    auto with loo_db.

  - specialize (IHHred M);
      auto_specialize.
    eauto with loo_db.
Qed.

Lemma pair_reduction_is_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall M, M1 ⋄ M2 ≜ M ->
                      M ∙ σ1 ⤳⋆ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    link_unique_auto;
    auto with loo_db.

  - match goal with
    | [H : _ ⦂ _ ⦿ _ ⤳… _ |- _] =>
      eapply internal_reductions_is_reducions in H;
        eauto with loo_db
    end.
Qed.

(**
reduction_order is an ordering on stacks. 
This is used to prove that reduction is acyclic.
reducion_order is not well-founded, as loo has
recursive functions, and thus a loo program might 
never terminate. It is only useful as an ordering 
on stacks to prove reduction acyclic from the 
perspective of stacks

ro extends this ordering on configurations.

ro σ1 σ2

means σ2 < σ1
 *)

Definition stmt_of (ϕ : frame) :=
  match contn ϕ with
  | c_stmt s => s
  | c_hole _ s => s
  end.

Definition contn_size :=
  fun c => match c with
        | c_stmt s => stmt_size s
        | c_hole _ s => 1 + stmt_size s
        end.

Inductive reduction_order : stack -> stack -> Prop :=
| ro_frame : forall ψ1 ψ2 ϕ1 ϕ2 ψ, contn_size (contn ϕ1) > contn_size (contn ϕ2) ->
                              reduction_order (ψ1 ++ ϕ1 :: ψ) (ψ2 ++ ϕ2 :: ψ).
Hint Constructors reduction_order : loo_db.

Definition ro (σ1 σ2 : config) :=
  reduction_order (snd σ1) (snd σ2).

Lemma reduction_order_transitive :
  forall ψ1 ψ2, reduction_order ψ1 ψ2 ->
           forall ψ3, reduction_order ψ2 ψ3 ->
                 reduction_order ψ1 ψ3.
Proof.
(**
This is fairly straight-forward to prove on paper.
By inversion on the derivation of reduction_order, 
we get:

ψ1 = ψ1' ++ ϕ1 :: ψa
ψ2 = ψ2_1 ++ ϕ2 :: ψa

and 

ψ2 = ψ2_2 ++ ϕ2' :: ψb
ψ3 = ψ3' ++ ϕ3 :: ψb

Since 

ψ2_1 ++ ϕ2 :: ψa = ψ2_2 ++ ϕ2' :: ψb, 

it follows that either
(i) ψa = ψb, (ii) ψa ⊂ ψb, or (iii) ψb ⊂ ψa

(i) derived simply by noting that 
ϕ2' = ϕ2 and
contn_size ϕ1 > contn_size ϕ2 > contn_size ϕ3

(ii) it follows that ∃ ψ3'', ψ3 = ψ3'' ++ ϕ2 :: ψa. 
the desired result follows from this

(iii) it follows that ∃ ψ1'', ψ1 = ψ1'' ++ ϕ2' :: ψb. 
the desired result follows from this
*)
Admitted.

Lemma reduction_is_ordered :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             ro σ1 σ2.
Proof.
  intros M σ1 σ2 Hred;
    inversion Hred;
    subst;
    unfold ro;
    simpl in *;
    try solve [match goal with
               | [|- reduction_order (?ϕ1 :: ?ψ) (?ϕ2 :: ?ψ)] =>
                 let Ha := fresh in
                 let Hb := fresh in
                 assert (Ha : (ϕ1 :: ψ) = (nil ++ (ϕ1 :: ψ)));
                 [crush|rewrite Ha];
                 assert (Hb : (ϕ2 :: ψ) = (nil ++ (ϕ2 :: ψ)));
                 [crush|rewrite Hb];
                 apply ro_frame;
                 simpl
               end;
               match goal with
               | [H : contn ?ϕ = _ |- context[contn ?ϕ]] =>
                 rewrite H;
                 simpl
               end;
               simpl;
               try rewrite merge_stmt_size;
               crush];
    try solve [match goal with
               | [|- reduction_order (?ϕ1 :: ?ϕ2 :: ?ψ) (?ϕ :: ?ψ)] =>
                 let Ha := fresh in
                 let Hb := fresh in
                 assert (Ha : (ϕ :: ψ) = (nil ++ (ϕ :: ψ)));
                 [crush|rewrite Ha];
                 assert (Hb : (ϕ1 :: ϕ2 :: ψ) = ((ϕ1 :: nil) ++ (ϕ2 :: ψ)));
                 [crush|rewrite Hb];
                 apply ro_frame;
                 simpl
               end;
               match goal with
               | [H : contn ?ϕ = _ |- context[contn ?ϕ]] =>
                 rewrite H;
                 simpl
               end;
               auto].

  - match goal with
    | [|- reduction_order (?ϕ :: ?ψ) (?ϕ1 :: ?ϕ2 :: ?ψ)] =>
      let Ha := fresh in
      let Hb := fresh in
      assert (Ha : (ϕ :: ψ) = (nil ++ (ϕ :: ψ)));
        [crush|rewrite Ha];
        assert (Hb : (ϕ1 :: ϕ2 :: ψ) = ((ϕ1 :: nil) ++ (ϕ2 :: ψ)));
        [crush|rewrite Hb];
        apply ro_frame;
        simpl
    end.
    match goal with
    | [H : contn ?ϕ = _ |- context[contn ?ϕ]] =>
      rewrite H;
        simpl
    end;
      auto.
Qed.

Lemma reductions_is_ordered :
  forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
             ro σ1 σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred.

  - eapply reduction_is_ordered; eauto.

  - apply reduction_order_transitive with (ψ2:=snd σ2); auto.
    eapply reduction_is_ordered; eauto.
Qed.

Lemma reduction_order_implies_neq :
  forall ψ1 ψ2, reduction_order ψ1 ψ2 ->
           ψ1 <> ψ2.
Proof.
  intros ψ1 ψ2 Hord;
    inversion Hord;
    subst.
Admitted.

Lemma ro_implies_neq :
  forall σ1 σ2, ro σ1 σ2 ->
           σ1 <> σ2.
Proof.
  intros.
  apply reduction_order_implies_neq in H.
  intros Hcontra;
    subst;
    crush.
Qed.

Lemma acyclic_reductions :
  forall M σ1 σ2, M ∙ σ1 ⤳⋆ σ2 ->
             σ1 <> σ2.
Proof.
  intros.
  apply ro_implies_neq.
  eapply reductions_is_ordered; eauto.
Qed.

(*Lemma internal_reductions_are_internal :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M σ, M1 ⋄ M2 ≜ M ->
                        M ∙ σ1 ⤳⋆ σ ->
                        M ∙ σ ⤳⋆ σ2 ->
                        internal_self M1 M2 σ.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros;
    link_unique_auto.

  - 

Qed.*)

Lemma hoare_reductions_implies_pair_reduction :
  forall M P σ1 σ2 Q, M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q} ->
                 forall M1 M2, M1 ⋄ M2 ≜ M ->
                          M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                          M1 ⦂ M2 ⦿ {pre: P} σ1 {post: Q}.
Proof.
  intros M P σ1 σ2 Q Hhoare;
    intros.

  apply ht_pr; intros.
  unique_reduction_auto.
  match goal with
  | [H : _ ⦂ _ ⦿ _ ⤳ _ |- _] =>
    eapply pair_reduction_is_reductions in H;
      eauto
  end.
  hoare_inversion; auto.
Qed.

Definition empty_precondition := (fun (_ : config) => True).
Notation "∅" := (empty_precondition)(at level 40).

Definition waiting_frame_is :=
  fun (f : config -> Prop) σ => exists ϕ1 ϕ2 ψ, snd σ = ϕ1 :: ϕ2 :: ψ /\
                                    f (fst σ, ϕ2 :: ψ).

Definition is_return_to :=
  fun (f : config -> Prop) σ => is_rtrn σ /\
                         waiting_frame_is f σ.

Definition is_call_to :=
  fun (f : config -> var -> Prop) σ => exists x y m β s, contn_is (s_meth x y m β ;; s) σ /\
                                            f σ y.

Definition external_step :=
  fun (M1 M2 : mdl) σ => external_self M1 M2 σ /\
                      (is_assgn σ \/
                       is_new σ \/
                       is_if σ \/
                       is_call_to (is_external M1 M2) σ \/
                       is_return_to (external_self M1 M2) σ).

Definition internal_step :=
  fun M1 M2 σ => is_call_to (is_internal M1 M2) σ \/
              is_return_to (internal_self M1 M2) σ.

Lemma internal_self_update_contn :
  forall M1 M2 σ, internal_self M1 M2 σ ->
             forall c, internal_self M1 M2 (update_σ_contn σ c).
Proof.
  intros M1 M2 σ Hinternal c.
  destruct σ as [χ ψ].
  unfold update_σ_contn; simpl.
  destruct ψ as [|ϕ ψ];
    [crush|].
  eauto.
Qed.

Lemma internal_self_update_vMap :
  forall M1 M2 σ, internal_self M1 M2 σ ->
             forall x v, x <> this -> internal_self M1 M2 (update_σ_map σ x v).
Proof.
  intros M1 M2 σ Hinternal x v Hneq.
  destruct σ as [χ ψ].
  destruct ψ as [|ϕ ψ];
    [crush|].
  repeat map_rewrite.
  unfold update_ϕ_map.
  unfold internal_self, is_internal in *.
  repeat destruct_exists_loo;
    andDestruct.
  repeat eexists;
    simpl;
    eauto.
  repeat map_rewrite.
  unfold vMap.
  eq_auto.
Qed.

Lemma internal_step_is_internal :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall M1 M2, M1 ⋄ M2 ≜ M ->
                      internal_step M1 M2 σ1 ->
                      internal_self M1 M2 σ2.
Proof.
  intros M σ1 σ2 Hred;
    inversion Hred;
    intros;
    subst;
    try solve [unfold internal_step in *;
               match goal with
               | [H : is_call_to _ _ \/ is_return_to _ _ |- _] =>
                 let H' := fresh in
                 destruct H as [H'|H']
               end;
               unfold is_call_to, is_return_to, is_rtrn in *;
               repeat destruct_exists_loo;
               andDestruct;
               repeat destruct_exists_loo;
               try match goal with
                   | [H : contn_is _ _ \/ _ |- _] =>
                     destruct H
                   end;
               repeat destruct_exists_loo;
               try match goal with
                   | [Ha : contn_is _ ?ϕ |- _] =>
                     inversion Ha;
                     subst;
                     simpl in *
                   end;
               repeat simpl_crush];
    try solve [unfold internal_step in *;
               match goal with
               | [H : is_call_to _ _ \/ is_return_to _ _ |- _] =>
                 let H' := fresh in
                 destruct H as [H'|H']
               end;
               unfold is_call_to, is_return_to, is_rtrn in *;
               repeat destruct_exists_loo;
               andDestruct;
               repeat destruct_exists_loo;
               try match goal with
                   | [H : contn_is _ _ \/ _ |- _] =>
                     destruct H
                   end;
               repeat destruct_exists_loo;
               try match goal with
                   | [Ha : contn_is _ ?ϕ |- _] =>
                     inversion Ha;
                     subst;
                     simpl in *
                   end;
               repeat simpl_crush;
               unfold waiting_frame_is in *;
               repeat destruct_exists_loo;
               andDestruct;
               simpl in *;
               repeat simpl_crush;
               assert (Htmp : (χ, update_ϕ_contn (update_ϕ_map ϕ1 y α) (c_stmt s) :: ψ0) =
                              (update_σ_contn (update_σ_map (χ, ϕ1 :: ψ0) y α) (c_stmt s)));
               [auto|rewrite Htmp];
               apply internal_self_update_contn, internal_self_update_vMap; auto].

  - match goal with
    | [H : internal_step ?M1 ?M2 (?χ, ?ϕ :: ?ψ) |- _] =>
      let Ha := fresh in
      unfold internal_step in H;
        destruct H as [Ha|Ha];
        unfold is_call_to, is_return_to in Ha;
        repeat destruct_exists_loo;
        andDestruct
    end.
    + match goal with
      | [H : contn_is _ _ |- _] =>
        inversion H;
          subst;
          simpl in *
      end.
      repeat simpl_crush.

      
      unfold is_internal in Hb;
        repeat destruct_exists_loo;
        andDestruct;
        repeat simpl_crush.
      inversion H2; subst;
        simpl in *;
        repeat simpl_crush.
      repeat map_rewrite.
      repeat simpl_crush.
      unfold internal_self, is_internal;
        repeat map_rewrite;
        simpl;
        repeat eexists;
        eauto.

    + match goal with
      | [H : is_rtrn _ |- _] =>
        let H' := fresh in
        let x := fresh "x" in
        unfold is_rtrn in H;
          destruct H as [x H'];
          destruct H';
          repeat destruct_exists_loo;
          try match goal with
              | [Ha : contn_is _ ?ϕ |- _] =>
                inversion Ha;
                  subst;
                  simpl in *
              end;
          repeat simpl_crush
      end.

Qed.

Lemma internal_reductions_is_internal_step :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 internal_step M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros; auto.

  unfold internal_step.

  match goal with
  | [H : _ ∙ _ ⤳ _ |- _] =>
    inversion H; subst;
      eauto
  end.

  - admit.

   
Admitted.

Lemma external_self_implies_external_step :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall M1 M2, M1 ⋄ M2 ≜ M ->
                      external_self M1 M2 σ2 ->
                      external_step M1 M2 σ1.
Proof.

Admitted.

Lemma pair_reduction_inversion_hoare :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 external_step M1 M2 σ1 \/
                 internal_step M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  - right; eapply internal_reductions_is_internal_step; eauto.

  - left; eapply external_self_implies_external_step; eauto.

Qed.

Lemma external_step_leaves_internal_unchanged :
  forall M1 M2 σ, external_step M1 M2 σ ->
             forall σ0 α o, M1 ⦂ M2 ⦿
                          {pre: fun σ => ⟦ α ↦ o ⟧ ∈ σ /\
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α) internal)}
                          σ
                          {post: fun σ' => ⟦ α ↦ o ⟧ ∈ σ'}.
Proof.
Admitted.

Lemma fieldChange_not_heapUnchanged :
  forall M1 M2 σ0 σ α f v, M1 ⦂ M2 ◎ σ0 … ̱ ⊨ {pre: ex_acc_f (e_ α) f ⩶̸ v} σ {post: ex_acc_f (e_ α) f ⩶ v} ->
                      forall σ', M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                            ~ heapUnchanged σ σ'.
Proof.

Admitted.

Lemma not_eq_implies_neq :
  forall M1 M2 σ0 σ e1 e2, ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e2) ->
                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶̸ e2).
Proof.
Admitted.

Lemma not_neq_implies_eq :
  forall M1 M2 σ0 σ e1 e2, ~ M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶̸ e2) ->
                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (e1 ⩶ e2).
Proof.
Admitted.

Lemma update_contn_map :
  forall ϕ c, vMap (update_ϕ_contn ϕ c) = vMap ϕ.
Proof.
  intros ϕ c;
    destruct ϕ;
    auto.
Qed.

Lemma external_step_is_not_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 ~ external_step M1 M2 σ1.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    auto.

  intro Hcontra.
  unfold external_step in *;
    andDestruct.
  destruct σ as [χ ψ].

  repeat match goal with
         | [H : _ \/ _ |- _] =>
           destruct H
         end;

    try (unfold is_assgn, is_new, is_if in *;
         repeat destruct_exists_loo;
         andDestruct;
         match goal with
         | [H : contn_is _ _ |- _] =>
           inversion H;
           simpl in *;
           subst
         end;
         inversion H0;
         subst;
         simpl_crush;
         try solve [match goal with
                    | [Ha : contn _ = _,
                            Hb : contn _ = _ |- _] =>
                      rewrite Ha in Hb;
                      inversion Hb
                    end];
         try (unfold internal_self, is_internal,
              external_self, is_external in *;
              repeat destruct_exists_loo;
              andDestruct;
              repeat map_rewrite;
              unfold vMap in *;
              try eq_auto;
              match goal with
              | [_ : contn ?ϕ = _ |- _] =>
                destruct ϕ;
                repeat simpl_crush
              end)).

  - destruct (eq_dec α0 α);
      subst;
      eq_auto;
      unfold cname in *;
      repeat simpl_crush.

  - destruct (eq_dec α0 α);
      subst;
      eq_auto;
      unfold cname in *;
      repeat simpl_crush.
    match goal with
    | [H : fresh_χ _ _ |- _] =>
      apply fresh_heap_none in H
    end.
    crush.

  - unfold is_call_to in *;
      repeat destruct_exists_loo;
      andDestruct;
      match goal with
      | [H : contn_is _ _ |- _] =>
        inversion H;
          simpl in *;
          subst
      end;
      inversion H0;
      subst;
      simpl_crush;
      repeat match goal with
             | [Ha : contn _ = _,
                     Hb : contn _ = _ |- _] =>
               rewrite Ha in Hb;
                 inversion Hb;
                 subst;
                 clear Hb
             end;
      subst.
    unfold internal_self, is_internal, is_external in *;
      repeat destruct_exists_loo;
      andDestruct;
      match goal with
      | [Hint : ⌊ _ ⌋ _ ≜ _ |- _] =>
        inversion Hint;
          subst
      end;
      repeat map_rewrite;
      unfold vMap in *;
      eq_auto;
      andDestruct;
      repeat simpl_crush.

  - unfold is_return_to, is_rtrn, waiting_frame_is in *;
      andDestruct;
      repeat destruct_exists_loo;
      andDestruct;
      simpl in *;
      subst.

    match goal with
    | [H : _ \/ _ |- _] =>
      destruct H
    end.

    + match goal with
      | [H : contn_is _ _ |- _] =>
        inversion H;
          simpl in *;
          subst
      end;
        repeat simpl_crush.
      inversion H0;
        subst;
        repeat simpl_crush.
      match goal with
      | [H : contn ?ϕ = c_hole _ _,
             Ha : external_self _ _ (_, ?ϕ :: _),
                  Hb : internal_self _ _ (_, update_ϕ_contn _ _ :: _)|- _ ] =>
        unfold external_self, is_external, internal_self, is_internal in Ha, Hb
      end;
        repeat destruct_exists_loo;
        andDestruct;
        repeat map_rewrite.
      rewrite update_contn_map in Ha2.
      destruct ϕ';
        simpl in *.
      repeat map_rewrite.
      crush.

    + destruct_exists_loo.
      match goal with
      | [H : contn_is _ _ |- _] =>
        inversion H;
          simpl in *;
          subst
      end;
        repeat simpl_crush.
      inversion H0;
        subst;
        repeat simpl_crush.
      match goal with
      | [H : contn ?ϕ = c_hole _ _,
             Ha : external_self _ _ (_, ?ϕ :: _),
                  Hb : internal_self _ _ (_, update_ϕ_contn _ _ :: _)|- _ ] =>
        unfold external_self, is_external, internal_self, is_internal in Ha, Hb
      end;
        repeat destruct_exists_loo;
        andDestruct;
        repeat map_rewrite.
      rewrite update_contn_map in Ha2.
      destruct ϕ';
        simpl in *.
      repeat map_rewrite.
      crush.

Qed.

Lemma external_self_is_external :
  forall M1 M2 σ0 σ, external_self M1 M2 σ ->
                     exists α, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_name (a_ α) this ∧
                                                   ((a_ α) external)).
Proof.
  intros M1 M2 σ0 σ Hext.
  unfold external_self, is_external in *;
    repeat destruct_exists_loo;
    andDestruct.

  a_prop;
    eauto with chainmail_db.
Qed.

Lemma mutation_is_assignment :
  forall M σ σ', M ∙ σ ⤳ σ' ->
                 forall M1 M2 σ0 α v f,
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ (ex_acc_f (e_ α) f ⩶ (ex_val v)) ->
                   M1 ⦂ M2 ◎ σ0 … σ' ⊨ (ex_acc_f (e_ α) f ⩶̸ (ex_val v)) ->
                   M ∙ σ ⤳ σ' ->
                   M1 ⋄ M2 ≜ M ->
                   is_assgn σ.
Proof.
  intros M σ σ' Hred;                                
    inversion Hred;
    subst;
    clear Hred;
    intros;
    try solve [match goal with
               | [H : context [_ ≔ _ ;; _] |- _ ] =>
                 unfold is_assgn;
                 repeat eexists;
                 eauto
               end];
    try solve [repeat match goal with
                      | [H : _ ⦂ _ ◎ _ … _ ⊨ _ |- _] =>
                        inversion H;
                        subst;
                        clear H
                      end;
               repeat link_unique_auto;
               repeat match goal with
                      | [H : is_exp _ _ |- _ ] =>
                        inversion H;
                        subst;
                        clear H
                      end;
               repeat match goal with
                      | [Ha : _ ∙ _ ⊢ _ ↪ _,
                              Hstmt : _ = c_stmt (s_if ?e _ _ ;; _),
                                      Hb : _ ∙ _ ⊢ ?e ↪ _ |- _] =>
                        inversion Ha;
                        subst;
                        clear Ha
                      end;
               repeat match goal with
                      | [Ha : _ ∙ _ ⊢ _ ↪ _  |- _] =>
                        match goal with
                        | [_ : _ = c_stmt (s_if _ _ _ ;; _) |- _ ] =>
                          fail 1
                        | _ =>
                          idtac
                        end;
                        inversion Ha;
                        subst;
                        clear Ha
                      end;
               repeat map_rewrite;
               simpl_crush;
               crush].

  - repeat match goal with
           | [H : _ ⦂ _ ◎ _ … _ ⊨ _ |- _] =>
             inversion H;
               subst;
               clear H
           end.
    repeat link_unique_auto.
    repeat match goal with
           | [H : is_exp _ _ |- _ ] =>
             inversion H;
               subst;
               clear H
           end.
    repeat match goal with
           | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
             inversion H;
               subst;
               clear H
           end.
    repeat map_rewrite.
    destruct (eq_dec α0 α);
      subst;
      eq_auto.
    + match goal with
      | [Hfresh : fresh_χ ?χ ?α,
                  H : ?χ ?α = Some _ |- _] =>
        rewrite (fresh_heap_none χ α Hfresh) in H
      end.
      crush.
    + simpl_crush.
      crush.
Qed.

Lemma external_step_does_not_mutate_internal_fields :
  forall M1 M2 σ0 σ, external_step M1 M2 σ ->
                forall α v f, M1 ⦂ M2 ◎ σ0 … ̱ ⊨
                            {pre: (((a_ α) internal) ∧
                                   (ex_acc_f (e_ α) f ⩶ (ex_val v)))}
                            σ
                            {post: ex_acc_f (e_ α) f ⩶ (ex_val v)}.
Proof.
  intros M1 M2 σ0 σ Hext α v f.
  apply ht_pr;
    intros.

  apply not_nsat_implies_sat;
    intros Hcontra.

  a_prop.

  unfold external_step in *.
  andDestruct.

  match goal with
  | [H : _ ⦂ _ ⦿ _ ⤳ _ |- _] =>
    inversion H;
      subst
  end.

  - contradiction (external_step_is_not_reductions M1 M2 σ σ2);
      unfold external_step;
      auto.

  - assert (is_assgn σ);
      [eapply mutation_is_assignment; eauto|].

    + let Hcontra := fresh "Hcontra" in
      apply not_eq_implies_neq;
        apply nsat_implies_not_sat;
        auto.

    + unfold is_assgn in *;
        repeat destruct_exists_loo;
        andDestruct.
      match goal with
      | [Hcontn : contn_is _ ?σ |- _ ] =>
        inversion Hcontn;
          subst;
          clear Hcontn;
          let χ := fresh "χ" in
          let ψ := fresh "ψ" in
          destruct σ as [χ ψ];
            simpl in *;
            subst
      end.
      match goal with
      | [H : _ ∙  _ ⤳ _  |- _] =>
        inversion H;
          subst;
          repeat simpl_crush
      end.

      * match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end;
        match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊭ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end;
        repeat link_unique_auto;
        is_exp_auto;
        try (match goal with
        | [H : _ ∙ _ ⊢ ?e ↪ _,
               H' : context[_ ≔′ ?e] |- _] =>
          clear H
        end);
        repeat match goal with
               | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
                 inversion H;
                   subst;
                   clear H
               end;
        repeat map_rewrite;
        repeat simpl_crush;
        crush.

      * match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end.
        match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊭ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end.
        repeat link_unique_auto.
        is_exp_auto.
        repeat match goal with
               | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
                 inversion H;
                   subst;
                   clear H
               end.
        repeat map_rewrite.
        repeat simpl_crush.

      * match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end.
        match goal with
        | [H : _ ⦂ _ ◎ _ … _ ⊭ (_ ⩶ _) |- _ ] =>
          inversion H;
            subst;
            clear H
        end.
        repeat link_unique_auto.
        is_exp_auto.
        repeat match goal with
               | [H : _ ∙ _ ⊢ _ ↪ _ |- _ ] =>
                 inversion H;
                   subst;
                   clear H
               end.
        repeat map_rewrite.
        (* if the original interal object is the same object we are mutating  *)
        destruct (eq_dec α α0);
          subst;
          eq_auto.

        ** (* we are mutating the interal object -> contradiction*)
          repeat match goal with
                  | [Hclass : classOf _ _ _ |- _] =>
                    inversion Hclass;
                      subst;
                      clear Hclass
                  end.
           repeat interpretation_rewrite.
           repeat simpl_crush.
           repeat match goal with
                  | [Hint : ⌊ _ ⌋ _ ≜ _ |- _] =>
                    inversion Hint;
                      subst;
                      clear Hint
                  end.
           unfold external_self, is_external in *;
             repeat destruct_exists_loo;
             andDestruct.
           repeat map_rewrite.
           repeat simpl_crush.
           match goal with
           | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ internal) |- _] =>
             inversion H;
               subst;
               clear H
           end.
           destruct_exists_loo.
           repeat map_rewrite.
           repeat simpl_crush.

        ** (* we are not mutating the interal object -> contradiction*)
          repeat simpl_crush.

Qed.

Definition contains_method_call (m : mth)(C : cls)(M : mdl):=
  forall CDef, M C = Some CDef ->
          forall s zs, c_meths CDef m = Some (zs, s) ->
                  exists x y m' β, substmt (s_meth x y m' β) s.

Definition external_stack (M : mdl)(σ : config) :=
  forall ϕ, In ϕ (snd σ) ->
       exists α o,  vMap ϕ this = Some (v_addr α) /\
               fst σ α = Some o /\
               M (cname o) = None.

Lemma external_stack_internal_step_is_method_call :
  forall M1 M2 σ, internal_step M1 M2 σ ->
             external_stack M1 σ ->
             is_call_to (is_internal M1 M2) σ.
Proof.
  intros.
  unfold internal_step in *.
  match goal with
  | [H : _ \/ _ |- _] =>
    destruct H
  end;
    auto.
  unfold external_stack, is_return_to, waiting_frame_is in *;
    andDestruct;
    repeat destruct_exists_loo;
    andDestruct.
  let χ := fresh "χ" in
  let ψ := fresh "ψ" in
  destruct σ as [χ ψ];
    simpl in *;
    subst.

  match goal with
  | [H : forall ϕ, In ϕ (?ϕ1 :: ?ϕ2 :: ?ψ) -> _ |- _] =>
    specialize (H ϕ2 (in_cons ϕ1 ϕ2 (ϕ2 :: ψ) (in_eq ϕ2 ψ)))
  end.
  repeat destruct_exists_loo;
    andDestruct.
  unfold internal_self, is_internal in *;
    repeat destruct_exists_loo;
    andDestruct.
  repeat map_rewrite;
    repeat simpl_crush.
Qed.

Lemma substmt_equality :
  forall s1 s2, substmt s1 s2 ->
           s1 = s2 \/
           (exists e s s', s2 = s_if e s s' /\
                      (substmt s1 s \/
                       substmt s1 s')) \/
           (exists s s', s2 = s ;; s' /\
                    (substmt s1 s \/
                     substmt s1 s')).
Proof.
  intros s1 s2 Hsub;
    induction Hsub;
    auto with loo_db;
    try match goal with
        | [|- context [s_if _ _ _ = s_if _ _ _]] =>
          right; left;
            try solve [repeat eexists;
                       auto with loo_db]
        | [|- context [_ ;; _ = _ ;; _]] =>
          right; right;
            try solve [repeat eexists;
                       auto with loo_db]
        end.

  -  repeat match goal with
            | [H : _ \/ _ |- _] =>
              destruct H
            end;
       subst;
       repeat destruct_exists_loo;
       andDestruct;
       subst;
       auto with loo_db;
       try solve [right; left; eauto];
       try solve [right; right; eauto];
       match goal with
       | [|- context [s_if _ _ _ = s_if _ _ _]] =>
         right; left
       | [|- context [_ ;; _ = _ ;; _]] =>
         right; right
       end;
       try solve [repeat eexists;
                  match goal with
                  | [H : substmt _ ?s1 \/ substmt _ ?s2 |- substmt ?s ?s1 \/ substmt ?s ?s2] =>
                    destruct H;
                    eauto with loo_db
                  end].

Qed.

Lemma substmt_stmts :
  forall s s1 s2, substmt s (s1 ;; s2) ->
             s = (s1 ;; s2) \/ substmt s s1 \/ substmt s s2.
Proof.
  intros.
  apply substmt_equality in H.
  match goal with
  | [H : _ \/ _ |- _] =>
    destruct H
  end;
    auto.
  repeat match goal with
         | [H : _ \/ _ |- _] =>
           destruct H
         end;
    repeat destruct_exists_loo;
    andDestruct.
  - crush.
  - crush.
Qed.

Definition atomic_stmt (s : stmt) :=
  forall s1 s2, s <> s1 ;; s2 /\ forall e, s <> s_if e s1 s2.

Lemma atomic_asgn :
  forall r1 r2, atomic_stmt (r1 ≔ r2).
Proof.
  intros;
    unfold atomic_stmt;
    crush.
Qed.

Lemma atomic_new :
  forall x C β, atomic_stmt (s_new x C β).
Proof.
  intros;
    unfold atomic_stmt;
    crush.
Qed.

Lemma atomic_rtrn :
  forall x, atomic_stmt (s_rtrn x).
Proof.
  intros;
    unfold atomic_stmt;
    crush.
Qed.

Lemma atomic_meth :
  forall x y m β, atomic_stmt (s_meth x y m β).
Proof.
  intros;
    unfold atomic_stmt;
    crush.
Qed.

Ltac atomic_auto :=
  match goal with
  | [H : atomic_stmt (?s1 ;; ?s2) |- _] =>
    let Ha := fresh in
    unfold atomic_stmt in H;
    specialize (H s1 s2);
    destruct H as [Ha];
    contradiction Ha;
    auto
  | [H : atomic_stmt (s_if ?e ?s1 ?s2) |- _] =>
    let Ha := fresh in
    let Hb := fresh in
    unfold atomic_stmt in H;
    specialize (H s1 s2);
    destruct H as [Ha Hb];
    specialize (Hb e);
    contradiction Hb;
    auto
  | [|- atomic_stmt (s_meth _ _ _ _)] =>
    apply atomic_meth
  | [|- atomic_stmt (_ ≔ _)] =>
    apply atomic_asgn
  | [|- atomic_stmt (s_new _ _ _)] =>
    apply atomic_new
  | [|- atomic_stmt (s_rtrn _)] =>
    apply atomic_rtrn
  end.

Lemma atomic_substmt :
  forall s1 s2, substmt s1 s2 ->
           atomic_stmt s2 ->
           s1 = s2.
Proof.
  intros s1 s2 Hsub;
    induction Hsub;
    intros;
    auto with loo_db;
    try solve [atomic_auto].

  -  auto_specialize;
       subst;
       auto_specialize;
       auto.
Qed.

Lemma atomic_substmt_merge :
  forall s1 s2 s, substmt s (merge s1 s2) ->
                  atomic_stmt s ->
                  substmt s s1 \/ substmt s s2.
Proof.
  intro s1;
    induction s1;
    intros;
    simpl in *;
    match goal with
    | [H : substmt ?s (?s1 ;; ?s2) |- _] =>
      apply substmt_stmts in H
    end;
    try solve [repeat match goal with
                      | [H : _ \/ _ |- _] =>
                        destruct H;
                        subst
                      end;
               auto;
               atomic_auto].

  - repeat match goal with
           | [H : _ \/ _ |- _] =>
             destruct H
           end;
      subst;
      try solve [atomic_auto];
      eauto with loo_db.
    specialize (IHs1_2 s2 s);
      repeat auto_specialize.
    repeat match goal with
           | [H : _ \/ _ |- _] =>
             destruct H
           end;
      eauto with loo_db.
Qed.

Lemma no_method_calls_internal_step :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 external_stack M1 σ1 ->
                 (forall m C, ~ contains_method_call m C M1) ->
                        exists ϕ1 x y m β s1 ϕ2 s2 ψ, vMap ϕ1 y = vMap ϕ2 this /\
                                                 snd σ1 = ϕ1 :: ψ /\
                                                 contn ϕ1 = c_stmt ((s_meth x y m β) ;; s1) /\
                                                 snd σ2 = ϕ2 :: (frm (vMap ϕ1) (c_hole x s1)) :: ψ /\
                                                 contn ϕ2 = c_stmt s2 /\
                                                 (forall x' y' m' β', ~ substmt (s_meth x' y' m' β') s2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  - assert (is_call_to (is_internal M1 M2) σ);
      [apply external_stack_internal_step_is_method_call;
       auto;
       eapply internal_reductions_is_internal_step; eauto with loo_db
      |].
    unfold is_call_to in *;
      repeat destruct_exists_loo;
      andDestruct.
    match goal with
    | [Hcontn : contn_is _ ?σ |- _] =>
      let χ := fresh "χ" in
      let ψ := fresh "ψ" in
      destruct σ as [χ ψ];
        inversion Hcontn;
        simpl in *;
        subst
    end.
    match goal with
    | [H : _ ∙ _ ⤳ _ |- _ ] =>
      inversion H;
        subst;
        repeat simpl_crush
    end.
    match goal with
    | [H : contn ?ϕ = c_stmt (s_meth ?x ?y ?m ?β;; ?s),
           Hint : ⌊ ?y ⌋ (_, ?ϕ :: ?ψ) ≜ v_ ?α,
                  Hmeth : c_meths _ ?m = Some (_, ?s') |-
       exists (_ : frame)(_ : var)(_ : var)(_ : mth)(_ : partial_map var var)
         (_ : stmt)(_ : frame)(_ : stmt)(_ : list frame), _] =>
      exists ϕ, x, y, m, β, s, (frm (update this (v_ α) (β ∘ vMap ϕ)) (c_stmt s')), s', ψ
    end.
    repeat split;
      intros;
      auto.

    + match goal with
      | [H : ⌊ _ ⌋ _ ≜ _ |- _] =>
        inversion H;
          subst;
          clear H
      end.
      repeat map_rewrite.
      match goal with
      | [H : ?x = _ |- ?x = _] =>
        rewrite H
      end.
      unfold vMap.
      eq_auto.

    + intro Hcontra.
      match goal with
      | [H : forall m' C', ~ contains_method_call  m' C' _,
           Ha : ?M ?C = Some ?CDef,
           Hb : c_meths ?CDef ?m = Some (_, _) |- _] =>
        specialize (H m C);
          contradiction H
      end.
      unfold contains_method_call.
      intros.
      unfold is_internal in *.
      repeat destruct_exists_loo;
        andDestruct.
      match goal with
      | [H : ⌊ _ ⌋ _ ≜ _ |- _] =>
        inversion H;
          subst;
          clear H
      end.
      repeat map_rewrite.
      match goal with
      | [H : _ ⋄ _ ≜ _ |- _] =>
        inversion H;
          subst
      end.
      match goal with
      | [Ha : context[(?M1 ∪ _) ?x],
              Hb : ?M1 ?x = _ |- _] =>
        unfold extend in Ha;
          rewrite Hb in Ha
      end.
      repeat simpl_crush.
      eauto.

  - repeat auto_specialize.
    repeat destruct_exists_loo.
    andDestruct.
    exists ϕ, x, x0, m, β, s.
    match goal with
    | [Hreduce : _ ∙ _ ⤳ _ |- _] =>
      inversion Hreduce;
        subst
    end;
      try solve [match goal with
                 | [_ : context [s_asgn _ _] |- _] =>
                   idtac
                 | [_ : context [s_new _ _ _] |- _] =>
                   idtac
                 end;
                 simpl in *;
                 repeat simpl_crush;
                 repeat eexists;
                 eauto;
                 simpl;
                 repeat map_rewrite;
                 intros; intro Hcontra;
                 match goal with
                 | [Ha : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) (_ ;; ?s),
                      Hb : substmt (s_meth ?x ?y ?m ?β) ?s |- _] =>
                   contradiction (Ha x y m β);
                   eauto with loo_db
                 end].

    + simpl in *;
        repeat simpl_crush.
      match goal with
      | [H : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) (s_meth ?x ?y ?m ?β;; _) |- _] =>
        contradiction (H x y m β)
      end.
      eauto with loo_db.

    + simpl in *.
      repeat simpl_crush.
      repeat eexists;
        eauto.
      intros; intro Hcontra.
      apply atomic_substmt_merge in Hcontra;
        [destruct Hcontra|atomic_auto].
      * match goal with
        | [Ha : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) ((s_if _ ?s _);; _),
             Hb : substmt (s_meth ?x ?y ?m ?β) ?s |- _] =>
          contradiction (Ha x y m β)
        end.
        eauto with loo_db.
      * match goal with
        | [Ha : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) (_ ;; ?s),
             Hb : substmt (s_meth ?x ?y ?m ?β) ?s |- _] =>
          contradiction (Ha x y m β)
        end.
        eauto with loo_db.

    + simpl in *.
      repeat simpl_crush.
      repeat eexists;
        eauto.
      intros; intro Hcontra.
      apply atomic_substmt_merge in Hcontra;
        [destruct Hcontra|atomic_auto].
      * match goal with
        | [Ha : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) ((s_if _ _ ?s);; _),
             Hb : substmt (s_meth ?x ?y ?m ?β) ?s |- _] =>
          contradiction (Ha x y m β)
        end.
        eauto with loo_db.
      * match goal with
        | [Ha : forall _ _ _ _, ~ substmt (s_meth _ _ _ _) (_ ;; ?s),
             Hb : substmt (s_meth ?x ?y ?m ?β) ?s |- _] =>
          contradiction (Ha x y m β)
        end.
        eauto with loo_db.

    + simpl in *.
      repeat simpl_crush.
      unfold internal_self, is_internal in *;
          repeat destruct_exists_loo;
          andDestruct.
      repeat map_rewrite.
      simpl in *.
      repeat map_rewrite.
      unfold external_stack in *.
      match goal with
      | [Ha : snd ?σ = _,
              Hb : context [snd ?σ] |- _ ] =>
        rewrite Ha in Hb
      end.

      specialize (H2 ϕ (in_eq ϕ ψ)).
      repeat destruct_exists_loo;
        andDestruct.

      specialize (H2 or_introl).
            auto_specialize.

      match goal with
      | [H : c_hole _ _ = c_hole _ _ |- _] =>
        inversion H;
          subst;
          clear H
      end.



Qed.


Lemma no_method_calls_internal_steps_method_calls :
  forall M1 M2 σ0 σ, M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                initial σ0 ->
                internal_step M1 M2 σ ->
                forall m C, ~ contains_method_call m C M1 ->
                       is_call_to (is_internal M1 M2) σ.
Proof.
  intros M1 M2 σ0 σ Hred;
    induction Hred;
    intros.

  - match goal with
    | [H : internal_step _ _ _ |- _] =>
      unfold internal_step in H;
        destruct H;
        auto
    end.

    unfold initial in *;
      repeat destruct_exists_loo;
      andDestruct;
      subst.


  -
Qed.



(*Lemma external_step_leaves_internal_field_unchanged_neq :
  forall M1 M2 σ0 σ α, M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α) internal) ->
                  forall f v, M1 ⦂ M2 ◎ σ0 … σ ⊨ (ex_acc_f (e_ α) f ⩶̸ v) ->
                         external_step M1 M2 σ ->
                         forall σ', M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                               M1 ⦂ M2 ◎ σ0 … σ' ⊨ (ex_acc_f (e_ α) f ⩶̸ v).
Proof.

Admitted.*)

(*Lemma internal_class_implies_internal :
  forall M1 M2 σ0 σ α C, M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_class (a_ α) C) ->
                    (exists CDef, M1 C = Some CDef) ->
                    forall σ0' σ', M1 ⦂ M2 ◎ σ0' … σ' ⊨ ((a_ α) internal).
Proof.
Admitted.*)
