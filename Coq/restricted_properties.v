Require Import loo_reduction_properties.
Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma mapp_iff_vMap_Some :
  forall x v χ ϕ ψ, ⟦ x ↦ v ⟧ ∈ (χ, ϕ :: ψ) <->
    vMap ϕ x = Some v
.
Proof.
  intros x v χ ϕ ψ.
  unfold mapp.
  unfold configMapStack.
  unfold mapp.
  unfold stackMap.
  simpl.
  reflexivity.
Qed.

Hint Resolve mapp_iff_vMap_Some : loo_db.

Lemma restriction_implies_same :
  forall ψ χ Σ χ' α o o', (χ, ψ) ↓ Σ ≜ (χ', ψ) ->
    χ α = Some o ->
    χ' α = Some o' ->
    o = o'
.
Proof.
  intros ψ χ Σ χ' α o o' HϕΣ H H'.
  inversion HϕΣ.
  simpl in *. subst.
  apply H3 in H'.
  rewrite H in H'.
  inversion H'.
  trivial.
Qed.

Hint Resolve restriction_implies_same : loo_db.

Lemma mapp_ingores_heap : 
  forall x v (χ χ' : heap) ψ,
    ⟦ x ↦ v ⟧ ∈ (χ', ψ) ->
    ⟦ x ↦ v ⟧ ∈ (χ, ψ)
.
Proof.
  intros x v χ χ' ψ Hexpanded.
  unfold mapp in *. 
  unfold configMapStack in *. 
  simpl in *.
  assumption.
Qed.

Hint Resolve mapp_ingores_heap : loo_db.

Lemma restricted_classOf_implies_classOf :
  forall x χ ψ C Σ ϕΣ, (χ, ψ) ↓ Σ ≜ ϕΣ ->
    classOf x ϕΣ C ->
    classOf x (χ, ψ) C
.
Proof.
  intros x χ ψ C Σ ϕΣ HϕΣ Hclass.
  inversion HϕΣ.
  inversion Hclass.
  inversion H7.
  subst; simpl in *.
  apply (cls_of x (χ, ψ) α χ o (cname o)); eauto with loo_db.
Qed.

Hint Resolve restricted_classOf_implies_classOf : loo_db.

Lemma has_self_σ_top_frame_has_self_ϕ :
  forall χ ϕ ψ, has_self_σ (χ, ϕ :: ψ) ->
    has_self_ϕ χ ϕ
.
Proof.
  intros χ ϕ ψ Hself.
  inversion Hself; subst.
  assert (In ϕ (ϕ :: ψ)). { crush. }
  apply H0 in H.
  assumption.
Qed.

Hint Resolve has_self_σ_top_frame_has_self_ϕ : loo_db.

Lemma restricted_external_self_implies_external_self :
  forall M1 M2 χ χ' ϕ ψ Σ, (χ, ϕ :: ψ) ↓ Σ ≜ (χ', ϕ :: ψ) ->
    external_self M1 M2 (χ', ϕ :: ψ) ->
    external_self M1 M2 (χ, ϕ :: ψ)
.
Proof.
  intros M1 M2 χ χ' ϕ ψ Σ HϕΣ Hexternal_self.
  inversion HϕΣ.
  inversion Hexternal_self as [α [o [Hthis [Hα HC]]]].
  subst; simpl in *.
  unfold external_self; unfold is_external.
  exists α, o.
  eauto with loo_db.
Qed.

Hint Resolve restricted_external_self_implies_external_self : loo_db.

Lemma has_top_reduces_to_has_top :
  forall M χ χ' ϕ ψ ψ', M ∙ (χ, ϕ :: ψ) ⤳ (χ', ψ') ->
    exists ϕ' ψ'', ψ' = ϕ' :: ψ''
.
Proof.
  intros M χ χ' ϕ ψ ψ' Hred.
  inversion Hred; subst; eauto with loo_db.
  - exists {| vMap := vMap ϕ0; contn := c_stmt s |}, ψ0.
    crush.
  - exists {| vMap := update this (v_addr α) (ps ∘ vMap ϕ0); contn := c_stmt (merge s (s_rtrn this)) |}, 
      ({| vMap := vMap ϕ0; contn := c_hole x s' |} :: ψ0).
    crush.
Qed.

Hint Resolve has_top_reduces_to_has_top : loo_db.

Lemma restricted_evaluation_implies_evaluation :
  forall M ϕ χ Σ ϕΣ ψ e v, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ ->
    (M ∙ ϕΣ ⊢ e ↪ v) ->
    (M ∙ (χ, ϕ :: ψ) ⊢ e ↪ v)
.
Proof.
  intros M ϕ χ Σ ϕΣ ψ e v HϕΣ Hev.
  generalize dependent χ. generalize dependent ψ. generalize dependent ϕ.
  induction Hev; intros ϕ ψ χ HϕΣ; inversion HϕΣ; subst; simpl in *; eauto with loo_db.
  - apply (v_f_ghost M (χ, ϕ :: ψ) e0 e f α o x e' v v' C); auto with loo_db.
    unfold update_σ_map in *; simpl in *.
    unfold update_ϕ_map in *; simpl in *.
    remember {| vMap := update this (v_addr α) (update x v (vMap ϕ)); contn := contn ϕ |} as ϕ'.
    apply IHHev3.
    eauto.
    (* TODO stuck! *)
    
 (*  - apply (v_f_heap M (χ, ϕ :: ψ) e f α o v); auto with loo_db.
  - apply (v_equals M (χ, ϕ :: ψ) e1 e2 v); auto with loo_db.
  - apply (v_nequals M (χ, ϕ :: ψ) e1 e2 v1 v2); auto with loo_db.
  - apply (v_lt M (χ, ϕ :: ψ) e1 e2 i1 i2); auto with loo_db.
  - apply (v_nlt M (χ, ϕ :: ψ) e1 e2 i1 i2); auto with loo_db. *)
Admitted. (* apply (v_if_true M (χ, ϕ :: ψ) (e1 ⩵ e2) e1 e2 v); auto with loo_db. *)

Lemma restricted_reduction_implies_reduction :
  forall M ϕ ψ χ Σ ϕΣ, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_ϕ χ ϕ ->
    (exists σ, M ∙ ϕΣ ⤳ σ) ->
    (exists σ, M ∙ (χ, ϕ :: ψ) ⤳ σ)
.
Proof.
  intros M ϕ ψ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  inversion Hself as [χ_ ϕ_ [α_this [[C_this flds_this] [Hthisϕ Hthisχ]]]]. subst; simpl in *.
  induction Hσ; subst; inversion HϕΣ; simpl in *; eauto with loo_db.
  - inversion H11.
    inversion H2.
    subst χ0 ϕ0 ψ0 σ Σ0 χ1 x0 σ0 v.
    remember {| vMap := vMap ϕ; contn := c_hole x s' |} as ϕ'.
    remember {| vMap := update this (v_addr α) (ps ∘ vMap ϕ); contn := c_stmt s |} as ϕ''.
    exists (χ, ϕ'' :: ϕ' :: ψ).
    apply (r_mth M ϕ ψ χ x y ps (χ, ϕ :: ψ) m zs α o s s' C ϕ' ϕ''); auto.
    apply int_x.
    crush.
  - subst χ0 ϕ0 ψ0 σ Σ0 χ1.
    exists (χ, {| vMap := update x v (vMap ϕ); contn := c_stmt s |} :: ψ).
    apply (r_eAssgn M χ ϕ ψ x e v s); auto.
    apply restricted_evaluation_implies_evaluation with (ϕΣ:=(χ', ϕ :: ψ)) (Σ:=Σ); eauto.
  - inversion H2.
    subst χ0 ϕ0 ψ0 σ Σ0 χ1 x0 σ0 v0.
    remember (frm (update x v (vMap ϕ)) (c_stmt s)) as ϕ'.
    exists (χ, ϕ' :: ψ).
    apply (r_xAssgn M (χ, ϕ :: ψ) ϕ x y f s ψ χ α v o ϕ' C); eauto with loo_db.
  - inversion H1.
    inversion H2.
    inversion H3.
    inversion H4.
    simpl in *.
    inversion H24.
    inversion H31.
    subst; simpl in *.
    apply mapp_iff_vMap_Some in H38.
    rewrite H38 in Hthisϕ.
    inversion Hthisϕ.
    remember {| cname := C_this; flds := flds_this |} as o'.
    assert (o0 = o'). { eauto with loo_db. }
    subst α0 o0.
    rename χ1 into χ, χ3 into χ', ϕ0 into ϕ, ψ0 into ψ.
    remember (frm (vMap ϕ) (c_stmt s)) as ϕ'.
    remember (update α o' χ) as χ1.
    exists (χ1, ϕ' :: ψ).
    apply (r_fAssgn M (χ, ϕ :: ψ) ϕ ϕ' x y f s ψ χ α v o (χ1, ϕ' :: ψ) χ1 o' C_this); eauto with loo_db.
    + apply restricted_classOf_implies_classOf with (Σ:=Σ) (ϕΣ:=(χ', ϕ :: ψ)).
      eauto with loo_db.
      apply (cls_of this (χ', ϕ :: ψ) α_this χ' o' C_this); subst; eauto with loo_db.
    + apply restricted_classOf_implies_classOf with (Σ:=Σ) (ϕΣ:=(χ', ϕ :: ψ)); eauto with loo_db.
      apply (cls_of y (χ', ϕ :: ψ) α1 χ' o' C_this); subst; eauto with loo_db.
  - inversion H2.
    inversion H3.
    subst χ0 χ1 ϕ0 χ2 ψ0 Σ0 σ; simpl in *.
    remember (frm (vMap ϕ) (c_hole x s')) as ϕ'.
    remember (frm (update this (v_addr α) (ps ∘ (vMap ϕ))) (c_stmt (merge s (s_rtrn this)))) as ϕ''.
    remember (new C fMap) as o.
    remember (update α o χ) as χ1.
    admit. (* TODO fresh in heaps are hard, need proof there is alway a fresh heap address *)
  - subst χ0 χ1 ϕ0 Σ0 σ ψ0; simpl in *.
    remember (frm (vMap ϕ) (c_stmt (merge s1 s))) as ϕ'.
    exists (χ, ϕ' :: ψ); subst.
    apply (r_if1 M χ ϕ ψ e s1 s2 s); eauto with loo_db.
    apply restricted_evaluation_implies_evaluation with (Σ:=Σ) (ϕΣ:=(χ', ϕ :: ψ)); assumption.
  - subst χ0 χ1 ϕ0 Σ0 σ ψ0; simpl in *.
    remember (frm (vMap ϕ) (c_stmt (merge s2 s))) as ϕ'.
    exists (χ, ϕ' :: ψ); subst.
    apply (r_if2 M χ ϕ ψ e s1 s2 s); eauto with loo_db.
    apply restricted_evaluation_implies_evaluation with (Σ:=Σ) (ϕΣ:=(χ', ϕ :: ψ)); assumption.
Admitted.
(*     exists (χ1, ϕ'' :: ϕ' :: nil).
    apply (r_new M (χ, ϕ :: nil) (χ1, ϕ'' :: ϕ' :: nil) χ nil ϕ ϕ' ϕ'' α x C fMap zs s s' o CDef ps); eauto with loo_db; try solve [subst; reflexivity].
    
Admitted. (* H6 : ⌊ y ⌋ (χ', ϕ :: nil) ≜ v_addr α *) *)


Lemma restricted_reductions_implies_reductions : 
  forall M ϕ ψ χ Σ ϕΣ, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_ϕ χ ϕ ->
    (exists σ, M ∙ ϕΣ ⤳⋆ σ) ->
    (exists σ, M ∙ (χ, ϕ :: ψ) ⤳⋆ σ)
.
Proof.
  intros M ϕ ψ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  induction Hσ as [ M σ σ' Hσ | M σ σ' σ'' Hσ Hσ' IHσ ].
  + apply (restricted_reduction_implies_reduction M ϕ ψ χ Σ σ) in Hself; eauto.
    destruct Hself as [σ1 Hσ1].
    exists σ1.
    constructor.
    assumption.
  + apply (restricted_reduction_implies_reduction M ϕ ψ χ Σ σ) in Hself; eauto.
    destruct Hself as [σ1 Hσ1].
    exists σ1.
    constructor. assumption.
Qed.

Lemma restricted_reductions_internal_self_implies_internal_self :
  forall M M1 M2 Σ ϕΣ ϕΣ' χ ϕ ψ σ', (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_σ (χ, ϕ :: ψ) ->
    M1 ⋄ M2 ≜ M ->
    M ∙ ϕΣ ⤳ ϕΣ' ->
    M ∙ (χ, ϕ :: ψ) ⤳ σ' ->
    internal_self M1 M2 ϕΣ' ->
    internal_self M1 M2 σ'
.
Proof. 
    intros M M1 M2 Σ ϕΣ ϕΣ' χ ϕ ψ σ' HϕΣ Hself HM HϕΣ' Hσ' Hinternal_self.
    inversion HϕΣ.
    inversion Hself.
    apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ; inversion Hselfϕ.
    inversion Hinternal_self as [αthis1' [othis1' [Cthis [Hthis1' [Hα1' HCthis]]]]].
    unfold internal_self.
    unfold is_internal.
    subst; simpl in *.
    destruct ϕΣ' as [χ1' ψ1'0].
    destruct σ' as [χ1 ψ10].
    apply has_top_reduces_to_has_top in HϕΣ' as HϕΣ'1; destruct HϕΣ'1 as [ϕ1' [ψ1' Hϕ1']].
    apply has_top_reduces_to_has_top in Hσ' as Hσ'1; destruct Hσ'1 as [ϕ1 [ψ1 Hϕ1]].
    subst; simpl in *.
    destruct H10 as [αthis [othis [Hαthis Hothis]]].
    apply reduction_preserves_config_has_self with (M:=M) (σ2:=(χ1, ϕ1 :: ψ1)) in Hself as Hself'; auto.
    apply has_self_σ_top_frame_has_self_ϕ in Hself' as Hself'ϕ; inversion Hself'ϕ.
    subst; simpl in *.
    destruct H0 as [αthis1 [othis1 [Hαthis1 Hothis1]]].
    exists αthis1, othis1, Cthis. (* α should be vMap ϕ this *)
    split; try split; eauto with loo_db.
    rewrite mapp_iff_vMap_Some in *.
    unfold mapp in Hα1'.
    unfold configMapHeap in Hα1'; simpl in *; subst.
Admitted. (* TODO needs a proof, left for now as distracting *)

(* Lemma restruction_reduction_this_class_is_reduction_this_class :
  forall M Σ χ χ' χ1' ϕ ϕ1' ψ ψ1' α1 α1' othis1 othis1', 
    (χ, ϕ :: ψ) ↓ Σ ≜ (χ', ϕ :: ψ) -> 
    has_self_σ (χ, ϕ :: ψ) ->
    M ∙ (χ', ϕ :: ψ) ⤳ (χ1', ϕ1' :: ψ1') ->
    vMap ϕ' this = Some (v_addr α1') ->
    χ' α1' = Some othis1' ->
    vMap ϕ this = Some (v_addr α1) ->
    χ α1 = Some othis1 ->
    cname othis1 = cname othis1'
.
Proof.
    intros M Σ χ χ' χ1' ϕ ϕ' ϕ1' ψ ψ' ψ1' α1 α1' othis1 othis1'
      HϕΣ Hself Hσ1' Hthis' Hα1' Hthis Hα1.
    inversion HϕΣ.
    inversion Hself.
    apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ.
    subst; simpl in *.
    inversion Hσ1'.
Qed. *)

Lemma restricted_internal_reductions_implies_internal_reductions :
  forall M1 M2 ϕ ψ χ Σ ϕΣ, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_σ (χ, ϕ :: ψ) ->
    (exists σ, M1 ⦂  M2 ⦿ ϕΣ ⤳… σ) ->
    (exists σ, M1 ⦂  M2 ⦿ (χ, ϕ :: ψ) ⤳… σ)
.
Proof.
  intros M1 M2 ϕ ψ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  inversion HϕΣ.
  induction Hσ as [ M1 M2 M σ σ' HM H' | M1 M2 σ σ' σ'' Hσ Hσ' IHσ ]; subst; simpl in *.
  inversion Hself.
  apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ; 
      apply (restricted_reduction_implies_reduction M ϕ ψ χ Σ (χ', ϕ :: ψ)) in Hselfϕ as [[χ'' ψ''0] Hσ'']; 
      eauto; 
      apply has_top_reduces_to_has_top in Hσ'' as Hex;
      destruct Hex as [ϕ'' [ψ'' Heqσ'']]; subst.
  - exists (χ'', ϕ'' :: ψ'').
    apply pr_single with (M1:=M1) (M2:=M2) in Hσ''; eauto with loo_db.
    inversion H8 as [α [o [C [Hthis [Hα HC]]]]].
    apply (restricted_reductions_internal_self_implies_internal_self
      M M1 M2 Σ (χ', ϕ :: ψ) σ' χ ϕ ψ (χ'', ϕ'' :: ψ'')
    ); eauto with loo_db.
  - apply IHσ in HϕΣ as [σ' H']; trivial.
    exists σ'.
    assumption.
Qed.




Lemma restricted_reductions_external_self_implies_external_self :
  forall M M1 M2 Σ ϕΣ ϕΣ' χ ϕ ψ σ', (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_σ (χ, ϕ :: ψ) ->
    M1 ⋄ M2 ≜ M ->
    M ∙ ϕΣ ⤳ ϕΣ' ->
    M ∙ (χ, ϕ :: ψ) ⤳ σ' ->
    external_self M1 M2 ϕΣ' ->
    external_self M1 M2 σ'
.
Proof. 
    intros M M1 M2 Σ ϕΣ ϕΣ' χ ϕ ψ σ' HϕΣ Hself HM HϕΣ' Hσ' Hexternal_self.
    inversion HϕΣ.
    inversion Hself.
    apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ; inversion Hselfϕ.
    inversion Hexternal_self as [α [o [Hthis [Hα HC]]]].
    unfold external_self.
    unfold is_external.
    subst; simpl in *.
    destruct ϕΣ' as [χ1' ψ1'0].
    destruct σ' as [χ1 ψ10].
    apply has_top_reduces_to_has_top in HϕΣ' as HϕΣ'1; destruct HϕΣ'1 as [ϕ1' [ψ1' Hϕ1']].
    apply has_top_reduces_to_has_top in Hσ' as Hσ'1; destruct Hσ'1 as [ϕ1 [ψ1 Hϕ1]].
    subst; simpl in *.
    destruct H10 as [αthis [othis [Hαthis Hothis]]].
    apply reduction_preserves_config_has_self with (M:=M) (σ2:=(χ1, ϕ1 :: ψ1)) in Hself as Hself'; auto.
    apply has_self_σ_top_frame_has_self_ϕ in Hself' as Hself'ϕ; inversion Hself'ϕ.
    subst; simpl in *.
    destruct H0 as [αthis' [othis' [Hαthis' Hothis']]].
    exists αthis', othis'. (* α should be vMap ϕ this *)
    split; try split; eauto with loo_db.
    rewrite mapp_iff_vMap_Some in *.
    unfold mapp in Hα.
    unfold configMapHeap in Hα; simpl in *.
Admitted. (* TODO needs a proof, left for now as distracting *)


Lemma restricted_pair_reduction_implies_pair_reduction :
  forall M1 M2 ϕ ψ χ Σ ϕΣ, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_σ (χ, ϕ :: ψ) ->
    (exists σ, M1 ⦂  M2 ⦿ ϕΣ ⤳ σ) ->
    (exists σ, M1 ⦂  M2 ⦿ (χ, ϕ :: ψ) ⤳ σ)
.
Proof.
  intros M1 M2 ϕ ψ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  inversion HϕΣ.
  inversion Hself.
  apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ.
  inversion Hselfϕ; subst; simpl in *.
  destruct H10 as [αthis [othis [Hαthis Hothis]]].
  inversion Hσ; subst; simpl in *.
  - apply restricted_internal_reductions_implies_internal_reductions 
      with (M1:=M1) (M2:=M2) in HϕΣ as HϕΣ'; try (destruct HϕΣ' as [σ' Hσ']);
      eauto with loo_db.
    exists σ'.
    apply (p_external M1 M2 M (χ, ϕ :: ψ) σ'); eauto with loo_db.
    + apply restricted_reduction_implies_reduction with (M:=M) in HϕΣ as [σ'' Hσ'']; trivial.
      inversion Hσ'; subst; link_unique_auto; eauto with loo_db.
      admit. (* TODO AHHH *)
      admit.
    + apply restricted_reduction_implies_reduction with (M:=M) in HϕΣ as [σ'' Hσ'']; trivial.
      admit.
Abort.

Lemma restricted_pair_reduction_implies_pair_reduction :
  forall M1 M2 ϕ ψ χ Σ ϕΣ, (χ, ϕ :: ψ) ↓ Σ ≜ ϕΣ -> has_self_σ (χ, ϕ :: ψ) ->
    (exists σ, M1 ⦂  M2 ⦿ ϕΣ ⤳ σ) ->
    (exists σ, M1 ⦂  M2 ⦿ (χ, ϕ :: ψ) ⤳ σ)
.
Proof.
  intros M1 M2 ϕ ψ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  inversion HϕΣ.
  inversion Hself.
  apply has_self_σ_top_frame_has_self_ϕ in Hself as Hselfϕ.
  inversion Hselfϕ; subst.
  destruct H10 as [αthis [othis [Hαthis Hothis]]].
  apply restricted_internal_reductions_implies_internal_reductions 
        with (M1:=M1) (M2:=M2) in HϕΣ as HϕΣ'; try (destruct HϕΣ' as [σ' Hσ']); 
        eauto with loo_db.
  - inversion Hσ'; subst; simpl in *; eauto with loo_db.
    + exists σ'.
      apply p_internal with (M:=M) (σ:=(χ, ϕ :: ψ)); eauto with loo_db.
      apply (restricted_reductions_external_self_implies_external_self
        M M1 M2 Σ (χ', ϕ :: ψ) σ χ ϕ ψ σ'
      ) in HϕΣ; eauto with loo_db.
    (* inversion Hσ'; link_unique_auto; subst; eauto with loo_db. *)
    (* exists σ'.
    apply p_internal with (M:=M) (σ:=(χ, ϕ :: ψ)); eauto with loo_db. *)
(*     apply (restricted_reductions_external_self_implies_external_self
      M M1 M2 Σ (χ', ϕ :: ψ) σ χ ϕ ψ σ'
    ) in HϕΣ; eauto with loo_db. *)
Abort.

(* --- --- --- --- --- --- --- --- --- ---

TODO: The following may or do not hold, but will help future investigations

  --- --- --- --- --- --- --- --- --- --- *)

Lemma exists_fresh_χ :
  forall χ ψ, σ_wf (χ, ψ) -> exists α, fresh_χ χ α
.
Proof.
  intros.
  inversion H.
  inversion H0.
  inversion H2.
  inversion H3.
  inversion H4.
  inversion H5.
  subst.
  assert (Hexists_max_χ : exists α, max_χ χ α). { admit. }
Abort.

Lemma restricted_fresh_implies_fresh :
  forall χ χ' α ψ Σ, (χ, ψ) ↓ Σ ≜ (χ', ψ) ->
    fresh_χ χ' α ->
    fresh_χ χ α
.
Proof.
  intros χ χ' α ψ Σ HϕΣ Hfresh.
  inversion Hfresh.
  inversion HϕΣ.
  constructor.
  inversion H.
  destruct H10 as [b Hb].
  apply H5 in Hb.
  constructor; subst; simpl in *.
  + exists b. assumption.
  + intros α' b' H'.
    apply H11 with (b:=b').
Abort.
(* Lemma restricted_reduction_implies_reduction' :
  forall M ϕ χ Σ ϕΣ, (χ, ϕ :: nil) ↓ Σ ≜ ϕΣ -> has_self_ϕ χ ϕ ->
    (exists σ, M ∙ ϕΣ ⤳ σ) ->
    (exists σ, M ∙ (χ, ϕ :: nil) ⤳ σ)
.
Proof.
  intros M ϕ χ Σ ϕΣ HϕΣ Hself [σ Hσ].
  inversion Hself as [χ_ ϕ_ [α_this [[C_this flds_this] [Hthisϕ Hthisχ]]]]. subst; simpl in *.
  inversion Hσ; subst; inversion HϕΣ; simpl in *; eauto with loo_db.
  - inversion H2.
    inversion H6.
    subst χ0 χ1 ϕ0 ψ Σ0 σ σ0 v x0 .
    remember {| vMap := vMap ϕ; contn := c_hole x s' |} as ϕ'.
    remember {| vMap := update this (v_addr α) (ps ∘ vMap ϕ); contn := c_stmt s |} as ϕ''.
    exists (χ, ϕ'' :: ϕ' :: nil).
    apply (r_mth M ϕ nil χ x y ps (χ, ϕ :: nil) m zs α o s s' C ϕ' ϕ''); auto.
    apply int_x.
    crush.
  - subst χ0 ϕ0 ψ σ Σ0 χ1.
    exists (χ, {| vMap := update x v (vMap ϕ); contn := c_stmt s |} :: nil).
    apply (r_eAssgn M χ ϕ nil x e v s); auto.
    apply restricted_evaluation_implies_evaluation with (ϕΣ:=(χ', ϕ :: nil)) (Σ:=Σ); eauto.
  - inversion H2.
    inversion H3.
    inversion H4.
    simpl in *.
    inversion H20.
    inversion H27.
    subst; simpl in *.
    apply mapp_iff_vMap_Some in H34.
    rewrite H34 in Hthisϕ.
    inversion Hthisϕ.
    remember {| cname := C_this; flds := flds_this |} as o'.
    assert (o0 = o'). { eauto with loo_db. }
    subst α0 o0.
    rename χ1 into χ, χ3 into χ', ϕ0 into ϕ.
    remember (frm (vMap ϕ) (c_stmt s)) as ϕ'.
    remember (update α o' χ) as χ1.
    exists (χ1, ϕ' :: nil).
Admitted. *)

