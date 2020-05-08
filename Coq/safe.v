Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma linked_class :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             forall C Def, C <> ObjectName ->
                      M1 C = Some Def ->
                      M C = Some Def.
Proof.
  intros M1 M2 M Hlink;
    inversion Hlink;
    subst;
    intros;
    unfold extend;
    crush.
Qed.

Lemma substmt_trans :
  forall s2 s3, substmt s2 s3 ->
           forall s1, substmt s1 s2 ->
                 substmt s1 s3.
Proof.
  intros s2 s3 Hsub;
    induction Hsub;
    intros;
    auto.

  - apply sub_if1;
      eauto.

  - apply sub_if2;
      eauto.

  - apply sub_stmt1;
      eauto.

  - apply sub_stmt2;
      eauto.

Qed.

Hint Resolve substmt_trans : loo_db.

Lemma reduction_field_change :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ1 ϕ1 ψ1 χ2 ϕ2 ψ2,
               σ1 = (χ1, ϕ1 :: ψ1) ->
               σ2 = (χ2, ϕ2 :: ψ2) ->
               forall α o1 o2 f v1 v2,
                 mapp σ1 α = Some o1 ->
                 mapp σ2 α = Some o2 ->
                 flds o1 f = Some v1 ->
                 flds o2 f = Some v2 ->
                 v1 <> v2 ->
                 exists x y s C, contn ϕ1 = c_stmt ((x ◌ f) ≔ (r_ y) ;; s) /\
                            ⌊ x ⌋ σ1 ≜ (v_addr α) /\
                            classOf this σ1 C /\
                            classOf x σ1 C /\
                            ⌊ y ⌋ σ1 ≜ v2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    try solve [repeat simpl_crush;
               repeat map_rewrite;
               simpl in *;
               crush].

  - subst; repeat simpl_crush.
    destruct (eq_dec α α0);
      subst.
    + destruct (eq_dec f0 f);
        subst;
        eauto.
      * exists y, x, s, C;
          repeat split;
          eauto.
        repeat map_rewrite.
        rewrite H5 in H13;
          inversion H13;
          subst.
        assert (Htmp : o2 =
                       {| cname := cname o1;
                          flds := fun x : fld => if eqb x f then Some v else flds o1 x |});
          [crush|rewrite Htmp in H16; unfold flds in *].
        assert (Hflds : (let (_, flds) := o1 in flds) = (flds o1));
          [auto|rewrite Hflds in H16].
        eq_auto.
        crush.

      * repeat map_rewrite.
        rewrite H5 in H13;
          inversion H13;
          subst.
        assert (Htmp : o2 =
                       {| cname := cname o1;
                          flds := fun x : fld => if eqb x f then Some v else flds o1 x |});
          [crush|rewrite Htmp in H16; unfold flds in *].
        assert (Hflds : (let (_, flds) := o1 in flds) = (flds o1));
          [auto|rewrite Hflds in H16].
        eq_auto.
        crush.
    + repeat map_rewrite.
      crush.

  - subst; repeat simpl_crush.
    destruct (eq_dec α α0);
      subst.
    + eapply fresh_heap_some_contradiction; eauto.
    + repeat map_rewrite.
      crush.

Qed.

Lemma reductions_prop_change :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall P, ~ P σ1 ->
                            P σ2 ->
                            exists σ σ', M ∙ σ ⤳ σ' /\
                                    ~ P σ /\
                                    P σ' /\
                                    (reductions M σ1 σ \/ σ1 = σ) /\
                                    (reductions M σ' σ2 \/ σ2 = σ').
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.

  - repeat eexists;
      eauto.

  - destruct (excluded_middle (P σ2)) as [Hprop|Hprop].
    + destruct (IHHred P); auto;
        destruct_exists_loo;
        andDestruct.
      match goal with
      | [Ha : reductions ?M ?σ1 ?σ \/ ?σ1 = ?σ,
              Hb : reductions ?M ?σ' ?σ2 \/ ?σ2 = ?σ' |- _] =>
        destruct Ha, Hb
      end;
        subst;
        try solve [repeat eexists; eauto with loo_db].
    + repeat eexists; eauto.

Qed.

Check reduction_field_change.


Inductive stmt_in_method : mdl -> heap -> addr -> mth -> stmt -> Prop :=
| in_mth : forall χ α m o M C CDef zs sm s, χ α = Some o ->
                                       cname o = C ->
                                       M C = Some CDef ->
                                       c_meths CDef m = Some (zs, sm) ->
                                       substmt s sm ->
                                       stmt_in_method M χ α m s.

Inductive method_is_called : config -> var -> addr -> mth -> partial_map var value -> Prop :=
| meth_called : forall x y m β s α ϕ χ ψ, contn ϕ = c_stmt (s_meth x y m β ;; s) ->
                                     ⌊ y ⌋ (χ, ϕ :: ψ) ≜ (v_addr α) ->
                                     method_is_called (χ, ϕ::ψ) x α m (β ∘ (vMap ϕ)).

Hint Constructors method_is_called stmt_in_method : loo_db.

Lemma arising_frame_is_method_call_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall χ1 χ2 ϕ1 ϕ2 ψ1 ψ2,
                    σ1 = (χ1, ϕ1 :: ψ1) ->
                    σ2 = (χ2, ϕ2 :: ψ2) ->
                    length (snd σ1) < length (snd σ2) ->
                    (exists x α m β s, method_is_called σ1 x α m β /\
                                  contn ϕ2 = c_stmt s /\
                                  stmt_in_method M χ1 α m s).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    crush;
    repeat simpl_crush.

  exists x, α, m, (ps ∘ vMap ϕ1), s;
    repeat split;
    simpl in *;
    eauto with loo_db.
  eapply meth_called; eauto.

Qed.

(*Lemma arising_frame_is_method_call_reduction' :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ1 χ2 ψ1 ψ2,
               σ1 = (χ1, ψ1) ->
               σ2 = (χ2, ψ2) ->
               (forall ϕ1, In ϕ1 ψ1 ->
                      (exists ψ', ψ1 = ψ' ++ ϕ1 :: nil) \/
                      (exists α m β s, method_is_called σ1 α m β /\
                                  contn ϕ2 = c_stmt s /\
                                  stmt_in_method M χ1 α m s) \/
                      (exists χ ϕ ψ α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                        reductions M (χ, ϕ :: ψ) σ2 /\
                                        method_is_called (χ, ϕ :: ψ) α m β /\
                                        (contn ϕ2 = c_stmt s \/ exists x, contn ϕ2 = c_hole x s) /\
                                        stmt_in_method M χ α m s)) ->
               forall ϕ2, In ϕ2 ψ2 ->
                     (exists ψ', ψ2 = ψ' ++ ϕ2 :: nil) \/
                     (exists α m β s, method_is_called σ1 α m β /\
                                 contn ϕ2 = c_stmt s /\
                                 stmt_in_method M χ1 α m s) \/
                     (exists χ ϕ ψ α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                       reductions M (χ, ϕ :: ψ) σ2 /\
                                       method_is_called (χ, ϕ :: ψ) α m β /\
                                       (contn ϕ2 = c_stmt s \/ exists x, contn ϕ2 = c_hole x s) /\
                                       stmt_in_method M χ α m s).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    repeat simpl_crush.

  - admit.

Qed.*)

Lemma arising_frame_is_method_call_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 χ2 ϕ1 ψ2,
                    σ1 = (χ1, ϕ1 :: nil) ->
                    σ2 = (χ2, ψ2) ->
                    forall ϕ2, In ϕ2 ψ2 ->
                               (exists ψ', ψ2 = ψ' ++ ϕ2 :: nil) \/
                               (exists x α m β s, method_is_called σ1 x α m β /\
                                             contn ϕ2 = c_stmt s /\
                                             stmt_in_method M χ1 α m s) \/
                               (exists χ ϕ ψ x α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                                   reductions M (χ, ϕ :: ψ) σ2 /\
                                                   method_is_called (χ, ϕ :: ψ) x α m β /\
                                                   (contn ϕ2 = c_stmt s \/ exists y, contn ϕ2 = c_hole y s) /\
                                                   stmt_in_method M χ α m s).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst.

  - inversion H;
      subst;
      repeat simpl_crush;
      try solve [left;
                 match goal with
                 | [H : In ?ϕ (?ϕ' :: nil)|- _] =>
                   inversion H;
                   subst; [|crush]
                 end;
                 match goal with
                 | [|- exists ψ', ?ϕ2 :: nil = ψ' ++ ?ϕ2 :: nil ] =>
                   exists nil;
                   simpl;
                   eauto
                 end].

    + inversion H2;
        subst;
        [right; left|left].
      * repeat eexists;
          eauto; [|crush].
        inversion H6;
          subst;
          simpl in *;
          simpl_crush;
          eauto.
      * inversion H0; subst;
          [|crush].
        match goal with
        | [|- exists ψ', ?ϕ1 :: ?ϕ2 :: nil = ψ' ++ ?ϕ2 :: nil ] =>
          exists (ϕ1 :: nil);
            simpl;
            eauto
        end.

  - admit.
Admitted.

(*Lemma arising_frame_is_method_call_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             forall χ1 χ2 ϕ1 ϕ2 ψ1 ψ2,
               σ1 = (χ1, ϕ1 :: ψ1) ->
               σ2 = (χ2, ϕ2 :: ψ2) ->
               length (snd σ1) < length (snd σ2) ->
               (exists α m β s, method_is_called σ1 α m β /\
                           contn ϕ2 = c_stmt s /\
                           stmt_in_method M χ1 α m s) \/
               (exists χ ϕ ψ α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                 method_is_called (χ, ϕ :: ψ) α m β /\
                                 contn ϕ2 = c_stmt s /\
                                 stmt_in_method M χ α m s).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    repeat simpl_crush;
    simpl in *.

  - left; eapply arising_frame_is_method_call_reduction; simpl; eauto.

  - inversion H; subst;
      repeat simpl_crush.
    + simpl in *.
      right.
      repeat eexists; eauto with loo_db.
      inversion H7;
        subst;
        simpl in *;
        simpl_crush;
        auto.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 ψ2) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H7;
          inversion H7;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H7;
          inversion H7;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 ψ2) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α0, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H6;
          inversion H6;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α0, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        crush.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H6;
          inversion H6;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ ϕ1 ϕ ψ1 ψ) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α0, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H1;
          inversion H1;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ0, ϕ0, ψ0, α0, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H1;
          inversion H1;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ ϕ1 ϕ ψ1 ψ) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α0, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H3;
          inversion H3;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ0, ϕ0, ψ0, α0, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H3;
          inversion H3;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 ψ2) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α, m, β, s1;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H5;
          inversion H5;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α, m, β, s1;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H5;
          inversion H5;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 ψ2) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α, m, β, s2;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H5;
          inversion H5;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α, m, β, s2;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H5;
          inversion H5;
          subst;
          crush.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 (ϕ'::ψ2)) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α0, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha0 in H5;
          inversion H5;
          subst;
          crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α0, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H1;
          inversion H1;
          subst;
          crush.
        crush.

    + simpl in *.
      destruct (IHHred χ1 χ2 ϕ1 ϕ ψ1 (ϕ'::ψ2)) as [Ha|Ha];
        auto.
      * left; auto.
        repeat destruct_exists_loo;
          andDestruct.
        exists α0, m, β, s;
          repeat split;
          auto.
        inversion Hb0;
          subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H1;
          inversion H1;
          subst;
          crush.
        crush.

      * right.
        repeat destruct_exists_loo;
          andDestruct.
        exists χ, ϕ0, ψ, α0, m, β, s;
          repeat split;
          auto.
        inversion Hb; subst.
        eapply in_mth; eauto.
        eapply substmt_trans;
          eauto.
        rewrite Ha1 in H1;
          inversion H1;
          subst;
          crush.
        crush.

Qed.*)

Lemma bottom_frame_remains_in_stack_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall χ1 ϕ1 ψ1,
                    σ1 = (χ1, ψ1 ++ ϕ1 :: nil) ->
                    exists ψ ϕ, (snd σ2) = (ψ ++ ϕ :: nil) /\
                                vMap ϕ this = vMap ϕ1 this.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    simpl in *;
    repeat simpl_crush;
    simpl;
    try solve [repeat match goal with
                      | [H : ?ϕ1 :: ?ψ1 = ?ψ2 ++ ?ϕ2 :: nil |- _] =>
                        let ϕ := fresh "ϕ" in
                        let ψ := fresh "ψ" in
                        destruct ψ2 as [|ϕ ψ]; simpl in H; inversion H; subst
                      end;
               match goal with
               | [|- exists ψ ϕ, ?ϕ' :: nil = ψ ++ ϕ :: nil /\ _] =>
                 exists nil, ϕ'
               | [|- exists ψ ϕ, ?ϕ'' :: ?ψ' ++ ?ϕ' :: nil = ψ ++ ϕ :: nil /\ _] =>
                 exists (ϕ''::ψ'), ϕ'
               | [|- exists ψ ϕ, ?ϕ'' :: ?ϕ' :: nil = ψ ++ ϕ :: nil /\ _] =>
                 exists (ϕ'' :: nil), ϕ'
               | [|- exists ψ ϕ, ?ϕ'' :: ?ϕ' :: ?ψ' ++ ?ϕ''' :: nil = ψ ++ ϕ :: nil /\ _] =>
                 exists (ϕ'' :: ϕ' :: ψ'), ϕ'''
               | [|- exists ψ ϕ, ?ϕ'' :: ?ϕ' :: ?ψ' = ψ ++ ϕ :: nil /\ _] =>
                 exists (ϕ''::ψ'), ϕ'
               end;
               split;
               auto;
               simpl; repeat map_rewrite].
Qed.

Lemma bottom_frame_remains_in_stack_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 ϕ1 ψ1,
                    σ1 = (χ1, ψ1 ++ ϕ1 :: nil) ->
                    exists ψ ϕ, (snd σ2) = (ψ ++ ϕ :: nil) /\
                                vMap ϕ this = vMap ϕ1 this.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst.

  - eapply bottom_frame_remains_in_stack_reduction; eauto.

  - destruct (IHHred χ1 ϕ1 ψ1); auto;
      destruct_exists_loo;
      andDestruct;
      subst.

    destruct σ2 as [χ ψ];
      simpl in *;
      subst.
    rewrite <- Hb.
    apply (bottom_frame_remains_in_stack_reduction M (χ, x++ϕ :: nil)) with (χ1:=χ)(ψ1:=x);
      auto.
Qed.

Lemma different_this_implies_larger_stack_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  σ_wf σ1 ->
                  forall χ1 ϕ1,
                    σ1 = (χ1, ϕ1 :: nil) ->
                    forall v1 v2, ⌊ this ⌋ σ1 ≜ v1 ->
                                  ⌊ this ⌋ σ2 ≜ v2 ->
                                  (length (snd σ1) < length (snd σ2)) \/
                                  (v1 = v2 /\ length (snd σ1) = length (snd σ2)).
Proof.
  intros.
  destruct (bottom_frame_remains_in_stack_reductions M σ1 σ2 H χ1 ϕ1 nil)
    as [ψ];
    auto;
    destruct_exists_loo;
    andDestruct.
  destruct σ2 as [χ2 ψ2];
    simpl in *;
    subst;
    simpl in *.

  destruct ψ as [|ϕ' ψ'];
    simpl in *.
  - match goal with
    | [Ha : ⌊ ?x ⌋ ?σ1 ≜ _,
            Hb : ⌊ ?x ⌋ ?σ2 ≜ _ |- _] =>
      inversion Ha;
        inversion Hb;
        subst
    end;
      simpl in *;
      repeat simpl_crush.
    crush.

  - simpl;
      rewrite app_length;
      crush.
Qed.

Lemma reduction_implies_non_empty_stack_1 :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  exists χ1 ϕ1 ψ1, σ1 = (χ1, ϕ1 :: ψ1).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Lemma reduction_implies_non_empty_stack_2 :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  exists χ2 ϕ2 ψ2, σ2 = (χ2, ϕ2 :: ψ2).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto.
Qed.

Lemma reduction_preserves_heap_locations :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall α (o : obj), mapp σ1 α = Some o ->
                                      exists o', mapp σ2 α = Some o'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto;
    subst;
    try solve [repeat eexists;
               crush;
               eauto];
    try solve [destruct (eq_dec α α0);
               subst;
               repeat map_rewrite;
               eauto].
Qed.

Lemma reductions_preserves_heap_locations_classes :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall α (o : obj), mapp σ1 α = Some o ->
                                      exists o', mapp σ2 α = Some o' /\
                                                 cname o' = cname o.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros.

  - eapply reduction_preserves_addr_classes;
      eauto.

  - specialize (IHHred α o);
      auto_specialize;
      destruct_exists_loo;
      andDestruct.
    apply reduction_preserves_addr_classes
      with (α:=α)(o1:=o0) in H;
      eauto;
      repeat destruct_exists_loo;
      andDestruct.
    eexists; split; eauto; crush.
Qed.

Lemma reduction_preserves_fields :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall α o f v, mapp σ1 α = Some o ->
                                  flds o f = Some v ->
                                  exists o' v', mapp σ2 α = Some o' /\
                                                flds o' f = Some v'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    eauto;
    try solve [repeat eexists; crush; eauto].

  - destruct (eq_dec α α0);
      subst;
      destruct (eq_dec f0 f);
      subst;
      repeat map_rewrite;
      eauto.
    + repeat eexists;
        eauto;
        unfold flds;
        eq_auto.
    + match goal with
      | [|- exists o' _, Some ?o = Some o' /\ _ ] =>
        exists o
      end.
      exists v0;
        split;
        eauto;
        unfold flds;
        eq_auto.
      match goal with
      | [Ha : ?m ?a = _,
              Hb : ?m ?a = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst
      end.
      destruct o0;
        auto.

  - subst.
    destruct (eq_dec α α0);
      subst;
      repeat map_rewrite;
      eauto.
    eapply fresh_heap_some_contradiction; eauto.
Qed.

Lemma reductions_preserves_fields :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall α o f v, mapp σ1 α = Some o ->
                                  flds o f = Some v ->
                                  exists o' v', mapp σ2 α = Some o' /\
                                                flds o' f = Some v'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros.

  - eapply reduction_preserves_fields; eauto.

  - specialize (IHHred α o f v);
      repeat auto_specialize;
      repeat destruct_exists_loo;
      andDestruct.
    eapply reduction_preserves_fields;
      eauto.
Qed.

Lemma reductions_field_change :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 ϕ1 ψ1 χ2 ϕ2 ψ2,
                    σ1 = (χ1, ϕ1 :: ψ1) ->
                    σ2 = (χ2, ϕ2 :: ψ2) ->
                    forall α o1 o2 f v1 v2,
                      mapp σ1 α = Some o1 ->
                      mapp σ2 α = Some o2 ->
                      flds o1 f = Some v1 ->
                      flds o2 f = Some v2 ->
                      v1 <> v2 ->
                      exists χ ϕ ψ, (reductions M σ1 (χ, ϕ :: ψ) \/ σ1 = (χ, ϕ :: ψ)) /\
                                    exists  x y s C, contn ϕ = c_stmt ((x ◌ f) ≔ (r_ y) ;; s) /\
                                                     ⌊ x ⌋ (χ, ϕ :: ψ) ≜ (v_addr α) /\
                                                     classOf this (χ, ϕ :: ψ) C /\
                                                     classOf x (χ, ϕ :: ψ) C /\
                                                     ⌊ y ⌋ (χ, ϕ :: ψ) ≜ v2.
Proof.
  intros.
  destruct (reductions_prop_change M σ1 σ2)
    with (P:= fun σ : config => forall o, mapp σ α = Some o -> flds o f = Some v2);
    auto.
  - intros Hcontra;
      specialize (Hcontra o1);
      auto_specialize;
      crush.

  - intros;
      crush.

  - destruct_exists_loo;
      andDestruct.
    destruct x as [χa ψa];
      destruct σ as [χb ψb].
    edestruct (reduction_implies_non_empty_stack_1 M (χa, ψa));
      eauto.
    edestruct (reduction_implies_non_empty_stack_2 M (χa, ψa) (χb, ψb));
      eauto;
      repeat destruct_exists_loo;
      repeat simpl_crush.
    exists x, ϕ0, ψ0;
      split;
      auto.

    match goal with
    | [ Ha : reductions _ _ _ \/ _,
             Hb : reductions _ _ _ \/ _ |- _] =>
      destruct Ha, Hb
    end.
    
    + destruct (reductions_preserves_fields M (χ1, ϕ1 :: ψ1) (x, ϕ0 :: ψ0))
        with (α:=α)(o:=o1)(f:=f)(v:=v1);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      destruct (reduction_preserves_fields M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (α:=α)(o:=x1)(f:=f)(v:=v);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      eapply (reduction_field_change M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (χ1:=x)(ψ1:=ψ0)(χ2:=x0);
        eauto.
      intros Hcontra;
        subst.
      contradiction Ha0;
        intros.
      repeat map_rewrite.
      rewrite Ha2 in H7;
        inversion H7;
        subst;
        auto.

    + repeat simpl_crush.
      destruct (reductions_preserves_fields M (χ1, ϕ1 :: ψ1) (x, ϕ0 :: ψ0))
        with (α:=α)(o:=o1)(f:=f)(v:=v1);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      destruct (reduction_preserves_fields M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (α:=α)(o:=x1)(f:=f)(v:=v);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      eapply (reduction_field_change M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (χ1:=x)(ψ1:=ψ0)(χ2:=x0);
        eauto.
      intros Hcontra;
        subst.
      contradiction Ha0;
        intros.
      repeat map_rewrite.
      rewrite Ha2 in H1;
        inversion H1;
        subst;
        auto.

    + repeat simpl_crush.
      destruct (reduction_preserves_fields M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (α:=α)(o:=o1)(f:=f)(v:=v1);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      destruct (reductions_preserves_fields M (x0, ϕ :: ψ) (χ2, ϕ2 :: ψ2))
        with (α:=α)(o:=x1)(f:=f)(v:=v);
        eauto with loo_db;
        destruct_exists_loo;
        andDestruct.
      eapply (reduction_field_change M (x, ϕ0 :: ψ0) (x0, ϕ :: ψ))
        with (χ1:=x)(ψ1:=ψ0)(χ2:=x0);
        eauto.

    + repeat simpl_crush.
      eapply reduction_field_change; eauto.

Qed.

Lemma frame_arising_from_single_frame_is_method_call_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 ϕ1,
                    σ1 = (χ1, ϕ1 :: nil) ->
                    mapp σ1 this <> mapp σ2 this ->
                    forall χ2 ϕ2 ψ2, σ2 = (χ2, ϕ2 :: ψ2) ->
                                (exists x α m β s, method_is_called σ1 x α m β /\
                                              contn ϕ2 = c_stmt s /\
                                              stmt_in_method M χ1 α m s) \/
                                (exists χ ϕ ψ x α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                                    method_is_called (χ, ϕ :: ψ) x α m β /\
                                                    contn ϕ2 = c_stmt s /\
                                                    stmt_in_method M χ α m s).
Proof.
  intros.
(*  destruct (arising_frame_is_method_call_reductions M σ1 σ2)
    with
      (χ1:=χ1)(χ2:=χ2)(ϕ1:=ϕ1)(ϕ2:=ϕ2)(ψ1:=@nil frame)(ψ2:=ψ2);
    simpl;
    auto.

  let ψ := fresh "ψ" in
  let ϕ := fresh "ϕ" in
  edestruct (bottom_frame_remains_in_stack_reductions M σ1 σ2)
    with
      (ψ1:=@nil frame) as [ψ Htmp];
    eauto;
    destruct Htmp as [ϕ];
    andDestruct;
    subst;
    simpl in *.

  let ϕ' := fresh "ϕ" in
  let ψ' := fresh "ψ" in
  destruct ψ as [|ϕ' ψ'];
    simpl in *;
    simpl_crush;
    repeat map_rewrite;
    try rewrite app_length; crush.*)
Admitted.

Lemma reductions_field_change_not_this :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 ϕ1 ψ1 χ2 ϕ2 ψ2,
                    σ1 = (χ1, ϕ1 :: ψ1) ->
                    σ2 = (χ2, ϕ2 :: ψ2) ->
                    forall α o1 o2 f v1 v2,
                      mapp σ1 α = Some o1 ->
                      mapp σ2 α = Some o2 ->
                      flds o1 f = Some v1 ->
                      flds o2 f = Some v2 ->
                      v1 <> v2 ->
                      (forall C, classOf this σ1 C ->
                                 cname o1 <> C) ->
                      exists χ ϕ ψ x y s C, reductions M σ1 (χ, ϕ :: ψ) /\
                                            contn ϕ = c_stmt ((x ◌ f) ≔ (r_ y) ;; s) /\
                                            ⌊ x ⌋ (χ, ϕ :: ψ) ≜ (v_addr α) /\
                                            classOf this (χ, ϕ :: ψ) C /\
                                            classOf x (χ, ϕ :: ψ) C /\
                                            ⌊ y ⌋ (χ, ϕ :: ψ) ≜ v2.
Proof.
  intros.
  let χ := fresh "χ" in
  edestruct (reductions_field_change M σ1 σ2)
    as [χ];
    eauto;
    repeat destruct_exists_loo;
    andDestruct;
    repeat destruct_exists_loo;
    andDestruct.
  exists χ, ϕ, ψ, x, x0, s, C;
    repeat split;
    auto.
  destruct Ha;
    subst;
    auto;
    simpl_crush.
  specialize (H7 C);
    auto_specialize.
  repeat map_rewrite.
  inversion Ha3;
    subst;
    simpl in *.
  interpretation_rewrite.
  inversion H0;
    subst.
  rewrite H2 in H8;
    inversion H8;
    subst;
    crush.
Qed.

Definition is_internal (M1 M2 : mdl)(σ : config)(α : addr) :=
  (exists o CDef, mapp σ α = Some o /\
             M1 (cname o) = Some CDef).

Definition is_external (M1 M2 : mdl)(σ : config)(α : addr) :=
  (exists o, mapp σ α = Some o /\
        M1 (cname o) = None).

Definition is_internal_self (M1 M2 : mdl)(σ : config) :=
  (exists α, mapp σ this = Some (v_addr α) /\
        is_internal M1 M2 σ α).

Definition is_external_self (M1 M2 : mdl)(σ : config) :=
  (exists α, mapp σ this = Some (v_addr α) /\
        is_external M1 M2 σ α).

Lemma pair_reductions_is_external_1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 is_external_self M1 M2 σ1.
Proof.
Admitted.

Lemma pair_reductions_is_external_2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 is_external_self M1 M2 σ2.
Proof.
Admitted.

Lemma frame_arising_from_single_frame_external_internal_is_method_call_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
                  forall χ1 ϕ1,
                    σ1 = (χ1, ϕ1 :: nil) ->
                    forall M1 M2,
                      M1 ⋄ M2 ≜ M ->
                      is_external_self M1 M2 σ1 ->
                      is_internal_self M1 M2 σ2 ->
                      forall χ2 ϕ2 ψ2, σ2 = (χ2, ϕ2 :: ψ2) ->
                                  (exists x α m β s, method_is_called σ1 x α m β /\
                                                contn ϕ2 = c_stmt s /\
                                                stmt_in_method M χ1 α m s) \/
                                  (exists χ ϕ ψ x α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                                      method_is_called (χ, ϕ :: ψ) x α m β /\
                                                      contn ϕ2 = c_stmt s /\
                                                      stmt_in_method M χ α m s).
Proof.
  intros.
  eapply frame_arising_from_single_frame_is_method_call_reductions;
    eauto.
  unfold is_external_self, is_external, is_internal_self, is_internal in *;
    repeat destruct_exists_loo;
    andDestruct;
    repeat destruct_exists_loo;
    andDestruct;
    subst;
    repeat map_rewrite.
  intros Hcontra;
    rewrite Hcontra in *.
  rewrite Ha0 in Ha;
    inversion Ha;
    subst.

  let o' := fresh "o" in
  destruct (reductions_preserves_heap_locations_classes M (χ1, ϕ1::nil)(χ2, ϕ2 :: ψ2))
    with (α:=α)(o:=o0) as [o'];
    auto;
    andDestruct.
  repeat map_rewrite.
  rewrite Ha1 in Ha3;
    inversion Ha3;
    subst.
  rewrite Hb1 in *;
    crush.
Qed.

Lemma is_external_self_implies_not_is_internal :
  forall M1 M2 σ, is_external_self M1 M2 σ ->
                  ~ is_internal_self M1 M2 σ.
Proof.
  intros;
    unfold is_internal_self, is_external_self, is_internal, is_external in *;
    intro Hcontra;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Lemma is_internal_self_implies_not_is_external :
  forall M1 M2 σ, is_internal_self M1 M2 σ ->
                  ~ is_external_self M1 M2 σ.
Proof.
  intros;
    intro Hcontra;
    unfold is_internal_self, is_external_self, is_internal, is_external in *;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Lemma is_external_implies_not_is_internal :
  forall M1 M2 σ α, is_external M1 M2 σ α ->
               ~ is_internal M1 M2 σ α.
Proof.
  intros;
    unfold is_internal, is_external in *;
    intro Hcontra;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Lemma is_internal_implies_not_is_external :
  forall M1 M2 σ α, is_internal M1 M2 σ α ->
               ~ is_external M1 M2 σ α.
Proof.
  intros;
    intro Hcontra;
    unfold is_internal_self, is_external_self, is_internal, is_external in *;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Inductive stack_trace : mdl -> mdl -> config -> Prop :=
| trace_initial : forall M1 M2 χ ϕ x s, is_external_self M1 M2 (χ, ϕ :: nil) ->
                                        classOf this (χ, ϕ :: nil) ObjectName ->
                                        contn ϕ = c_hole x s ->
                                        stack_trace M1 M2 (χ, ϕ :: nil)
| trace_internal : forall M1 M2 χ ϕ ψ x s C CDef m zs body,
    stack_trace M1 M2 (χ, ψ) ->
    contn ϕ = c_hole x s ->
    classOf this (χ, ϕ :: ψ) C ->
    M1 C = Some CDef ->
    M2 C = None ->
    c_meths CDef m = Some (zs, body) ->
    substmt s body ->
    stack_trace M1 M2 (χ, ϕ :: ψ)
| trace_external : forall M1 M2 χ ϕ ϕ' ψ x s C CDef m zs body,
    stack_trace M1 M2 (χ, ψ) ->
    contn ϕ = c_hole x s ->
    classOf this (χ, ϕ :: ϕ' :: ψ) C ->
    M1 C = None ->
    M2 C = Some CDef ->
    c_meths CDef m = Some (zs, body) ->
    substmt s body ->
    stack_trace M1 M2 (χ, ϕ :: ϕ' :: ψ).

Inductive valid_stack_trace : mdl -> mdl -> config -> Prop :=
| int_head : forall M1 M2 χ ϕ ψ s C CDef m zs body,
    stack_trace M1 M2 (χ, ψ) ->
    contn ϕ = c_stmt s ->
    classOf this (χ, ϕ :: ψ) C ->
    M1 C = Some CDef ->
    M2 C = None ->
    c_meths CDef m = Some (zs, body) ->
    substmt s body ->
    valid_stack_trace M1 M2 (χ, ϕ :: ψ)
| ext_head : forall M1 M2 χ ϕ ψ s C CDef m zs body,
    stack_trace M1 M2 (χ, ψ) ->
    contn ϕ = c_stmt s ->
    classOf this (χ, ϕ :: ψ) C ->
    M1 C = None ->
    M2 C = Some CDef ->
    c_meths CDef m = Some (zs, body) ->
    substmt s body ->
    valid_stack_trace M1 M2 (χ, ϕ :: ψ).

Hint Constructors valid_stack_trace stack_trace : loo_db.

Lemma valid_program_trace_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall M1 M2,
                    M_wf M1 ->
                    M1 ⋄ M2 ≜ M ->
                    valid_stack_trace M1 M2 σ1 ->
                    valid_stack_trace M1 M2 σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst.

  - admit.

  - match goal with
    | [H : valid_stack_trace _ _ _ |- _] =>
      inversion H;
        subst
    end;
      match goal with
      | [Ha : ?M1 ?C = Some ?CDef,
              Hb : ?M2 ?C = None,
                   Hc : c_meths ?CDef ?m = Some (?zs, ?body),
                        Hd : contn ?ϕ = c_stmt (_ ;; ?s)
         |- valid_stack_trace ?M1 ?M2 (_, _)] =>
        eapply (int_head M1 M2 χ) with (C:=C)(CDef:=CDef)(m:=m)(s:=s)(zs:=zs)(body:=body);
          eauto
      | [Ha : ?M1 ?C = None,
              Hb : ?M2 ?C = Some ?CDef,
                   Hc : c_meths ?CDef ?m = Some (?zs, ?body),
                        Hd : contn ?ϕ = c_stmt (_ ;; ?s)
         |- valid_stack_trace ?M1 ?M2 (_, _)] =>
        eapply (ext_head M1 M2 χ) with (C:=C)(CDef:=CDef)(m:=m)(s:=s)(zs:=zs)(body:=body);
          eauto
      end;
      try solve [match goal with
                 | [Hcls : classOf _ _ _ |- _] =>
                   inversion Hcls;
                   subst;
                   simpl in *
                 end;
                 eapply cls_of; simpl; eauto;
                 match goal with
                 | [Hint : interpret_x _ _ _ |- _] =>
                   inversion Hint;
                   subst;
                   simpl in *;
                   repeat simpl_crush
                 end;
                 eapply int_x; simpl; eauto; simpl;
                 repeat map_rewrite;
                 auto];
      try solve [ match goal with
                  | [Ha : contn ?ϕ = _,
                          Hb : contn ?ϕ = _,
                               Hsub : substmt _ _ |- _] =>
                    rewrite Ha in Hb;
                    inversion Hb;
                    subst
                  end;
                  apply substmt_trans with (s2:= (x ≔′ e) ;; s);
                  crush].

  - match goal with
    | [H : valid_stack_trace _ _ _ |- _] =>
      inversion H;
        subst
    end;
      match goal with
      | [Ha : ?M1 ?C' = Some ?CDef,
              Hb : ?M2 ?C' = None,
                   Hc : c_meths ?CDef ?m = Some (?zs, ?body),
                        Hd : contn ?ϕ = c_stmt (_ ;; ?s)
         |- valid_stack_trace ?M1 ?M2 (_, _)] =>
        eapply (int_head M1 M2 χ) with (C:=C')(CDef:=CDef)(m:=m)(s:=s)(zs:=zs)(body:=body);
          eauto
      | [Ha : ?M1 ?C' = None,
              Hb : ?M2 ?C' = Some ?CDef,
                   Hc : c_meths ?CDef ?m = Some (?zs, ?body),
                        Hd : contn ?ϕ = c_stmt (_ ;; ?s)
         |- valid_stack_trace ?M1 ?M2 (_, _)] =>
        eapply (ext_head M1 M2 χ) with (C:=C')(CDef:=CDef)(m:=m)(s:=s)(zs:=zs)(body:=body);
          eauto
      end;
      
      try solve [match goal with
                 | [Hcls : classOf _ _ _ |- _] =>
                   inversion Hcls;
                   subst;
                   simpl in *
                 end;
                 eapply cls_of; simpl; eauto;
                 match goal with
                 | [Hint : interpret_x _ _ _ |- _] =>
                   inversion Hint;
                   subst;
                   simpl in *;
                   repeat simpl_crush
                 end;
                 eapply int_x; simpl; eauto; simpl;
                 repeat map_rewrite;
                 auto];
      try solve [ match goal with
                  | [Ha : contn ?ϕ = _,
                          Hb : contn ?ϕ = _,
                               Hsub : substmt _ _ |- _] =>
                    rewrite Ha in Hb;
                    inversion Hb;
                    subst
                  end;
                  apply substmt_trans with (s2:= ((r_ x) ≔ (y ◌ f)) ;; s);
                  crush].

  - (*match goal with
    | [H : valid_stack_trace _ _ _ |- _] =>
      inversion H;
        subst
    end;
      match goal with
      | [Ha : ?Ma ?C' = Some ?CDef',
              Hb : ?Mb ?C' = None,
                   Hc : c_meths ?CDef' ?m' = Some (?zs', ?body'),
                        Hd : contn ?ϕ' = c_stmt (_ ;; ?s')
         |- valid_stack_trace ?Ma ?Mb (?χ', _)] =>
        eapply (int_head Ma Mb χ') with (C:=C')(CDef:=CDef')(m:=m')(s:=s')(zs:=zs')(body:=body');
          eauto
      | [Ha : ?Ma ?C' = None,
              Hb : ?Mb ?C' = Some ?CDef',
                   Hc : c_meths ?CDef' ?m' = Some (?zs', ?body'),
                        Hd : contn ?ϕ' = c_stmt (_ ;; ?s')
         |- valid_stack_trace ?Ma ?Mb (?χ', _)] =>
        eapply (ext_head Ma Mb χ') with (C:=C')(CDef:=CDef')(m:=m')(s:=s')(zs:=zs')(body:=body');
          eauto
      end.*)
    admit.

  - admit.

  - 


Admitted.

Lemma reduction_internal_external :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  M_wf M ->
                  forall χ1 ϕ1 ψ1 χ2 ϕ2 ψ2, σ1 = (χ1, ϕ1 :: ψ1) ->
                                            σ2 = (χ2, ϕ2 :: ψ2) ->
                                            forall M1 M2, M1 ⋄ M2 ≜ M ->
                                                          is_external_self M1 M2 σ1 ->
                                                          (is_external_self M1 M2 σ2 \/
                                                           (is_internal_self M1 M2 σ2 /\
                                                            exists C CDef m zs s s', classOf this σ2 C /\
                                                                                     M1 C = Some CDef /\
                                                                                     c_meths CDef m = Some (zs, s) /\
                                                                                     contn ϕ2 = c_stmt s' /\
                                                                                     substmt s' s)).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    repeat simpl_crush;
    try solve [left;
               unfold is_external;
               repeat (map_rewrite; simpl)];
    try solve [crush; eauto].

  - (*destruct (partial_map_dec (cname o) M1);
      [repeat destruct_exists_loo; right; left|left].
    + split; [unfold is_internal|].
      * repeat map_rewrite;
          simpl;
          repeat eexists; eauto.
      * exists (cname o), C, m, zs, s, s;
          repeat split;
          auto.
        ** eapply cls_of; eauto.
           eapply int_x; simpl; eauto.
        ** inversion H12;
             subst.
           repeat map_rewrite.
           unfold extend in H4;
             rewrite H0 in H4;
             inversion H4;
             subst;
             auto.
        ** apply sub_refl.

    + unfold is_external; eauto;
        repeat map_rewrite;
        simpl.
      repeat eexists; eauto.

  - subst;
      repeat simpl_crush.
    left;
      unfold is_external.
    exists α, {| cname := cname o; flds := update f v (flds o); meths := meths o |}; simpl;
      repeat split;
      repeat map_rewrite;
      auto.
    
    
    
    repeat (map_rewrite; simpl);
      split;
      auto.
      simpl.
      repeat (map_rewrite; simpl).
      subst.*)

    
    
Admitted.

Definition meth_func :=
  fun (M : mdl)(x : var)(α : addr)(m : mth)(β : partial_map var var)(σ : config) =>
    let (χ, ψ) := σ in
    match ψ with
    | ϕ :: ψ' =>
      let c := contn ϕ in
      let β' := vMap ϕ in
      match c with
      | c_stmt (s_meth _ _ _ _ ;; s') =>
        match χ α with
        | Some o =>
          match M (cname o) with
          | Some CDef =>
            match (c_meths CDef) m with
            | Some (zs, body) =>
              Some (χ, (frm (update this (v_addr α) (β ∘ β')) (c_stmt body))
                         :: (frm β' (c_hole x s'))
                         :: ψ')
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

Definition assgn_func :=
  fun (x : var)(v : value)(σ : config) =>
    let (χ, ψ) := σ in
    match ψ with
    | ϕ :: ψ' =>
      let c := contn ϕ in
      let β := vMap ϕ in
      match c with
      | c_stmt s =>
        match s with
        | s_asgn _ _ ;; s => Some (χ, (frm (update x v β) (c_stmt s)) :: ψ')
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

Definition new_func :=
  fun (x : var)(o : obj)(α : addr)(σ : config) =>
    let (χ, ψ) := σ in
    match ψ with
    | ϕ :: ψ' =>
      let c := contn ϕ in
      let β := vMap ϕ in
      match c with
      | c_stmt s =>
        match s with
        | s_new _ _ _ ;; s => Some (update α o χ, (frm (update x (v_addr α) β) (c_stmt s)) :: ψ')
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

Definition if_func : value -> config -> option config :=
  fun (v : value)(σ : config) =>
    let (χ, ψ) := σ in
    match ψ with
    | ϕ :: ψ' =>
      let c := contn ϕ in
      let β := vMap ϕ in
      match c with
      | c_stmt s =>
        match s with
        | s_if _ s1 s2 ;; s =>
          match v with
          | v_true => Some (χ, frm β (c_stmt (s1 ;; s)) :: ψ')
          | v_false => Some (χ, frm β (c_stmt (s2 ;; s)) :: ψ')
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

Definition ret_func :=
  fun (v : value)(σ : config) =>
    let (χ, ψ) := σ in
    match ψ with
    | ϕ1 :: ϕ2 :: ψ' =>
      let c1 := contn ϕ1 in
      let c2 := contn ϕ2 in
      let β := vMap ϕ2 in
      match c2 with
      | c_hole x s =>
        match c1 with
        | c_stmt (s_rtrn _) =>
          Some (χ, frm (update x v β) (c_stmt s))
        | c_stmt ((s_rtrn _) ;; _) =>
          Some (χ, frm (update x v β) (c_stmt s))
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.


Lemma reduction_function :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  exists f, f M σ1 = σ2.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    subst;
    match goal with
    | [|- exists f, f _ _ = ?σ] =>
      exists (fun _ _ => σ)
    end;
    auto.

Qed.



Definition internal_obj (M1 M2 : mdl)(o : obj) : Prop :=
  exists CDef, M1 (cname o) = CDef.

Definition external_obj (M1 M2 : mdl)(o : obj) : Prop :=
  exists CDef, M2 (cname o) = CDef.

Definition internal_addr (M1 M2 : mdl)(σ : config)(α : addr) : Prop :=
  exists o, mapp σ α = Some o ->
            internal_obj M1 M2 o.

Definition external_addr (M1 M2 : mdl)(σ : config)(α : addr) : Prop :=
  exists o, mapp σ α = Some o ->
            external_obj M1 M2 o.

Definition no_external_calls (M1 M2 : mdl)(m : mth) : Prop :=
  forall σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                forall σ0 α1 α2  β, M1 ⦂ M2 ◎ σ0 … σ1 ⊨ (α1 calls α2 ▸ m ⟨ β ⟩) ->
                                    exists χ1 ϕ1 ψ1 χ2 ϕ2 ψ2 s x y β',
                                      σ1 = (χ1, ϕ1 :: ψ1) /\
                                      σ2 = (χ2, ϕ2 :: ψ2) /\
                                      length ψ1 = length ψ2 /\
                                      vMap ϕ1 this = vMap ϕ2 this /\
                                      contn ϕ1 = c_stmt (s_meth x y m β' ;; s) /\
                                      contn ϕ2 = c_stmt s.

Definition classic_spec (M1 M2 : mdl)(α1 α2 : addr)(m : mth)(β : partial_map var a_var)(A1 A2 : asrt) :=
  forall σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                (length (snd σ1)) = length (snd σ2) ->
                forall σ0, M1 ⦂ M2 ◎ σ0 … σ1 ⊨ ((a_ α1) calls (a_ α2) ▸ m ⟨ β ⟩) ->
                           M1 ⦂ M2 ◎ σ0 … σ1 ⊨ A1 ->
                           M1 ⦂ M2 ◎ σ0 … σ2 ⊨ A2.

Definition classic_spec_prop (M1 M2 : mdl)(C : cls)(m : mth)(P Q : mdl -> mdl -> config -> Prop) :=
  forall σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                (length (snd σ1)) = length (snd σ2) ->
                (exists CDef body, M1 C = Some CDef /\
                                   c_meths CDef m = body) ->
                forall σ0 α1 α2 β o, M1 ⦂ M2 ◎ σ0 … σ1 ⊨ ((a_ α1) calls (a_ α2) ▸ m ⟨ β ⟩) ->
                                     mapp σ1 α1 = Some o ->
                                     cname o = C ->
                                     P M1 M2 σ1 ->
                                     Q M1 M2 σ2.

Inductive reductions_alt : mdl -> mdl -> config -> config -> Prop :=
| ra_single : forall M1 M2 M σ1 σ2, M1 ⋄ M2 ≜ M ->
                                    M ∙ σ1 ⤳ σ2 ->
                                    is_internal_self M1 M2 σ1 ->
                                    is_external_self M1 M2 σ2 ->
                                    reductions_alt M1 M2 σ1 σ2
| ra_trans : forall M1 M2 M σ1 σ2 σ, M1 ⋄ M2 ≜ M ->
                                     M ∙ σ1 ⤳ σ2 ->
                                     is_internal_self M1 M2 σ1 ->
                                     reductions_alt M1 M2 σ2 σ ->
                                     reductions_alt M1 M2 σ1 σ.

Inductive pair_reduction_alt : mdl -> mdl -> config -> config -> Prop :=
| pra : forall M1 M2 M σ1 σ σ2, M1 ⋄ M2 ≜ M ->
                           M ∙ σ1 ⤳ σ ->
                           is_external_self M1 M2 σ1 ->
                           reductions_alt M1 M2 σ σ2 ->
                           pair_reduction_alt M1 M2 σ1 σ2.

Inductive pair_reductions_alt : mdl -> mdl -> config -> config -> Prop :=
| pra_single : forall M1 M2 σ1 σ2, pair_reduction_alt M1 M2 σ1 σ2 ->
                              pair_reductions_alt M1 M2 σ1 σ2
| pra_trans : forall M1 M2 σ1 σ σ2, pair_reduction_alt M1 M2 σ1 σ ->
                               pair_reductions_alt M1 M2 σ σ2 ->
                               pair_reductions_alt M1 M2 σ1 σ2.

Hint Constructors pair_reductions_alt.

Lemma reductions_step_e_assgn :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall χ ϕ ψ M x e v s,
                        σ1 = (χ, ϕ :: ψ) ->
                        contn ϕ = c_stmt ((r_ x) ≔ (r_exp e) ;; s) ->
                        M1 ⋄ M2 ≜ M ->
                        M ∙ σ1 ⊢ e ↪ v ->
                        exists σ, assgn_func x v σ1 = Some σ /\
                                  M ∙ σ1 ⤳ σ /\
                                  reductions_alt M1 M2 σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    intros;
    subst.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst;
        clear Hb
    end.
    match goal with
    | [Ha : is_external_self _ _ _ |- _ ] =>
      apply is_external_self_implies_not_is_internal in Ha;
        contradiction Ha
    end.
    unfold is_internal_self, is_internal in *;
      repeat destruct_exists_loo;
      andDestruct;
      repeat destruct_exists_loo;
      andDestruct;
      repeat map_rewrite.
    unfold vMap in *.
    repeat eq_auto.
    repeat eexists; eauto.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst;
        clear Hb
    end.
    unfold assgn_func.
    match goal with
    | [Ha : contn ?ϕ = _ |- context [contn ?ϕ]] =>
      rewrite Ha; simpl
    end.
    link_unique_auto.
    eval_rewrite.
    eexists;
      repeat split;
      eauto.
Qed.

Lemma reductions_step_assgn :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall χ ϕ ψ M x e v s,
                        σ1 = (χ, ϕ :: ψ) ->
                        contn ϕ = c_stmt (((r_ x) ≔ (r_exp e)) ;; s) ->
                        M1 ⋄ M2 ≜ M ->
                        M ∙ σ1 ⊢ e ↪ v ->
                        exists σ, assgn_func x v σ1 = Some σ /\
                                  M ∙ σ1 ⤳ σ /\
                                  reductions_alt M1 M2 σ σ2.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    intros;
    subst.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst;
        clear Hb
    end.
    match goal with
    | [Ha : is_external_self _ _ _ |- _ ] =>
      apply is_external_self_implies_not_is_internal in Ha;
        contradiction Ha
    end.
    unfold is_internal_self, is_internal in *;
      repeat destruct_exists_loo;
      andDestruct;
      repeat destruct_exists_loo;
      andDestruct;
      repeat map_rewrite.
    unfold vMap in *.
    repeat eq_auto.
    repeat eexists; eauto.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst;
        clear Hb
    end.
    unfold assgn_func.
    match goal with
    | [Ha : contn ?ϕ = _ |- context [contn ?ϕ]] =>
      rewrite Ha; simpl
    end.
    link_unique_auto.
    eval_rewrite.
    eexists;
      repeat split;
      eauto.
Qed.

(*Lemma reductions_step_if :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall χ ϕ ψ M e s1 s2 s,
                        σ1 = (χ, ϕ :: ψ) ->
                        contn ϕ = c_stmt ((s_if e s1 s2) ;; s) ->
                        M1 ⋄ M2 ≜ M ->
                        (exists σ, if_func v_true σ1 = Some σ /\
                                   M ∙ σ1 ⤳ σ /\
                                   reductions_alt M1 M2 σ σ2 /\
                                   M ∙ σ1 ⊢ e ↪ v_true) \/
                        (exists σ, if_func v_false σ1 = Some σ /\
                                   M ∙ σ1 ⤳ σ /\
                                   reductions_alt M1 M2 σ σ2 /\
                                   M ∙ σ1 ⊢ e ↪ v_false).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    intros;
    subst.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    + match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst;
          clear Hb
      end.
      match goal with
      | [Ha : is_external _ _ _ |- _ ] =>
        apply is_external_implies_not_is_internal in Ha;
          contradiction Ha
      end.
    + match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst;
          clear Hb
      end.
      match goal with
      | [Ha : is_external _ _ _ |- _ ] =>
        apply is_external_implies_not_is_internal in Ha;
          contradiction Ha
      end.

  - match goal with
    | [Ha : _ ∙ _ ⤳ _|- _] =>
      inversion Ha;
        subst;
        try solve [crush]
    end.
    + match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst;
          clear Hb
      end.
      unfold if_func.
      match goal with
      | [Ha : contn ?ϕ = _ |- context [contn ?ϕ]] =>
        rewrite Ha; simpl
      end.
      link_unique_auto.
      left;
        eexists;
        repeat split;
        eauto.
    + match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb;
          inversion Hb;
          subst;
          clear Hb
      end.
      unfold if_func.
      match goal with
      | [Ha : contn ?ϕ = _ |- context [contn ?ϕ]] =>
        rewrite Ha; simpl
      end.
      link_unique_auto.
      eval_rewrite.
      right;
        eexists;
        repeat split;
        eauto.
Qed.*)

Lemma pair_reduction_change_alt :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 forall (P : mdl -> mdl -> config -> Prop),
                   P M1 M2 σ1 ->
                   ~ P M1 M2 σ2 ->
                   exists σ σ', (σ = σ1 \/ pair_reductions_alt M1 M2 σ1 σ) /\
                           pair_reduction_alt M1 M2 σ σ' /\
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


Lemma pair_reduction_alt_equiv_1 :
  forall M1 M2 σ1 σ2, pair_reduction_alt M1 M2 σ1 σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳ σ2.
Proof.

Admitted.

Lemma pair_reductions_alt_equiv_1 :
  forall M1 M2 σ1 σ2, pair_reductions_alt M1 M2 σ1 σ2 ->
                 M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2.
Proof.
Admitted.


Lemma pair_reduction_alt_equiv_2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 pair_reduction_alt M1 M2 σ1 σ2.
Proof.

Admitted.

Lemma pair_reductions_alt_equiv_2 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                 pair_reductions_alt M1 M2 σ1 σ2.
Proof.
Admitted.

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
  + apply pair_reduction_alt_equiv_1; auto.
  + destruct Ha1; auto.
    right; apply pair_reductions_alt_equiv_1; auto.
Qed.

Lemma asgn_reduction_step :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall χ ϕ ψ, σ1 = (χ, ϕ :: ψ) ->
                                forall x r s, contn ϕ = c_stmt (((r_ x) ≔ r) ;; s) ->
                                              exists v, σ2 = (χ, frm (update x v (vMap ϕ)) (c_stmt s) :: ψ) /\
                                                        ((exists y, r = r_var y /\ vMap ϕ y = Some v) \/
                                                         (exists e, r = r_exp e /\ M ∙ σ1 ⊢ e ↪ v)).
Proof.

Admitted.

Lemma if_reduction_step :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
                  forall χ ϕ ψ, σ1 = (χ, ϕ :: ψ) ->
                                forall e s1 s2 s, contn ϕ = c_stmt ((s_if e s1 s2) ;; s) ->
                                                  (σ2 = (χ, frm (vMap ϕ) (c_stmt (s1 ;; s)) :: ψ) /\
                                                   M ∙ σ1 ⊢ e ↪ v_true) \/
                                                  (σ2 = (χ, frm (vMap ϕ) (c_stmt (s2 ;; s)) :: ψ) /\
                                                   M ∙ σ1 ⊢ e ↪ v_false).
Proof.

Admitted.

Lemma vAssgn_reductions_step :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall M χ ϕ ψ, σ1 = (χ, ϕ :: ψ) ->
                                      M1 ⋄ M2 ≜ M ->
                                      forall x r s, contn ϕ = c_stmt (((r_ x) ≔ r) ;; s) ->
                                                    exists σ v, σ = (χ, frm (update x v (vMap ϕ)) (c_stmt s) :: ψ) /\
                                                                ((exists e, r = r_exp e /\
                                                                            M ∙ σ1 ⊢ e ↪ v) \/
                                                                 (exists y f α o, r = r_fld y f /\
                                                                                  vMap ϕ y = Some (v_addr α) /\
                                                                                  χ α = Some o /\
                                                                                  flds o f = Some v)) /\
                                                                reductions_alt M1 M2 σ σ2 /\
                                                                M ∙ σ1 ⤳ σ /\
                                                                is_internal_self M1 M2 σ1 /\
                                                                is_internal_self M1 M2 σ.
Proof.

Admitted.

Lemma fAssgn_reductions_step :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall M χ ϕ ψ, σ1 = (χ, ϕ :: ψ) ->
                                      M1 ⋄ M2 ≜ M ->
                                      forall x f y s, contn ϕ = c_stmt ((x ◌ f ≔ (r_ y)) ;; s) ->
                                                 exists σ v α o, σ = (update α (new (cname o) (update f v (flds o))) χ,
                                                                 frm (vMap ϕ) (c_stmt s):: ψ) /\
                                                            vMap ϕ y = Some v /\
                                                            vMap ϕ x = Some (v_addr α) /\
                                                            χ α = Some o /\
                                                            (exists v', flds o f = Some v') /\
                                                            reductions_alt M1 M2 σ σ2 /\
                                                            M ∙ σ1 ⤳ σ /\
                                                            is_internal_self M1 M2 σ1 /\
                                                            is_internal_self M1 M2 σ.
Proof.

Admitted.

Lemma if_reductions_step :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                      forall M χ ϕ ψ, σ1 = (χ, ϕ :: ψ) ->
                                      M1 ⋄ M2 ≜ M ->
                                      forall e s1 s2 s, contn ϕ = c_stmt ((s_if e s1 s2) ;; s) ->
                                                        exists σ, ((σ = (χ, frm (vMap ϕ) (c_stmt (merge s1 s)) :: ψ) /\
                                                                    M ∙ σ1 ⊢ e ↪ v_true) \/
                                                                   (σ = (χ, frm (vMap ϕ) (c_stmt (merge s2 s)) :: ψ) /\
                                                                    M ∙ σ1 ⊢ e ↪ v_false)) /\
                                                                  reductions_alt M1 M2 σ σ2 /\
                                                                  M ∙ σ1 ⤳ σ /\
                                                                  is_internal_self M1 M2 σ1 /\
                                                                  is_internal_self M1 M2 σ.
Proof.

Admitted.

Lemma rtrn_1_reductions_step :
  forall M1 M2 σ1 σ2, reductions_alt M1 M2 σ1 σ2 ->
                 forall M χ ϕ1 ϕ2 ψ,
                   σ1 = (χ, ϕ1 :: ϕ2 :: ψ) ->
                   M1 ⋄ M2 ≜ M ->
                   forall x1 s1 x2 s2, contn ϕ1 = c_stmt ((s_rtrn x1) ;; s1) ->
                                  contn ϕ2 = c_hole x2 s2 ->
                                  exists σ v, (σ = (χ, frm (update x2 v (vMap ϕ2)) (c_stmt s2) :: ψ)) /\
                                         (vMap ϕ1 x1 = Some v) /\
                                         (M ∙ σ1 ⤳ σ)  /\
                                         ((reductions_alt M1 M2 σ σ2 /\
                                           is_internal_self M1 M2 σ1 /\
                                           is_internal_self M1 M2 σ) \/
                                          (σ2 = σ /\
                                           is_internal_self M1 M2 σ1 /\
                                           is_external_self M1 M2 σ)).
Proof.

Admitted.

Ltac reduction_step :=
  match goal with

    
  | [H : reductions_alt ?M1 ?M2
                        (?χ', {| vMap := ?β; contn := (c_stmt ((?x' ◌ ?f' ≔ (r_ ?y')) ;; ?s)) |} :: ?ψ')
                        ?σ2,
         Hlink : ?M1 ⋄ ?M2 ≜ ?M |- _ ] =>
    let σ := fresh "σ" in
    edestruct
      (fAssgn_reductions_step
         M1 M2
         (χ', {| vMap := β; contn := (c_stmt ((x' ◌ f' ≔ (r_ y')) ;; s)) |} :: ψ')
         σ2
         H)
      with
        (ϕ:={| vMap := β; contn := (c_stmt ((x' ◌ f' ≔ (r_ y')) ;; s)) |})
        (M:=M)(χ:=χ')(ψ:=ψ')
      as [σ];
    clear H

    
  | [H : reductions_alt ?M1 ?M2
                        (?χ', {| vMap := ?β; contn := (c_stmt ((?y ≔ ?r') ;; ?s)) |} :: ?ψ')
                        ?σ2,
         Hlink : ?M1 ⋄ ?M2 ≜ ?M |- _ ] =>
    let σ := fresh "σ" in
    edestruct
      (vAssgn_reductions_step
         M1 M2
         (χ', {| vMap := β; contn := (c_stmt ((y ≔ r') ;; s)) |} :: ψ')
         σ2
         H)
      with
        (ϕ:={| vMap := β; contn := (c_stmt ((y ≔ r') ;; s)) |})
        (r:=r')(M:=M)(χ:=χ')(ψ:=ψ')
      as [σ];
    clear H

          
  | [H : reductions_alt ?M1 ?M2
                        (?χ', {| vMap := ?β; contn := (c_stmt ((s_if ?e' ?s1' ?s2') ;; ?s')) |} :: ?ψ')
                        ?σ2,
         Hlink : ?M1 ⋄ ?M2 ≜ ?M |- _ ] =>
    let σ := fresh "σ" in
    edestruct
      (if_reductions_step
         M1 M2
         (χ', {| vMap := β; contn := (c_stmt ((s_if e' s1' s2') ;; s')) |} :: ψ')
         σ2
         H)
      with
        (ϕ:={| vMap := β; contn := (c_stmt ((s_if e' s1' s2') ;; s')) |})
        (e:=e')(s1:=s1')(s2:=s2')(M:=M)(χ:=χ')(ψ:=ψ')(s:=s')
      as [σ];
    clear H

          
  | [H : reductions_alt ?M1 ?M2
                        (?χ', {| vMap := ?β1; contn := (c_stmt ((s_rtrn ?x1') ;; ?s1')) |}
                                :: {| vMap := ?β2; contn := (c_hole ?x2' ?s2') |}
                                :: ?ψ')
                        ?σ2',
         Hlink : ?M1 ⋄ ?M2 ≜ ?M |- _ ] => 
    let σ := fresh "σ" in
    edestruct (rtrn_1_reductions_step
                 M1 M2
                 (χ', {| vMap := β1; contn := (c_stmt ((s_rtrn x1') ;; s1')) |}
                        :: {| vMap := β2; contn := (c_hole x2' s2') |}
                        :: ψ')
                 σ2'
                 H)
      with
        (ϕ1:={| vMap := β1; contn := (c_stmt ((s_rtrn x1') ;; s1')) |})
        (ϕ2:={| vMap := β2; contn := (c_hole x2' s2') |})
      as [σ];
    clear H
  end.

Module SafeExample.

  (**
∀s.[s : Safe ∧ s.treasure <> null ∧ will(s.treasure = null) 
        ⟶ ∃o.[external(o) ∧ (o access s.secret)]]
   *)

  (** Safe Definition *)

  Definition Safe := classID 1.

  Definition treasure := fieldID 0.

  Definition secret := fieldID 1.

  Definition take := methID 0.

  Definition scr := bnd 1.

  Definition x := bnd 2.

  Definition y := bnd 3.

  Definition takeBody := ((r_ x) ≔ (r_exp (e_val (v_null)))) ;;
                         (((r_ y) ≔ (this ◌ treasure)) ;;
                          ((s_if ((e_var scr) ⩵ (e_acc_f (e_var this) secret))
                                 (((this ◌ treasure) ≔ (r_ x)) ;;
                                  (s_rtrn y))
                                 (s_rtrn x)) ;;
                           (s_rtrn x))).

  Definition SafeDef1 := clazz Safe
                               (treasure :: secret :: nil)
                               (update
                                  take (scr :: nil, takeBody)
                                  empty)
                               empty.

  (** MyModule Definition *)

  Definition MyModule1 := (update
                             Safe SafeDef1
                             empty).

  Lemma link_MyModule1_Safe :
    forall M' M, MyModule1 ⋄ M' ≜ M ->
            M Safe = Some SafeDef1.
  Proof.
    intros.
    inversion H;
      subst;
      simpl.
    unfold MyModule1, extend in *; simpl.
    repeat map_rewrite.
  Qed.



  Lemma take_implies_secret :
    forall M1 M2 σ1 σ2, pair_reduction_alt MyModule1 M2 σ1 σ2 ->
                   M1 = MyModule1 ->
                   forall x α β o, method_is_called σ1 x α take β ->
                              mapp σ1 α = Some o ->
                              cname o = Safe ->
                              exists v, flds o secret = Some v.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      inversion Hred;
      subst;
      intros.

    inversion H4; subst.
    inversion H0; subst;
      repeat simpl_crush;
      try solve [crush].
    interpretation_rewrite.
    simpl_crush.
    unfold mapp, configMapHeap, fst in H5.
    
    match goal with
    | [Ha : ?χ ?α = Some _,
            Hb : ?χ ?α = Some _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    match goal with
    | [Ha : cname ?o = _,
            Hb : context[cname ?o] |- _] =>
      rewrite Ha in Hb
    end.
    erewrite link_MyModule1_Safe in H13;
      eauto.
    inversion H13;
      subst.
    simpl in H14.
    unfold update, t_update in H14;
      eq_auto.
    inversion H14;
      subst.
    unfold takeBody in H2.

    reduction_step;
      simpl; eauto;
        destruct_exists_loo;
        andDestruct;
        subst;
        simpl in *.
    destruct Ha0 as [|Htmp];
      [|destruct Htmp];
      repeat destruct_exists_loo;
      andDestruct;
      try solve [crush].

    match goal with
    | [H : r_exp _ = r_exp _ |- _] =>
      inversion H; subst
    end.

    reduction_step;
      simpl; eauto;
        destruct_exists_loo;
        andDestruct;
        subst;
        simpl in *.
    destruct Ha1 as [|Htmp];
      [|destruct Htmp];
      repeat destruct_exists_loo;
      andDestruct;
      try solve [crush].

    match goal with
    | [H : (?x ◌ ?f) = (_ ◌ _) |- _] =>
      inversion H; subst
    end.

    assert (α0=α);
      [repeat map_rewrite;
       unfold x, this;
       crush
      |subst α0].

    reduction_step;
      simpl; eauto;
        andDestruct;
        subst;
        simpl in *;
        andDestruct.
    destruct Ha4;
      andDestruct;
      subst.

    - match goal with
      | [Heval : ?M ∙ ?σ ⊢ (_ ⩵ e_acc_f (e_var this) secret) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      match goal with
      | [Heval : ?M ∙ ?σ ⊢ (e_acc_f (e_var this) secret) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      repeat map_rewrite.
      match goal with
      | [Heval : ?M ∙ ?σ ⊢ (e_var this) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      repeat map_rewrite.
      simpl in *.
      match goal with
      | [H : Some _ = Some _ |- _]  =>
        inversion H;
          subst;
          clear H
      end.
      repeat match goal with
             | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _]  =>
               rewrite Ha in Hb;
                 inversion Hb;
                 subst
             end.
      eauto.

    - match goal with
      | [Heval : ?M ∙ ?σ ⊢ (_ ⩵ e_acc_f (e_var this) secret) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      match goal with
      | [Heval : ?M ∙ ?σ ⊢ (e_acc_f (e_var this) secret) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      repeat map_rewrite.
      match goal with
      | [Heval : ?M ∙ ?σ ⊢ (e_var this) ↪ ?v |- _] =>
        inversion Heval;
          subst
      end.
      repeat map_rewrite.
      simpl in *.
      match goal with
      | [H : Some _ = Some _ |- _]  =>
        inversion H;
          subst;
          clear H
      end.
      repeat match goal with
             | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _]  =>
               rewrite Ha in Hb;
                 inversion Hb;
                 subst
             end.
      eauto.

  Qed.                            

  Lemma take_implies_treasure :
    forall M1 M2 σ1 σ2, pair_reduction_alt MyModule1 M2 σ1 σ2 ->
                   M1 = MyModule1 ->
                   forall x α β o, method_is_called σ1 x α take β ->
                              mapp σ1 α = Some o ->
                              cname o = Safe ->
                              exists v, flds o treasure = Some v.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      inversion Hred;
      subst;
      intros.

    inversion H4; subst.
    inversion H0; subst;
      repeat simpl_crush;
      try solve [crush].
    interpretation_rewrite.
    unfold mapp, configMapHeap, fst in H5.
    repeat simpl_crush.
    match goal with
    | [Ha : cname ?o = _,
            Hb : context[cname ?o] |- _] =>
      rewrite Ha in Hb
    end.
    erewrite link_MyModule1_Safe in H13;
      eauto.
    inversion H13;
      subst.
    simpl in H14.
    unfold update, t_update in H14;
      eq_auto.
    inversion H14;
      subst.
    unfold takeBody in H2.

    reduction_step;
      simpl; eauto;
        repeat destruct_exists_loo;
        andDestruct.
    destruct Ha0 as [|Htmp];
      [|destruct Htmp];
      try solve [crush];
      subst;
      andDestruct;
      simpl in *.

    reduction_step;
      simpl; eauto;
        repeat destruct_exists_loo;
        andDestruct.
    destruct Ha0 as [|Htmp];
      [|destruct Htmp];
      try solve [crush];
      subst;
      andDestruct;
      simpl in *.

    repeat destruct_exists_loo;
      andDestruct.
    match goal with
    | [H : _ ◌ _ = _ ◌ _  |- _] =>
      inversion H; subst
    end.
    assert (this <> x);
      [unfold this, x; crush|].
    repeat map_rewrite;
      repeat match goal with
             | [H : Some _ = Some _ |- _] =>
               inversion H; subst
             end.
    match goal with
    | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst;
        clear Hb
    end.
    eauto.
  Qed.

  Lemma pair_reduction_take_is_called :
    forall M σ1 σ2, MyModule1 ⦂ M ⦿ σ1 ⤳ σ2 ->
               forall χ ϕ ψ,
                 σ1 = (χ, ϕ :: ψ) ->
                 exists x α β o, method_is_called σ1 x α take β /\
                            mapp σ1 α = Some o /\
                            cname o = Safe.
  Proof.
  Admitted.

  Lemma take_pre_post_alt :
    forall M1 M2 σ1 σ2, pair_reduction_alt M1 M2 σ1 σ2 ->
                   M1 = MyModule1 ->
                   forall χ ϕ ψ s1 s2,
                     σ1 = (χ, ϕ :: ψ) ->
                     contn ϕ = c_stmt (s1 ;; s2) ->
                     forall x α β o, method_is_called σ1 x α take β ->
                                mapp σ1 α = Some o ->
                                cname o = Safe ->
                                exists t s, flds o treasure = Some t /\
                                       flds o secret = Some s /\
                                       ((β scr = Some s /\
                                         σ2 = (update α (new Safe (update treasure v_null (flds o))) χ,
                                               (frm (update x t (vMap ϕ)) (c_stmt s2)) :: ψ)) \/
                                        ((exists s', β scr = Some s' /\
                                                s' <> s /\
                                                σ2 = (χ,
                                                      frm (update x v_null (vMap ϕ)) (c_stmt s2)
                                                          :: ψ)))).
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      inversion Hred;
      intros;
      subst.

    inversion H10; subst.
    inversion H0; subst;
      try simpl_crush;
      try solve [crush].
    match goal with
    | [Ha : contn ?ϕ = _,
            Hb : contn ?ϕ = _ |- _] =>
      rewrite Ha in Hb;
        inversion Hb;
        subst
    end.
    interpretation_rewrite.
    match goal with
    | [Ha : (v_addr _) = (v_addr _) |- _] =>
      inversion Ha;
        subst
    end.
    assert (o0 = o);
      [repeat map_rewrite; crush|subst].
    match goal with
    | [Ha : cname ?o = ?C',
            Hb : ?M (cname ?o) = ?Def' |- _] =>
      rewrite Ha in Hb
    end.
    assert (C = SafeDef1);
    [apply linked_class with (C:=Safe)(Def:=SafeDef1) in H; auto;
        [|unfold Safe, ObjectName; crush];
        match goal with
        | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _] =>
          rewrite Ha in Hb;
          inversion Hb;
          subst;
          clear Hb
        end;
        auto|subst].

    match goal with
    | [H : c_meths SafeDef1 take = Some (_, _) |- _] =>
      unfold SafeDef1 in H;
        simpl in H;
        unfold update, t_update in H;
        eq_auto;
        inversion H;
        subst;
        clear H
    end.
    repeat simpl_crush.

    match goal with
    | [H : reductions_alt _ _ (_, {|vMap := _; contn := c_stmt takeBody |} :: _ :: _) _ |- _] =>
      unfold takeBody in H
    end.

    reduction_step;
      simpl; eauto;
        repeat destruct_exists_loo;
        andDestruct;
        subst.
    destruct Ha0 as [|Htmp];
      [|destruct Htmp];
      try solve [crush];
      destruct_exists_loo;
      andDestruct.
    match goal with
    | [H : r_exp _ = r_exp _ |- _] =>
      inversion H;
        subst;
        clear H
    end.
    match goal with
    | [H: _ ∙ _ ⊢ e_null ↪ ?v |- _] =>
      inversion H;
        subst
    end.

    reduction_step;
      simpl; eauto;
        repeat destruct_exists_loo;
        andDestruct;
        subst.
    destruct Ha0 as [|Htmp];
      [|destruct Htmp];
      try solve [crush];
      repeat destruct_exists_loo;
      andDestruct;
      simpl in *.
    assert (this <> x);
      [unfold x, this;
       crush|].
    repeat simpl_crush.
    assert (α0 = α);
      [repeat map_rewrite;
       repeat eq_auto;
       repeat simpl_crush;
       auto|subst; simpl_crush].

    exists v.

    reduction_step;
      simpl; eauto;
        andDestruct;
        subst.
    destruct Ha;
      andDestruct;
      subst.

    - (*scr == secret*)
      assert (exists s, flds o0 secret = Some s /\ (ps ∘ (vMap ϕ0)) scr = Some s).
      + match goal with
        | [Heval : _ ∙ _ ⊢ (_ ⩵ (e_acc_f (e_var this) secret)) ↪ v_true |- _] =>
          inversion Heval;
            subst
        end.
        match goal with
        | [Heval : _ ∙ _ ⊢ (e_acc_f (e_var this) secret) ↪ ?v |- _] =>
          inversion Heval;
            subst
        end.
        match goal with
        | [Heval : _ ∙ _ ⊢ ((e_var this)) ↪ ?v |- _] =>
          inversion Heval;
            subst
        end.
        repeat map_rewrite.
        simpl in *.
        repeat simpl_crush.
        exists v0; split; auto.
        match goal with
        | [Heval : _ ∙ _ ⊢ (e_var scr) ↪ ?v |- _ = Some ?v] =>
          inversion Heval; subst
        end.
        unfold mapp, configMapStack, mapp, stackMap, snd, vMap in H14.
        simpl in H14.
        auto.

      + destruct_exists_loo; andDestruct.
        exists v0; repeat split; auto.
        left; split; auto.
        simpl in *.

        reduction_step;
          simpl; eauto;
            repeat destruct_exists_loo;
            andDestruct;
            subst;
            simpl in *.
        assert (x <> y);
          [unfold y, x; crush|].
        unfold update, t_update in Ha8;
          repeat eq_auto;
          repeat simpl_crush.

        unfold mapp, configMapHeap, fst in H11.
        assert (y <> this);
          [unfold y, this; crush|].
        unfold update, t_update in Ha9;
          repeat eq_auto;
          repeat simpl_crush.

        repeat match goal with
               | [Ha : ?P, Hb : ?P |-_] =>
                 clear Hb
               end.

        reduction_step;
          simpl; eauto;
            repeat destruct_exists_loo
            repeat simpl_crush;
            andDestruct;
            subst;
            simpl in *;
            repeat destruct_exists_loo;
            andDestruct.
        destruct Hb1;
          andDestruct;
          subst.
        * apply is_internal_self_implies_not_is_external in Hb4.
          contradiction Hb4.
          unfold is_external_self, is_external.
          unfold is_external_self, is_external in H1;
            repeat destruct_exists_loo;
            andDestruct;
            repeat destruct_exists_loo;
            andDestruct.
          exists α; split; [|exists o0];
          unfold mapp, configMapStack, configMapHeap, mapp, snd, fst, stackMap;
            simpl;
            [|split; auto].
          unfold update, t_update;
            eq_auto.
          assert (α <> α0);
            [|unfold update, t_update; eq_auto].
          intros Hcontra;
            subst.
          unfold mapp, configMapHeap, fst in Ha9.
          repeat simpl_crush.
          match goal with
          | [H : cname ?o = Safe |- _] =>
            rewrite H in *
          end.
          repeat simpl_crush.
          match goal with
          | [H : MyModule1 Safe = None |- _] =>
            unfold MyModule1 in H;
              simpl in H;
              unfold update, t_update in H;
              repeat eq_auto
          end.
          crush.

        * assert (x <> y);
            [unfold x, y; crush|].
          unfold update, t_update in Ha3;
            repeat eq_auto;
            repeat simpl_crush.
          match goal with
          | [H : cname ?o = Safe |- context[cname ?o]] =>
            rewrite H
          end.
          auto.

    - (*scr ⩵̸ secret*)
      simpl in *.
      assert (exists s s', flds o0 secret = Some s /\ (ps ∘ (vMap ϕ0)) scr = Some s' /\ s <> s').
      + match goal with
        | [Heval : _ ∙ _ ⊢ (_ ⩵ (e_acc_f (e_var this) secret)) ↪ v_false |- _] =>
          inversion Heval;
            subst
        end.
        match goal with
        | [Heval : _ ∙ _ ⊢ (e_acc_f (e_var this) secret) ↪ ?v |- _] =>
          inversion Heval;
            subst
        end.
        match goal with
        | [Heval : _ ∙ _ ⊢ ((e_var this)) ↪ ?v |- _] =>
          inversion Heval;
            subst
        end.
        repeat map_rewrite.
        simpl in *.
        repeat simpl_crush.
        match goal with
        | [Heval : _ ∙ _ ⊢ (e_var scr) ↪ ?v |- _] =>
          inversion Heval; subst
        end.
        unfold mapp, configMapStack, mapp, stackMap, snd, vMap in H18.
        simpl in H18.
        exists v2, v1; split; auto.

      + repeat destruct_exists_loo; andDestruct.
        exists v0; repeat split; auto.
        right; exists v1; repeat split; auto.

        reduction_step;
          simpl; eauto;
            repeat destruct_exists_loo;
            andDestruct;
            subst;
            simpl in *.
        assert (x <> y);
          [unfold y, x; crush|].
        unfold update, t_update in Ha9;
          repeat eq_auto;
          repeat simpl_crush.

        repeat match goal with
               | [Ha : ?P, Hb : ?P |-_] =>
                 clear Hb
               end.

(*        unfold mapp, configMapHeap, fst in H12.
        assert (y <> this);
          [unfold y, this; crush|].
        unfold update, t_update in Ha10;
          repeat eq_auto;
          repeat simpl_crush.

        repeat match goal with
               | [Ha : ?P, Hb : ?P |-_] =>
                 clear Hb
               end.*)

        destruct Hb5;
          andDestruct;
          subst;
          auto.
        apply is_internal_self_implies_not_is_external in Hb1.
        contradiction Hb1.
        unfold is_external_self, is_external.
        unfold is_external_self, is_external in H1;
          repeat destruct_exists_loo;
          andDestruct;
          repeat destruct_exists_loo;
          andDestruct.
        exists α0; split; [|exists o];
          unfold mapp, configMapStack, configMapHeap, mapp, snd, fst, stackMap;
          simpl;
          repeat split;
          auto.
        unfold update, t_update;
          eq_auto;
          auto.
  Qed.

  Lemma take_pre_post :
    forall M σ1 σ2, MyModule1 ⦂ M ⦿ σ1 ⤳ σ2 ->
               forall χ ϕ ψ s1 s2,
                 σ1 = (χ, ϕ :: ψ) ->
                 contn ϕ = c_stmt (s1 ;; s2) ->
                 forall x α β o, method_is_called σ1 x α take β ->
                            mapp σ1 α = Some o ->
                            cname o = Safe ->
                            exists t s, flds o treasure = Some t /\
                                   flds o secret = Some s /\
                                   ((β scr = Some s /\
                                     σ2 = (update α (new Safe (update treasure v_null (flds o))) χ,
                                           (frm (update x t (vMap ϕ)) (c_stmt s2)) :: ψ)) \/
                                    ((exists s', β scr = Some s' /\
                                            s' <> s /\
                                            σ2 = (χ,
                                                  frm (update x v_null (vMap ϕ)) (c_stmt s2)
                                                      :: ψ)))).
  Proof.
    intros.
    eapply take_pre_post_alt; eauto.
    eapply pair_reduction_alt_equiv_2; eauto.
  Qed.                   
  
  Definition HolisticSpec := (∀x∙ (∀x∙(((a_class (a♢1) Safe)
                                        ∧
                                        ((ex_acc_f (e♢1) secret) ⩶ (e♢0))
                                        ∧
                                        ((ex_acc_f (e♢1) treasure) ⩶̸ (ex_null))
                                         ∧
                                         (a_will ((ex_acc_f (e♢1) treasure) ⩶ (ex_null))))
                                           ⟶
                                           (a_will (∃x∙ (((a♢0) external)
                                                         ∧
                                                         ((a♢0) access (a♢1))))
                                            ∨
                                            (∃x∙ (((a♢0) external)
                                                  ∧
                                                  ((a♢0) access (a♢1))))
                             )))).

  Theorem safe_example :
    MyModule1 ⊨m HolisticSpec.
  Proof.
    unfold mdl_sat;
      intros;
      destruct_exists_loo.
    unfold HolisticSpec;
      a_intros.
    a_prop.
    inversion H5;
      subst.
    let σ := fresh "σ" in
    destruct (pair_reduction_change MyModule1 M' (χ, ϕ :: nil) σ')
      with (P := fun (M1 M2 : mdl)(σ : config) =>
                   M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ ⊨ (ex_acc_f (e_ α) treasure ⩶̸ (ex_null)))
      as [σ];
      auto.
    + eapply sat_head_exp; eauto.
      eapply sat_initial_exp; eauto.

    + intros Hcontra.
      inversion H15; subst.
      inversion Hcontra;
        subst.
      link_unique_auto.
      repeat match goal with
             | [H : is_exp ?e ?e' |- _] =>
               inversion H;
                 subst;
                 clear H
             end.
      inversion H20; subst.
      inversion H18; subst.
      eval_rewrite.
      crush.

    + destruct_exists_loo;
        andDestruct.
      destruct Ha; subst.

      * let x := fresh "x" in
        destruct (pair_reduction_take_is_called M' (χ, ϕ :: nil) σ1)
          with (χ0:=χ)(ϕ0:=ϕ)(ψ:=@nil frame)
          as [x];
          auto;
          repeat destruct_exists_loo;
          andDestruct.
        inversion Ha;
          subst.
        let v := fresh "v" in
        destruct (take_pre_post M' (χ, ϕ :: nil) σ1)
          with (χ0:=χ)(ϕ0:=ϕ)(ψ:=@nil frame)(x:=x0)(α:=α1)(β:=β0 ∘ vMap ϕ)(o:=o1)
               (s1:=s_meth x0 y0 take β0)(s2:=s)
          as [v];
          auto;
          repeat destruct_exists_loo;
          andDestruct.
        inversion H7; subst.
        repeat match goal with
               | [H : is_exp _ _ |- _] =>
                 inversion H;
                   subst;
                   clear H
               end.
        assert (α1 = α);
          [admit|subst]. (* because α is the one that changes *)
        assert (o1 = o);
          [repeat map_rewrite; crush|subst].
        inversion H19; subst.
        inversion H14; subst.
        inversion H16; subst.
        inversion H12; subst.
        assert (o1 = o);
          [repeat map_rewrite; crush|subst].
        assert (v0 = (v_addr α0));
          [crush|subst].
        destruct Hb2;
          andDestruct;
          subst.
        ** assert (is_external_self MyModule1 M' (χ, ϕ :: ψ));
             [apply pair_reductions_is_external_2 with (σ1:=σ0); auto|].
           unfold is_external_self, is_external in H8;
             repeat destruct_exists_loo;
             andDestruct;
             repeat destruct_exists_loo;
             andDestruct.
           link_unique_auto.

           right.
           apply sat_ex_x with (α:=α)(o:=o1);
             simpl;
             auto;
             a_prop.
           eapply sat_extrn; eauto.
           unfold bind in Ha6; simpl in Ha6.
           let x := fresh "x" in
           destruct (partial_map_dec scr β0) as [x|Hnone];
             [destruct_exists_loo|rewrite Hnone in Ha6; inversion Ha6].
           eapply sat_access3 with (x:=x1); eauto.
           eapply int_x; simpl; eauto.
           eapply int_x; simpl; eauto.
           rewrite H8 in Ha6; auto.
           apply in_stmts_1.
           apply in_meth_3.
           exists scr; auto.

        ** admit. (* contradiction: nothing changes, i.e. treasure <> null *)

      * admit. (* above but again *)        
  Admitted.

End SafeExample.
