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
                       {|
                         cname := cname o1;
                         flds := fun x : fld => if eqb x f then Some v else flds o1 x;
                         meths := meths o1 |});
          [crush|rewrite Htmp in H16; unfold flds in *].
        assert (Hflds : (let (_, flds, _) := o1 in flds) = (flds o1));
          [auto|rewrite Hflds in H16].
        eq_auto.
        crush.

      * repeat map_rewrite.
        rewrite H5 in H13;
          inversion H13;
          subst.
        assert (Htmp : o2 =
                       {|
                         cname := cname o1;
                         flds := fun x : fld => if eqb x f then Some v else flds o1 x;
                         meths := meths o1 |});
          [crush|rewrite Htmp in H16; unfold flds in *].
        assert (Hflds : (let (_, flds, _) := o1 in flds) = (flds o1));
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

Inductive method_is_called : config -> addr -> mth -> partial_map var value -> Prop :=
| meth_called : forall x y m β s α ϕ χ ψ, contn ϕ = c_stmt (s_meth x y m β ;; s) ->
                                     ⌊ y ⌋ (χ, ϕ :: ψ) ≜ (v_addr α) ->
                                     method_is_called (χ, ϕ::ψ) α m (β ∘ (vMap ϕ)).

Hint Constructors method_is_called stmt_in_method : loo_db.

Lemma arising_frame_is_method_call_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ1 χ2 ϕ1 ϕ2 ψ1 ψ2,
               σ1 = (χ1, ϕ1 :: ψ1) ->
               σ2 = (χ2, ϕ2 :: ψ2) ->
               length (snd σ1) < length (snd σ2) ->
               (exists α m β s, method_is_called σ1 α m β /\
                           contn ϕ2 = c_stmt s /\
                           stmt_in_method M χ1 α m s).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    crush;
    repeat simpl_crush.

  exists α, m, (ps ∘ vMap ϕ1), s;
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
    match goal with
    | [ Ha : vMap ?ϕ1 ?x = vMap ?ϕ2 ?x,
             Hb : vMap ?ϕ1 ?x = Some _,
                  Hc : vMap ?ϕ2 ?x = Some _ |- _] =>
      rewrite Ha in Hb;
        rewrite Hb in Hc
    end;
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
                           (exists α m β s, method_is_called σ1 α m β /\
                                       contn ϕ2 = c_stmt s /\
                                       stmt_in_method M χ1 α m s) \/
                           (exists χ ϕ ψ α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                             method_is_called (χ, ϕ :: ψ) α m β /\
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

Definition is_internal (M1 M2 : mdl)(σ : config) :=
  (exists α o CDef, mapp σ this = Some (v_addr α) /\
               mapp σ α = Some o /\
               M1 (cname o) = Some CDef).

Definition is_external (M1 M2 : mdl)(σ : config) :=
  (exists α o, mapp σ this = Some (v_addr α) /\
          mapp σ α = Some o /\
          M1 (cname o) = None).

Lemma frame_arising_from_single_frame_external_internal_is_method_call_reductions :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             forall χ1 ϕ1,
               σ1 = (χ1, ϕ1 :: nil) ->
               forall M1 M2,
                 M1 ⋄ M2 ≜ M ->
                 is_external M1 M2 σ1 ->
                 is_internal M1 M2 σ2 ->
                 forall χ2 ϕ2 ψ2, σ2 = (χ2, ϕ2 :: ψ2) ->
                             (exists α m β s, method_is_called σ1 α m β /\
                                         contn ϕ2 = c_stmt s /\
                                         stmt_in_method M χ1 α m s) \/
                             (exists χ ϕ ψ α m β s, reductions M σ1 (χ, ϕ :: ψ) /\
                                               method_is_called (χ, ϕ :: ψ) α m β /\
                                               contn ϕ2 = c_stmt s /\
                                               stmt_in_method M χ α m s).
Proof.
  intros.
  eapply frame_arising_from_single_frame_is_method_call_reductions;
    eauto.
  unfold is_external, is_internal in *;
    repeat destruct_exists_loo;
    andDestruct;
    subst;
    repeat map_rewrite.
  intros Hcontra;
    rewrite Hcontra in *.
  rewrite Ha in Ha1;
    inversion Ha1;
    subst.

  let o' := fresh "o" in
  destruct (reductions_preserves_heap_locations_classes M (χ1, ϕ1::nil)(χ2, ϕ2 :: ψ2))
    with (α:=α0)(o:=o0) as [o'];
    auto;
    andDestruct.
  repeat map_rewrite.
  rewrite Ha0 in Ha3;
    inversion Ha3;
    subst.
  rewrite Hb in *;
    crush.
Qed.

Lemma is_external_implies_not_is_internal :
  forall M1 M2 σ, is_external M1 M2 σ ->
             ~ is_internal M1 M2 σ.
Proof.
  intros;
    unfold is_internal, is_external in *;
    intro Hcontra;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Lemma is_internal_implies_not_is_external :
  forall M1 M2 σ, is_internal M1 M2 σ ->
             ~ is_external M1 M2 σ.
Proof.
  intros;
    intro Hcontra;
    unfold is_internal, is_external in *;
    repeat destruct_exists_loo;
    andDestruct;
    crush.
Qed.

Inductive stack_trace : mdl -> mdl -> config -> Prop :=
| trace_initial : forall M1 M2 χ ϕ x s, is_external M1 M2 (χ, ϕ :: nil) ->
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
                                           is_external M1 M2 σ1 ->
                                           (is_external M1 M2 σ2 \/
                                            (is_internal M1 M2 σ2 /\
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

  Definition scr := bnd 0.

  Definition x := bnd 1.

  Definition y := bnd 2.

  Definition takeBody := ((r_ x) ≔ (r_exp (e_val (v_null))) ;;
                         (s_if ((e_var scr) ⩵ (e_acc_f (e_var this) secret))
                               ((r_ y) ≔ (this ◌ secret) ;; ((this ◌ secret) ≔ (r_ x)) ;; (s_rtrn y))
                               (s_rtrn x)) ;;
                         (s_rtrn x)).

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

  Definition HolisticSpec := (∀x∙ (∀x∙(((a_class (a♢1) Safe)
                                        ∧
                                        ((ex_acc_f (e♢1) secret) ⩶ (e♢0))
                                        ∧
                                        ((ex_acc_f (e♢1) treasure) ⩶̸ (ex_null))
                                        ∧
                                        (a_will (((ex_acc_f (e♢1) treasure) ⩶ (ex_null)))))
                                         ⟶
                                         (∃x∙ (((a♢0) external)
                                               ∧
                                               ((a♢0) access (a♢1))))
                             ))).

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

    let χ := fresh "χ" in
    let ψ := fresh "ψ" in
    destruct σ' as [χ ψ].

    assert (exists ϕ' ψ', ψ0 = ϕ' :: ψ');
      [admit|repeat destruct_exists_loo; subst].
    (*destruct (reductions_field_change M (χ, ϕ :: nil) (χ0, ϕ0 :: ψ1))
      with (χ1:=χ)(ϕ1:=ϕ)(ψ2:=ψ1)(χ2:=χ0)(ϕ2:=ϕ0)(f:=treasure).*)
              
  Admitted.

End SafeExample.

