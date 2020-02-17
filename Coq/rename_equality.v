Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(*Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.*)

Inductive exp_equiv : partial_map var var -> exp -> exp -> Prop :=
| eq_val : forall f v, exp_equiv f (e_val v) (e_val v)
| eq_var : forall f x1 x2, f x1 = Some x2 ->
                      exp_equiv f (e_var x1) (e_var x2)
| eq_hole : forall f n, exp_equiv f (e_hole n) (e_hole n)
| eq_eq : forall f e1 e2 e1' e2', exp_equiv f e1 e2 ->
                             exp_equiv f e1' e2' ->
                             exp_equiv f (e_eq e1 e1') (e_eq e2 e2')
| eq_if : forall f ea1 eb1 ec1 ea2 eb2 ec2, exp_equiv f ea1 ea2 ->
                                       exp_equiv f eb1 eb2 ->
                                       exp_equiv f ec1 ec2 ->
                                       exp_equiv f (e_if ea1 eb1 ec1) (e_if ea2 eb2 ec2)
| eq_acc_f : forall fn e1 e2 f, exp_equiv fn e1 e2 ->
                           exp_equiv fn (e_acc_f e1 f) (e_acc_f e2 f)
| eq_acc_g : forall f e1 e2 e1' e2' g, exp_equiv f e1 e2 ->
                                  exp_equiv f e1' e2' ->
                                  exp_equiv f (e_acc_g e1 g e1') (e_acc_g e2 g e2').

Inductive ref_equiv : (partial_map var var) -> ref -> ref -> Prop :=
| eqr_var : forall fn x y, fn x = Some y ->
                      ref_equiv fn (r_var x) (r_var y)
| eqr_fld : forall fn x y f, fn x = Some y ->
                        ref_equiv fn (r_fld x f) (r_fld y f).

Inductive stmt_equiv : (partial_map var var) -> stmt -> stmt -> Prop :=
| eq_asgn : forall f x1 y1 x2 y2, ref_equiv f x1 x2 ->
                             ref_equiv f y1 y2 ->
                             stmt_equiv f (s_asgn x1 y1) (s_asgn x2 y2)
| eq_meth : forall f x1 x2 y1 y2 m ps1 ps2,
    f x1 = Some x2 ->
    f y1 = Some y2 ->
    (forall p x, ps1 p = Some x ->
            exists y, f x = Some y) ->
    ps2 = ps1 ∘ f ->
    stmt_equiv f (s_meth x1 y1 m ps1) (s_meth x2 y2 m ps2)
| eq_new : forall f x1 x2 C ps1 ps2,
    f x1 = Some x2 ->
    (forall p x, ps1 p = Some x ->
            exists y, f x = Some y) ->
    ps2 = ps1 ∘ f ->
    stmt_equiv f (s_new x1 C ps1) (s_new x2 C ps2)
| eq_stmts : forall f s1 s2 s1' s2',
    stmt_equiv f s1 s2 ->
    stmt_equiv f s1' s2' ->
    stmt_equiv f (s_stmts s1 s1') (s_stmts s2 s2')
| eq_rtrn : forall f x1 x2,
    f x1 = Some x2 ->
    stmt_equiv f (s_rtrn x1) (s_rtrn x2).


Inductive contn_equiv : partial_map var var -> continuation -> continuation -> Prop :=
| eqc_hole : forall f x1 x2 s1 s2, f x1 = Some x2 ->
                              stmt_equiv f s1 s2 ->
                              contn_equiv f (c_hole x1 s1) (c_hole x2 s2)
| eqc_stmt : forall f s1 s2, stmt_equiv f s1 s2 ->
                        contn_equiv f (c_stmt s1) (c_stmt s2).

Definition wf_rename (f : partial_map var var) :=
  one_to_one f /\
  f this = Some this.

Inductive map_equiv : partial_map var var -> partial_map var value -> partial_map var value -> Prop :=
| eq_map : forall f m1 m2, m1 = f ∘ m2 ->
                      (forall x α, m1 x = Some α ->
                              exists y, f x = Some y) ->
                      (forall x α, m2 x = Some α ->
                              exists y, f y = Some x) ->
                      wf_rename f ->
                      map_equiv f m1 m2.

Lemma wf_one_to_one :
  forall f, wf_rename f -> one_to_one f.
Proof.
  intros; unfold wf_rename in *; andDestruct; auto.
Qed.

Hint Resolve wf_one_to_one.

Lemma wf_id :
  wf_rename id.
Proof.
  unfold wf_rename;
    split;
    auto.
  unfold one_to_one;
    intros.
  unfold id in *;
    crush.
Qed.

Hint Resolve wf_id.

Inductive frame_equiv : partial_map var var -> frame -> frame -> Prop :=
| eq_frm : forall f ϕ1 ϕ2, contn_equiv f (contn ϕ1) (contn ϕ2) ->
                      map_equiv f (vMap ϕ1) (vMap ϕ2) ->
                      wf_rename f ->
                      frame_equiv f ϕ1 ϕ2.

Inductive stack_equiv : stack -> stack -> Prop :=
| eq_nil : stack_equiv nil nil
| eq_cons : forall f ϕ1 ϕ2 ψ1 ψ2, frame_equiv f ϕ1 ϕ2 ->
                             stack_equiv ψ1 ψ2 ->
                             stack_equiv (ϕ1::ψ1) (ϕ2::ψ2).

Inductive config_equiv : config -> config -> Prop :=
| eq_conf : forall χ ψ1 ψ2, stack_equiv ψ1 ψ2 ->
                       config_equiv (χ, ψ1) (χ, ψ2).

Hint Constructors exp_equiv.
Hint Constructors ref_equiv.
Hint Constructors stmt_equiv.
Hint Constructors contn_equiv.
Hint Constructors map_equiv.
Hint Constructors frame_equiv.
Hint Constructors stack_equiv.
Hint Constructors config_equiv.

Ltac equiv_unfold :=
  match goal with
  | [H : exp_equiv ?f (e_val _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_var _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_hole _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_eq _ _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_if _ _ _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_acc_f _ _) ?e2 |- _] => inversion H; subst; clear H
  | [H : exp_equiv ?f (e_acc_g _ _ _) ?e2 |- _] => inversion H; subst; clear H

  | [H : ref_equiv ?f ?r1 ?r2 |- _] => inversion H; subst; clear H

  | [H : stmt_equiv ?f (s_asgn _ _) ?s |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?f (s_meth _ _ _ _) ?s |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?f (s_new _ _ _) ?s |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?f (s_stmts _ _) ?s |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?f (s_rtrn _) ?s |- _] => inversion H; subst; clear H

  | [H : contn_equiv ?f (c_hole _ _) _ |- _] => inversion H; subst; clear H
  | [H : contn_equiv ?f (c_stmt _) _ |- _] => inversion H; subst; clear H
  | [H : frame_equiv ?f ?ϕ1 ?ϕ2 |- _] =>
    notHyp (contn_equiv f (contn ϕ1) (contn ϕ2));
    notHyp (map_equiv f (vMap ϕ1) (vMap ϕ2));
    notHyp (wf_rename f);
    inversion H; subst

  | [H : stack_equiv (_ :: _) ?ψ2 |- _] => inversion H; subst; clear H
  | [H : stack_equiv nil ?ψ2 |- _] => inversion H; subst; clear H
  | [H : config_equiv ?σ1 ?σ2 |- _] => inversion H; subst; clear H

  | [H : map_equiv _ _ _ |- _] => inversion H; subst; clear H
  end.

Ltac equiv_auto :=
  match goal with
  | [|- config_equiv (?χ, ?ψ1) (?χ, ?ψ2)] => apply eq_conf
  | [|- stack_equiv nil nil] => apply eq_nil
  | [|- stack_equiv (?ϕ1 :: ?ψ1) (?ϕ2 :: ?ψ2)] => apply eq_cons
  | [|- frame_equiv _ ?ϕ1 ?ϕ2] => apply eq_frm

  | [H : contn ?ϕ = _ |- contn_equiv _ (contn ?ϕ) _] => rewrite H
  | [H : contn ?ϕ = _ |- contn_equiv _ _ (contn ?ϕ)] => rewrite H
  | [H : _ = contn ?ϕ |- contn_equiv _ (contn ?ϕ) _] => rewrite <- H
  | [H : _ = contn ?ϕ |- contn_equiv _ _ (contn ?ϕ)] => rewrite <- H
  | [|- contn_equiv _ (c_stmt _) (c_stmt _)] => apply eqc_stmt
  | [|- contn_equiv _ (c_hole _ _) (c_hole _ _)] => apply eqc_hole

  | [|- stmt_equiv _ (s_asgn _ _) (s_asgn _ _)] => apply eq_asgn
  | [Hdom : dom ?ps ?D |- stmt_equiv _ (s_meth _ _ _ ?ps) (s_meth _ _ _ _)] => apply eq_meth with (D:=D)
  | [Hdom : dom ?ps ?D |- stmt_equiv _ (s_meth _ _ _ _) (s_meth _ _ _ ?ps)] => apply eq_meth with (D:=D)
  | [|- stmt_equiv _ (s_new _ _ _) (s_new _ _ _)] => apply eq_new
  | [|- stmt_equiv _ (s_meth _ _ _ _) (s_meth _ _ _ _)] => apply eq_meth
  | [|- stmt_equiv _ (s_stmts _ _) (s_stmts _ _)] => apply eq_stmts
  | [|- stmt_equiv _ (s_rtrn _) (s_rtrn _)] => apply eq_rtrn
  end.

Lemma id_equiv_reflexive_ref :
  forall r, ref_equiv id r r.
Proof.
  intro r;
    destruct r;
    auto.
Qed.

Hint Resolve id_equiv_reflexive_ref.

Lemma bind_right_id :
  forall (A : Type)(m : A -> (option var)) , m ∘ id = m.
Proof.
  intros.
  apply functional_extensionality;
    intros a;
    unfold bind;
    simpl.
  match goal with
  | [|- _ = ?m ?a] => destruct (m a); auto
  end.
Qed.

Hint Rewrite (bind_right_id var).
Hint Rewrite (bind_right_id fld).
Hint Resolve bind_right_id.

Lemma bind_left_id :
  forall (A : Type)(m : var -> (option A)) , id ∘ m = m.
Proof.
  intros.
  apply functional_extensionality;
    intros a;
    unfold bind;
    simpl;
    auto.
Qed.

Hint Rewrite bind_left_id.
Hint Resolve bind_left_id.

Lemma id_equiv_reflexive_stmt :
  forall s, stmt_equiv id s s.
Proof.
  intro s;
    induction s;
    simpl in *;
    auto.

  - apply eq_meth; intros; auto.
    eexists; eauto.
  - apply eq_new; intros; auto.
    eexists; eauto.
Qed.

Hint Resolve id_equiv_reflexive_stmt.

Lemma id_equiv_reflexive_contn :
  forall c, contn_equiv id c c.
Proof.
  intros c;
    destruct c; auto.
Qed.

Hint Resolve id_equiv_reflexive_contn.

Lemma id_equiv_reflexive_map :
  forall m, map_equiv id m m.
Proof.
  intros;
    eauto.
Qed.

Hint Resolve id_equiv_reflexive_map.

Lemma id_equiv_reflexive_frame :
  forall ϕ, frame_equiv id ϕ ϕ.
Proof.
  intros; auto.
Qed.

Hint Resolve id_equiv_reflexive_frame.

Lemma equiv_reflexive_stack :
  forall ψ, stack_equiv ψ ψ.
Proof.
  intros ψ;
    induction ψ as [|ϕ ψ'];
    eauto.
Qed.

Hint Resolve equiv_reflexive_stack.

Lemma equiv_reflexive_config :
  forall σ, config_equiv σ σ.
Proof.
  intros; destruct σ; auto.
Qed.

Hint Resolve equiv_reflexive_config.

Ltac notin_unfold :=
  match goal with
  | [H : notin_exp (e_acc_f _ _) _ |- _] => inversion H; subst; clear H
  | [H : notin_exp (e_acc_g _ _ _) _ |- _] => inversion H; subst; clear H
  | [H : notin_exp (e_if _ _ _) _ |- _] => inversion H; subst; clear H
  | [H : notin_exp (e_eq _ _) _ |- _] => inversion H; subst; clear H
  end.

Lemma notin_self_contra :
  forall x, notin_exp (e_var x) x -> False.
Proof.
  intros.
  inversion H; subst; crush.
Qed.

Ltac notin_auto :=
  match goal with
  | [H : notin_exp (e_var ?x) ?x |- _] => apply notin_self_contra in H; crush
  end.

Lemma effective_equivalent_evaluation :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             M_wf M ->
             (exists χ ϕ ψ, σ = (χ, ϕ :: ψ)) ->
             forall σ', (forall x, mapp σ x = mapp σ' x \/
                         notin_exp e x) ->
                   (exists χ ϕ ψ, σ' = (χ, ϕ :: ψ)) ->
                   fst σ = fst σ' ->
                   M ∙ σ' ⊢ e ↪ v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    auto.

  - match goal with
    | [H : mapp ?σ ?x = Some ?v,
           Hmap : forall y, (mapp ?σ y = mapp ?σ' y \/ notin_exp ?e y) |- _ ∙ ?σ' ⊢ ?e ↪ _] =>
      destruct (Hmap x)
    end;
      [match goal with
       | [Ha : mapp ?σa ?x = Some ?v,
               Hb : mapp ?σa ?x = mapp ?σb ?x  |- _] => rewrite Hb in Ha; auto
       end
      |notin_auto].

  - apply v_f_heap with (α:=α)(o:=o); auto.
    apply IHHeval; intros; auto.
    match goal with
    | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_acc_f ?e ?f) y
                    |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e ?x] =>
      destruct (Hmapp x); repeat notin_unfold; auto
    end.
    destruct σ as [χ' ψ1];
      destruct σ' as [χ ψ2];
      simpl in *;
      subst.
    repeat map_rewrite; simpl in *; auto.

  - apply v_f_ghost with (α:=α)(o:=o)(x:=x)(e':=e')(v:=v)(C:=C);
      auto.
    + apply IHHeval1; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_acc_g ?e _ _) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + destruct σ as [χ' ψ1];
        destruct σ' as [χ ψ2];
        simpl in *;
        subst.
      repeat map_rewrite; simpl in *; auto.
    + apply IHHeval2; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_acc_g _ _ ?e) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + apply IHHeval3; intros; auto.
      * destruct σ as [χ' ψ];
          destruct σ' as [χ ψ'];
          simpl in *;
          subst.
        repeat destruct_exists;
          repeat match goal with
                 | [H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
                 end;
          repeat eexists.
      * destruct (eq_dec x0 this) as [Heq1|Hneq1];
          [subst|].
        destruct σ as [χ' ψ1];
          destruct σ' as [χ ψ2];
          simpl in *;
          subst.
        repeat rewrite map_update_σ; auto; simpl;
          repeat destruct_exists;
          repeat match goal with
                 | [H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
                 end;
          repeat eexists.
        destruct (eq_dec x0 x) as [Heq2|Hneq2];
          [subst|].
        destruct σ as [χ' ψ1];
          destruct σ' as [χ ψ2];
          simpl in *;
          subst.
        repeat match goal with
               | [ψ0 : stack,
                       χ0 : heap,
                            Hex : exists χ' ϕ' ψ', (?χ0, ?ψ0) = (χ', ϕ'::ψ') |-_] =>
                 let ϕ := fresh "ϕ" in
                 let ψ := fresh "ψ" in
                 let χ := fresh "χ" in
                 let Htmp := fresh in
                 destruct Hex as [χ Htmp];
                   destruct Htmp as [ϕ Htmp];
                   destruct Htmp as [ψ Htmp];
                   inversion Htmp;
                   subst;
                   clear Htmp
               end.
        repeat map_rewrite; simpl in *.
        repeat update_auto.
        rewrite eqb_refl; auto.
        right.
        match goal with
        | [HMwf : M_wf ?M |- _] =>
          inversion HMwf; subst
        end.
        match goal with
        | [HCwf : forall C0 CDef0, ?M C0 = Some CDef0 -> cls_wf CDef0,
             HCDef : ?M _ = Some ?C,
             Hghost : c_g_fields ?C _ = _ |- _] =>
          apply HCwf in HCDef
        end.
        match goal with
        | [HCwf : cls_wf ?C |- _] => inversion HCwf; subst
        end.
        match goal with
        | [Hgwf : gFields_wf (c_g_fields ?C) |- _] => inversion Hgwf; subst
        end.
        match goal with
        | [Hnotin : forall g x' e', c_g_fields ?C g = Some (x', e') ->
                               forall y, y <> x' ->
                                    y <> this ->
                                    notin_exp e' y,
             Hghost : c_g_fields ?C ?f = Some (?x, ?e),
             Hneq1 : ?x0 <> ?x,
             Hneq2 : ?x0 <> this |- _] =>
          apply Hnotin with (y:=x0) in Hghost; auto
        end.
      * repeat destruct_exists; subst;
          repeat eexists.

  - apply v_if_true; auto.
    + apply IHHeval1; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_if ?e1 ?e2 ?e3) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e1 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + apply IHHeval2; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_if ?e1 ?e2 ?e3) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e2 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.

  - apply v_if_false; auto.
    + apply IHHeval1; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_if ?e1 ?e2 ?e3) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e1 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + apply IHHeval2; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_if ?e1 ?e2 ?e3) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e3 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.

  - apply v_equals with (v:=v).
    + apply IHHeval1; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_eq ?e1 ?e2) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e1 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + apply IHHeval2; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_eq ?e1 ?e2) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e2 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.

  - apply v_nequals with (v1:=v1)(v2:=v2); auto.
    + apply IHHeval1; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_eq ?e1 ?e2) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e1 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
    + apply IHHeval2; intros; auto.
      match goal with
      | [Hmapp : forall y, mapp ?σa y = mapp ?σb y \/ notin_exp (e_eq ?e1 ?e2) y
                      |- mapp ?σa ?x = mapp ?σb ?x \/ notin_exp ?e2 ?x] =>
        destruct (Hmapp x); repeat notin_unfold; auto
      end.
Qed.

Lemma equivalent_evaluation :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             M_wf M ->
             forall χ ϕ ψ, σ = (χ, ϕ :: ψ) ->
             forall f ϕ' ψ' e', exp_equiv f e e' ->
                           frame_equiv f ϕ ϕ' ->
                           M ∙ (χ, ϕ'::ψ') ⊢ e' ↪ v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    auto;
    repeat equiv_unfold;
    eauto.

  - apply v_var; repeat map_rewrite; simpl.
    match goal with
    | [Hm1 : ?m1 ?x1 = Some ?v,
             Hf : ?f ?x1 = Some ?x2,
                  Hmeq : ?m1 = ?f ∘ ?m2|- ?m2 ?x2 = Some ?v] =>
      apply equal_f with (x0:=x1) in Hmeq
    (* figure out a better way to do this. 
       x0 is confusing and potentially fragile, 
       and x is conflicting with the outer x *)
    end.
    simpl in *.
    match goal with
    | [H : ?f ?x = Some ?y |- context[?m ?y]] =>  rewrite H in *
    end.
    crush.

  - apply v_f_ghost with (α:=α)(o:=o)(x:=x)(e':=e')(v:=v)(C:=C);
      eauto.
    apply effective_equivalent_evaluation with (σ:=update_σ_map (update_σ_map (χ, ϕ::ψ) x v) this (v_addr α));
      auto.
    + repeat eexists.
    + intros.
      destruct (eq_dec x0 this) as [Heq1|Hneq1];
        [subst|].
      repeat rewrite map_update_σ; auto; simpl;
        repeat destruct_exists;
        repeat match goal with
               | [H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
               end;
        repeat eexists.
      destruct (eq_dec x0 x) as [Heq2|Hneq2];
        [subst|].
      repeat map_rewrite; simpl in *.
      repeat update_auto.
      rewrite eqb_refl; auto.
      right.
      match goal with
      | [HMwf : M_wf ?M |- _] =>
        inversion HMwf; subst
      end.
      match goal with
      | [HCwf : forall C0 CDef0, ?M C0 = Some CDef0 -> cls_wf CDef0,
           HCDef : ?M _ = Some ?C,
           Hghost : c_g_fields ?C _ = _ |- _] =>
        apply HCwf in HCDef
      end.
      match goal with
      | [HCwf : cls_wf ?C |- _] => inversion HCwf; subst
      end.
      match goal with
      | [Hgwf : gFields_wf (c_g_fields ?C) |- _] => inversion Hgwf; subst
      end.
      match goal with
      | [Hnotin : forall g x' e', c_g_fields ?C g = Some (x', e') ->
                             forall y, y <> x' ->
                                  y <> this ->
                                  notin_exp e' y,
           Hghost : c_g_fields ?C ?f = Some (?x, ?e),
           Hneq1 : ?x0 <> ?x,
           Hneq2 : ?x0 <> this |- _] =>
        apply Hnotin with (y:=x0) in Hghost; auto
      end.

    + repeat eexists.

Qed.

Lemma rename_wf_not_this :
  forall f, wf_rename f ->
       forall x y, f x = Some y ->
              x <> this ->
              y <> this.
Proof.
  intros f Hwf x y;
    intros.
  unfold wf_rename in *.
  andDestruct.
  intros Hcontra; subst.
  match goal with
  | [H1_1 : one_to_one ?f,
            Ha : ?f this = Some ?z,
                 Hb : ?f ?y = Some ?z |-_] => eapply H1_1 in Hb; eauto
  end.
Qed.

Lemma equivalent_interpretation_x :
  forall x χ ϕ ψ v, ⌊ x ⌋ (χ, ϕ::ψ) ≜ v ->
               forall f x' ϕ' ψ', f x = Some x' ->
                             frame_equiv f ϕ ϕ' ->
                             ⌊ x' ⌋ (χ, ϕ'::ψ') ≜ v.
Proof.
  intros x χ ϕ ψ v Hint f x' ϕ' ψ';
    inversion Hint;
    subst;
    intros.
  simpl in *.
  match goal with
  | [H : _ :: _ = _ :: _ |-_] => inversion H; subst
  end.
  repeat equiv_unfold.
  match goal with
  | [|- ⌊ _ ⌋ (_, ?ϕ' :: ?ψ') ≜ _] => apply int_x with (ϕ:=ϕ')(ψ:=ψ'); auto
  end.
  match goal with
  | [Hmap : ?m1 = ?f ∘ ?m2,
            Hm1 : ?m1 ?x = ?o,
                  Hf : ?f ?x = Some ?x'
     |- ?m2 ?x' = ?o] => apply equal_f with (x0:=x) in Hmap;
                         simpl in *;
                         rewrite Hf in Hmap;
                         rewrite Hm1 in Hmap;
                         auto
  end.
Qed.

Lemma equivalent_interpretation_equal :
  forall x χ ϕ ψ v, ⌊ x ⌋ (χ, ϕ::ψ) ≜ v ->
               forall f x' ϕ' ψ' v', f x = Some x' ->
                                frame_equiv f ϕ ϕ' ->
                                ⌊ x' ⌋ (χ, ϕ'::ψ') ≜ v' ->
                                v' = v.
Proof.
  intros.
  match goal with
  | [H1 : ⌊ ?x1 ⌋ ?σ1 ≜ ?v1,
          H2 : ⌊ ?x2 ⌋ ?σ2 ≜ ?v2 |- _] =>
    inversion H1; inversion H2; subst;
      simpl in *;
      crush
  end.
  repeat equiv_unfold.
  match goal with
  | [H1 : ?m1 ?x = Some _,
          H2 : ?m2 _ = Some _,
               Hmap : ?m1 = _,
                      Hf : ?f ?x = _ |- _] =>
    rewrite Hmap in H1; simpl in H1;
      rewrite Hf in H1; crush
  end.
Qed.

Lemma empty_is_empty :
  forall {A B : Type} `{Eq A} (a : A)(b : B),
    empty a <> Some b.
Proof.
  intros;
    unfold empty;
    unfold t_empty;
    crush.
Qed.

Lemma domain_transitive :
  forall {A B C : Type} `{Eq A} (m1 : partial_map A B) D,
    dom m1 D ->
    forall (m2 : partial_map A C),
      dom m2 D ->
      forall D', dom m1 D' ->
            dom m2 D'.
Proof.
  intros.
  unfold dom in *;
    andDestruct.
  repeat split; intros;
    auto.

  match goal with
  | [H : ?m2 ?a = Some ?b,
         Ha : forall a' b', ?m2 a' = Some b' -> In a' ?D',
       Hb : forall a'', In a'' ?D' -> exists b'', ?m1 a'' = Some b'',
       Hc : forall a''', In a''' ?D' -> exists b''', ?m2 a''' = Some b''' |- _] =>
    apply Ha, Hb in H; destruct_exists; eauto
  end.

  match goal with
  | [Hin : In ?a ?D,
           H : forall a', In a' ?D -> ?P  |- exists _, ?m2 ?a = Some _] =>
    apply H in Hin; destruct_exists; eauto
  end.
Qed.

Lemma equivalent_class_of :
  forall x χ ϕ ψ C, classOf x (χ, ϕ::ψ) C ->
               forall f y ϕ' ψ',
                 f x = Some y ->
                 frame_equiv f ϕ ϕ' ->
                 classOf y (χ, ϕ'::ψ') C.
Proof.
  intros.
  match goal with
  |[H : classOf _ _ _ |- _] => inversion H; subst
  end.
  equiv_unfold.
  eapply cls_of; eauto.
  eapply equivalent_interpretation_x; eauto.
Qed.

Lemma equivalent_class_of_this :
  forall σ C, classOf this σ C ->
         forall σ', config_equiv σ σ' ->
               classOf this σ' C.
Proof.
  intros.
  repeat equiv_unfold.
  match goal with
  | [H : stack_equiv _ ?ψ,
     Hcls : classOf _ _ _ |- classOf _ (_, ?ψ) _] =>
    let ψ' := fresh "ψ" in
    let ϕ := fresh "ϕ" in
    destruct ψ as [|ϕ ψ'];
      inversion H; subst;
        inversion Hcls; subst;
          simpl in *;
          [match goal with
           | [Hint : ⌊ _ ⌋ (_, nil) ≜ _ |- _] =>
             inversion Hint; subst; simpl; crush
           end|]
  end.
  match goal with
  | [H : classOf this (_, ?ϕ1::?ψ1) _,
         Heq : frame_equiv ?f ?ϕ1 ?ϕ2 |- classOf this (_, ?ϕ2::_) _] =>
    apply equivalent_class_of with (x:=this)(ϕ:=ϕ1)(ψ:=ψ1)(f:=f)
  end; auto.
  repeat equiv_unfold.
  unfold wf_rename in *; andDestruct; auto.
Qed.

Hint Resolve equivalent_class_of_this.

Lemma equivalent_frames_with_equivalent_maps :
  forall f ϕ1 ϕ2, frame_equiv f ϕ1 ϕ2 ->
             (vMap ϕ1) = f ∘ (vMap ϕ2).
Proof.
  intros;
    repeat equiv_unfold; auto.
Qed.

Lemma bind_dom :
  forall {A : Type}`{Eq A}(m1 : partial_map A var)(m2 : partial_map var var),
    (forall a x, m1 a = Some x -> exists y, m2 x = Some y) ->
    forall d, dom m1 d ->
         dom (m1 ∘ m2) d.
Proof.
  intros A HeqA m1 m2;
    intros.
  unfold bind; simpl.
  unfold dom in *;
    repeat split;
    intros;
    andDestruct;
    auto.
  destruct (partial_map_dec a m1) as [|Hnone];
    [destruct_exists; eauto|rewrite Hnone in *; crush].
  destruct (partial_map_dec a m1) as [|Hnone];
    [destruct_exists|rewrite Hnone in *; crush].
  - match goal with
    | [H : ?m ?a = Some ?x |- _] => rewrite H; eauto
    end.
  - match goal with
    | [Ha : forall a', In a' ?d -> _,
         Hb : In ?a ?d |-_] => apply Ha in Hb; destruct_exists; crush
    end.
Qed.

Lemma equivalent_reduction_exists :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             M_wf M ->
             forall σ1', config_equiv σ1 σ1' ->
                    exists σ2', M ∙ σ1' ⤳ σ2'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    repeat equiv_unfold.

  - match goal with
    | [H1 : contn _ = c_stmt _ |-_] => rewrite H1 in *
    end;
      repeat equiv_unfold.
    remember (frm (vMap ϕ2) (c_hole x2 s2')) as ϕ2'.
    remember (frm (update this (v_addr α) (compose (ps ∘ f) (vMap ϕ2))) (c_stmt s)) as ϕ'.
    exists (χ, ϕ' :: ϕ2' :: ψ0).
    eapply r_mth
      with
        (s:=s)(C:=C)(o:=o)(α:=α)(zs:=zs)
        (x:=x2)(y:=y2)(m:=m)(ϕ:=ϕ2)(s':=s2')
        (ps:=fun x => bind (ps x) f);
      eauto.
    + eapply rename_wf_not_this; eauto.
    + eapply equivalent_interpretation_x; eauto.
    + apply bind_dom; auto.

  - match goal with
    | [H : contn _ = c_stmt _ |-_] => rewrite H in *
    | [H : c_stmt _ = contn _ |-_] => rewrite <- H in *
    end;
      repeat equiv_unfold.
    remember (update_σ_map (χ, ϕ2::ψ0) y1 v) as σ'.
    exists σ'.
    apply r_vAssgn
      with
        (ϕ:=ϕ2)(ψ:=ψ0)(x:=y1)(v:=v)
        (y:=y0)(f:=f)(s:=s2')(χ:=χ)
        (α:=α)(o:=o)(C:=C); auto.
    + match goal with
      | [Hwf : wf_rename ?f,
               H : ?f ?x = Some ?x' |- ?x' <> this] =>
        intro Hcontra; subst; unfold wf_rename in Hwf; andDestruct;
          match goal with
          | [H1_1 : one_to_one ?f,
                    Hneq : ?x <> this,
                           Hmap : ?f ?x = Some this |- _] =>
            unfold one_to_one in H1_1;
              rewrite (H1_1 x this this Hmap) in Hneq; crush
          end
      end.
    + eapply equivalent_interpretation_x; eauto.
    + match goal with
      | [_ : wf_rename ?f' |- _] =>
        eapply equivalent_class_of with (f:=f'); [eauto| |]
      end.
      unfold wf_rename in *;
        andDestruct; auto.
      repeat equiv_auto; auto.
    + match goal with
      | [_ : wf_rename ?f',
         _ : ?f' ?x' = Some ?y  |- classOf ?y _ _] =>
        eapply equivalent_class_of with (x:=x')(f:=f'); [eauto|auto|repeat equiv_auto; auto]
      end.

  - match goal with
    | [H : contn _ = c_stmt _ |-_] => rewrite H in *
    | [H : c_stmt _ = contn _ |-_] => rewrite <- H in *
    end;
      repeat equiv_unfold.
    remember (new (cname o) (update f v (flds o)) (meths o)) as o'.
    remember (update α o' χ) as χ'.
    remember (frm (vMap ϕ2) (c_stmt s2')) as ϕ'.
    exists (χ', ϕ'::ψ0).
    apply r_fAssgn
      with
        (ϕ:=ϕ2)(ϕ':=ϕ')(x:=y0)(y:=y1)
        (f:=f)(s:=s2')(ψ:=ψ0)(χ:=χ)(v:=v)
        (χ':=χ')(α:=α)(o:=o)(o':=o')(C:=C);
      auto.
    + eapply equivalent_interpretation_x; eauto.
    + eapply equivalent_interpretation_x; eauto.
    + match goal with
      | [_ : wf_rename ?f' |- _] =>
        eapply equivalent_class_of with (f:=f'); [eauto| |]
      end.
      unfold wf_rename in *;
        andDestruct; auto.
      repeat equiv_auto; auto.
    + match goal with
      | [_ : wf_rename ?f',
         _ : ?f' ?x' = Some ?y  |- classOf ?y _ _] =>
        eapply equivalent_class_of with (x:=x')(f:=f'); [eauto|auto|repeat equiv_auto; auto]
      end.

  - match goal with
    | [H : contn _ = c_stmt _ |-_] => rewrite H in *
    | [H : c_stmt _ = contn _ |-_] => rewrite <- H in *
    end;
      repeat equiv_unfold.
    remember (new C (compose (fun x : fld => bind (fMap x) f) (vMap ϕ2)) (c_meths CDef)) as o.
    remember (frm (update x2 (v_addr α) (vMap ϕ2)) (c_stmt s2')) as ϕ'.
    remember (update α o χ, ϕ'::ψ0) as σ'.
    exists σ'.
    apply r_new
        with
          (χ:=χ)(ψ:=ψ0)(ϕ:=ϕ2)(ϕ':=ϕ')
          (α:=α)(x:=x2)(C:=C)(s:=s2')
          (fMap:=fun x => bind (fMap x) f)
          (o:=o)(CDef:=CDef);
      auto.
    + match goal with
      | [Hwf : wf_rename ?f,
               H : ?f ?x = Some ?x' |- ?x' <> this] =>
        intro Hcontra; subst; unfold wf_rename in Hwf; andDestruct;
          match goal with
          | [H1_1 : one_to_one ?f,
                    Hneq : ?x <> this,
                           Hmap : ?f ?x = Some this |- _] =>
            unfold one_to_one in H1_1;
              rewrite (H1_1 x this this Hmap) in Hneq; crush
          end
      end.
    + apply bind_dom; auto.
    + intros.
      match goal with
      | [H : bind (?m ?f0) ?f = Some ?x,
             Ha : forall f' x', ?m f' = Some x' -> exists v, vMap ?ϕ x' = Some v,
           Hb : vMap ?ϕ = _ |- _] =>
        unfold bind in H; simpl in H;
          let Hmap := fresh in 
          destruct (partial_map_dec f0 m) as [|Hmap];
            try destruct_exists;
            [|rewrite Hmap in H; crush];
            match goal with
            | [Hc : m f0 = Some ?y |- _] =>
              rewrite Hc in H;
                apply Ha in Hc;
                destruct_exists;
                rewrite Hb in Hc;
                simpl in Hc;
                rewrite H in Hc;
                eexists;
                eauto
            end
      end.

  - repeat match goal with
           | [H : contn _ = _ |-_] => rewrite H in *
           | [H : c_stmt _ = contn _ |-_] => rewrite <- H in *
           end;
      repeat equiv_unfold.
    remember (update_ϕ_contn (update_ϕ_map ϕ0 x2 α) (c_stmt s2)) as ϕ''.
    exists (χ, ϕ''::ψ2).
    apply r_ret1
      with
        (ϕ:=ϕ2)(ϕ':=ϕ0)(y:=x2)(x:=x0)(α:=α)(s:=s2);
      auto.
    + match goal with
      | [Hwf : wf_rename ?f,
               H : ?f ?x = Some ?x' |- ?x' <> this] =>
        intro Hcontra; subst; unfold wf_rename in Hwf; andDestruct;
          match goal with
          | [H1_1 : one_to_one ?f,
                    Hneq : ?x <> this,
                           Hmap : ?f ?x = Some this |- _] =>
            unfold one_to_one in H1_1;
              rewrite (H1_1 x this this Hmap) in Hneq; crush
          end
      end.
    + eapply equivalent_interpretation_x; eauto.

  -  repeat match goal with
           | [H : contn _ = _ |-_] => rewrite H in *
           | [H : c_stmt _ = contn _ |-_] => rewrite <- H in *
           end;
      repeat equiv_unfold.
    remember (update_ϕ_contn (update_ϕ_map ϕ0 x2 α) (c_stmt s2)) as ϕ''.
    exists (χ, ϕ''::ψ2).
    apply r_ret2
      with
        (ϕ:=ϕ2)(ϕ':=ϕ0)(y:=x2)(x:=x0)(α:=α)(s:=s2)(s':=s2');
      auto.
    + match goal with
      | [Hwf : wf_rename ?f,
               H : ?f ?x = Some ?x' |- ?x' <> this] =>
        intro Hcontra; subst; unfold wf_rename in Hwf; andDestruct;
          match goal with
          | [H1_1 : one_to_one ?f,
                    Hneq : ?x <> this,
                           Hmap : ?f ?x = Some this |- _] =>
            unfold one_to_one in H1_1;
              rewrite (H1_1 x this this Hmap) in Hneq; crush
          end
      end.
    + eapply equivalent_interpretation_x; eauto.
Qed.

Lemma compose_is_bind :
  forall {A B C : Type}`{Eq A}`{Eq B}
    (m1 : partial_map A B)
    (m2 : partial_map B C), compose m1 m2 = (fun x => bind (m1 x) m2).
Proof.
  intros; auto.
Qed.

Lemma bind_assoc :
  forall {A B C D : Type}`{Eq A}`{Eq B}`{Eq C}
    (m1 : partial_map A B) (m2 : partial_map B C) (m3 : partial_map C D),
    (fun x => bind ((fun y => bind (m1 y) m2) x) m3) = (fun x => bind (m1 x) (fun y => bind (m2 y) m3)).
Proof.
  intros.
  unfold bind; simpl.
  apply functional_extensionality;
    intros a.
  match goal with
  | [m1 : partial_map ?A _,
          a : ?A |- _] => destruct (m1 a); auto
  end.
Qed.

Hint Resolve bind_assoc.

Lemma bind_update :
  forall {A B C : Type}`{Eq A}`{Eq B}
    (m1 : partial_map A B)(m2 : partial_map B C) a b,
    m1 a = Some b ->
    one_to_one m1 ->
    forall c, (update a c (fun a' => bind (m1 a') m2)) = (fun a' => bind (m1 a') (update b c m2)).
Proof.
  intros.
  repeat map_rewrite.
  apply functional_extensionality;
    intros a'.
  match goal with
  | [H : ?m ?a = Some ?b |- context[eqb ?a' ?a]] =>
    destruct (eq_dec a' a);
      subst;
      repeat eq_auto;
      simpl;
      [rewrite H;
      eq_auto|]
  end.
  destruct (partial_map_dec a' m1); [destruct_exists; crush|crush].
  assert (Hneq : x <> b);
    [intro Hcontra; subst; unfold one_to_one in *|].
  contradiction n.
  eapply H2; eauto.
  apply neq_eqb in Hneq;
    rewrite Hneq; auto.
Qed.

Lemma equivalent_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             M_wf M ->
             forall σ1', config_equiv σ1 σ1' ->
                    forall σ2', M ∙ σ1' ⤳ σ2' ->
                           config_equiv σ2 σ2'.
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    repeat equiv_unfold;
    repeat match goal with
           | [H : contn _ = _ |-_] => rewrite H in *
           | [H : _ = contn _ |-_] => rewrite <- H in *
           end;
    repeat equiv_unfold;
    repeat equiv_auto.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    match goal with
    | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
            H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                 Hmap : ?f ?x1 = Some ?x2 |- _ ] => 
      apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
        inversion H2; subst
    end.
    repeat match goal with
           | [H1 : ?χ ?α = _,
                   H2 : ?χ ?α = _ |- _] => rewrite H1 in H2; inversion H2; subst
           end.

    apply eq_cons with (f:=id); simpl.
    
    + apply eq_frm; simpl; auto.
      repeat rewrite compose_is_bind.
      match goal with
      | [H : ?m = _ |- context[bind (_ _) ?m]] => rewrite H
      end.
      rewrite <- bind_assoc;
        unfold bind; simpl; auto.

    + apply eq_cons with (f:=f); simpl; auto.
      repeat equiv_auto; simpl; auto.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    match goal with
    | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
            H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                 Hmap : ?f ?x1 = Some ?x2 |- _ ] =>
      apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
        inversion H2; subst
    end.
    repeat match goal with
           | [H1 : ?χ ?α = _,
                   H2 : ?χ ?α = _ |- _] => rewrite H1 in H2; inversion H2; subst
           end.
    repeat map_rewrite; simpl.
    equiv_auto.
    match goal with
    | [_ : wf_rename ?f' |- stack_equiv _ _] => apply eq_cons with (f:=f'); auto
    end.
    repeat equiv_auto; auto.
    + simpl in *.
      repeat equiv_auto; auto.
    + simpl in *.
      apply eq_map; auto.
      * match goal with
        | [Hmap : ?m = _ |- context[?m]] =>
          rewrite Hmap
        end.
        match goal with
        | [H : ?f ?x = Some ?x' |- context[(fun a' => bind (?f a') (update ?x' _ _))]] =>
          rewrite <- bind_update with (a:=x); auto
        end.
      * intros.
        repeat map_rewrite.
        match goal with
        | [H : context[eqb ?x ?y] |- exists _, _ ?x = Some _] =>
          destruct (eq_dec x y) as [|Hneq];
            [subst|];
            eq_auto;
            [eexists;
             eauto
            |eauto]
        end.
      * intros.
        repeat map_rewrite.
        match goal with
        | [H : context[eqb ?x ?y] |- exists _, _ = Some ?x] =>
          destruct (eq_dec x y) as [|Hneq];
            [subst|];
            eq_auto;
            [eexists;
             eauto
            |eauto]
        end.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    match goal with
    | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
            H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                 Hmap : ?f ?x1 = Some ?x2 |- _ ] =>
      apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
        inversion H2; subst
    end.
    repeat match goal with
           | [H1 : ?χ ?α = _,
                   H2 : ?χ ?α = _ |- _] => rewrite H1 in H2; inversion H2; subst
           end.
    match goal with
    | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
            H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                 Hmap : ?f ?x1 = Some ?x2 |- _ ] =>
      apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
        inversion H2; subst
    end.
    repeat map_rewrite; simpl.
    equiv_auto.
    match goal with
    | [_ : wf_rename ?f' |- stack_equiv _ _] => apply eq_cons with (f:=f'); auto
    end.
    repeat equiv_auto; auto.
    + simpl in *.
      repeat equiv_auto; auto.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    repeat match goal with
           | [H1 : ?m ?x = _,
                   H2 : ?m ?x = _ |- _] => rewrite H1 in H2; inversion H2; subst
           end.
    match goal with
    | [H1 : fresh_χ ?χ ?a1,
            H2 : fresh_χ ?χ ?a2 |- _] =>
      apply fresh_heap_unique with (α1:=a2) in H1;
        auto;
        subst
    end.
    repeat rewrite compose_is_bind.
    match goal with
    | [Hmap : ?m = (fun _ => bind _ _) |- context[?m]] => rewrite Hmap
    end.
    rewrite <- bind_assoc.
    apply eq_conf.
    apply eq_cons with (f:=f);
      auto.
    equiv_auto; simpl;
      repeat equiv_auto;
      auto.
    apply eq_map; auto.
    * rewrite <- bind_update with (a:=x); auto. 
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ ?x = Some _] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.
      match goal with
      | [H : (match ?f ?x with | Some _ => _ | None => None end = Some _) |- exists _, ?f ?x = Some _]  =>
        destruct (f x);
          [eexists; eauto|crush]
      end.
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ = Some ?x] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    match goal with
    | [H : c_hole _ _ = c_hole _ _ |- _] => inversion H; subst
    end.
    apply eq_cons with (f:=f0); auto.
    repeat equiv_auto; simpl; auto.
    apply eq_map; auto.
    * match goal with
      | [Hmap : ?m = (fun _ => bind _ _) |- context[?m]] => rewrite Hmap
      end.
      match goal with
      | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
              H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                   Hmap : ?f ?x1 = Some ?x2 |- _ ] =>
        apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
          inversion H2; subst
      end.
      apply bind_update; auto.
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ ?x = Some _] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ = Some ?x] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.

  - match goal with
    | [Hred : _ ∙ _ ⤳ _ |- _] => inversion Hred; subst; try solve [crush]
    end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    repeat equiv_auto; eauto;
      repeat equiv_auto; eauto;
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end;
        repeat match goal with
               | [H : contn _ = _ |-_] => rewrite H in *
               | [H : _ = contn _ |-_] => rewrite <- H in *
               | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
               end;
        auto.
    match goal with
    | [H : c_hole _ _ = c_hole _ _ |- _] => inversion H; subst
    end.
    apply eq_cons with (f:=f0); auto.
    repeat equiv_auto; simpl; auto.
    apply eq_map; auto.
    * match goal with
      | [Hmap : ?m = (fun _ => bind _ _) |- context[?m]] => rewrite Hmap
      end.
      match goal with
      | [H1 : ⌊ ?x1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
              H2 : ⌊ ?x2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2,
                   Hmap : ?f ?x1 = Some ?x2 |- _ ] =>
        apply (equivalent_interpretation_equal x1  χ ϕ1 ψ1 v1 H1 f) in H2; auto;
          inversion H2; subst
      end.
      apply bind_update; auto.
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ ?x = Some _] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.
    * intros.
      repeat map_rewrite.
      match goal with
      | [H : context[eqb ?x ?y] |- exists _, _ = Some ?x] =>
        destruct (eq_dec x y) as [|Hneq];
          [subst|];
          eq_auto;
          [eexists;
           eauto
          |eauto]
      end.    
Qed.

Hint Resolve equivalent_reduction.

Lemma ref_equiv_sym :
  forall f r1 r2, ref_equiv f r1 r2 ->
             forall f', inv f f' ->
                   ref_equiv f' r2 r1.
Proof.
  intros f r1 r2 Heq;
    inversion Heq;
    intros;
    subst.

  - unfold inv in *;
      andDestruct;
      eauto.

  - unfold inv in *;
      andDestruct;
      eauto.
Qed.

Hint Resolve ref_equiv_sym.

Lemma exp_equiv_sym :
  forall f e1 e2, exp_equiv f e1 e2 ->
             forall f', inv f f' ->
                   exp_equiv f' e2 e1.
Proof.
  intros f e1 e2 Heq;
    induction Heq;
    intros;
    subst;
    auto.

  unfold inv in *;
    andDestruct;
    eauto.

Qed.

Hint Resolve exp_equiv_sym.

(*Lemma bind_inverse :
  forall {A B C : Type}`{Eq A}`{Eq B}`{Eq C}
    (f : partial_map B C)(f' : partial_map C B),
    inv f f' ->
    forall {C : Type}`{Eq C} (m : partial_map A B),
      (forall a b, m a = Some b -> exists c, f b = Some c) ->
      (fun x => bind ((fun y => bind (m y) f) x) f') = m.
Proof.
  intros.
  unfold bind; simpl.
  apply functional_extensionality;
    intros a.
  match goal with
  | [|- _ = ?m ?a] =>
    destruct (partial_map_dec a m) as [Hsome|Hnone];
      [destruct_exists|rewrite Hnone; auto]
  end.
  match goal with
  | [H : ?m ?a = Some ?b,
         Hmap : forall a' b', ?m a' = Some b' -> _ |- _ = ?m ?a] =>
    rewrite H; apply Hmap in H;
      destruct_exists
  end.
  unfold inv in *;
    andDestruct.
  crush.
Qed.*)

Lemma stmt_equiv_sym :
  forall f s1 s2, stmt_equiv f s1 s2 ->
             forall f', inv f f' ->
                   stmt_equiv f' s2 s1.
Proof.
  intros f s1 s2 Heq;
    induction Heq;
    intros;
    subst;
    eauto.

  - repeat equiv_auto;
      intros;
      try solve [unfold inv in *;
                 andDestruct;
                 intros;
                 eauto].
    + unfold inv in *; andDestruct.
      match goal with
      | [H : bind (?m ?p) ?f = Some ?x |- _] =>
        destruct (partial_map_dec p m) as [Hsome|Hnone];
          [destruct_exists; unfold bind in *; simpl in *
          |rewrite Hnone in H; crush];
          match goal with
          | [Ha : m p = Some ?b |- _] => rewrite Ha in H
          end
      end.
      match goal with
      | [Hmap : ?f ?x1 = Some ?x2  |- exists y, ?f' ?x2 = Some y] =>
        exists x1; auto
      end.
    + symmetry; eapply bind_inverse_right; intros; eauto.

  - repeat equiv_auto;
      intros;
      try solve [unfold inv in *;
                 andDestruct;
                 intros;
                 eauto].
    + unfold inv in *; andDestruct.
      match goal with
      | [H : bind (?m ?p) ?f = Some ?x |- _] =>
        destruct (partial_map_dec p m) as [Hsome|Hnone];
          [destruct_exists; unfold bind in *; simpl in *
          |rewrite Hnone in H; crush];
          match goal with
          | [Ha : m p = Some ?b |- _] => rewrite Ha in H
          end
      end.
      match goal with
      | [Hmap : ?f ?x1 = Some ?x2  |- exists y, ?f' ?x2 = Some y] =>
        exists x1; auto
      end.
    + symmetry; eapply bind_inverse_right; intros; eauto.

  - repeat equiv_auto;
      intros;
      try solve [unfold inv in *;
                 andDestruct;
                 intros;
                 eauto].

Qed.

Hint Resolve stmt_equiv_sym.

Lemma map_equiv_sym :
  forall f m1 m2, map_equiv f m1 m2 ->
             forall f', inv f f' ->
                   map_equiv f' m2 m1.
Proof.
  intros f m1 m2 Heq;
    inversion Heq;
    subst;
    intros;
    apply eq_map.

  - symmetry.
    apply functional_extensionality;
      intros x.
    match goal with
    | [_ : inv ?f ?f'|- context[?f' ?x]] =>
      let Hnone := fresh in 
      destruct (partial_map_dec x f') as [|Hnone];
        [|rewrite Hnone; simpl]
    end.
    + destruct_exists.
      match goal with
      | [H : ?f' ?x = Some ?y |- context[?f' ?x]] =>
        rewrite H; simpl
      end.
      unfold inv in *; andDestruct.
      match goal with
      | [Ha : ?f' ?x = Some ?y,
              Hb : forall a' b', ?f' b' = Some a' -> ?f a' = Some b' |- _] =>
        apply Hb in Ha;
          rewrite Ha;
          auto
      end.
        
    + simpl.
      match goal with
      | [|- _ = ?m ?x] =>
        let Hnone := fresh in 
        destruct (partial_map_dec x m) as [|Hnone];
          [|rewrite Hnone; auto]
      end.
      destruct_exists.
      match goal with
      | [Ha : forall x' α', ?m x' = Some α' -> exists y', ?f y' = Some x',
           Hb : ?m ?x = Some ?y |- _] => apply Ha in Hb; destruct_exists
      end.
      unfold inv in *; andDestruct.
      match goal with
      | [Ha : forall x' y', ?f x' = Some y' -> ?f' y' = Some x',
           Hb : ?f ?x = Some ?y,
           Hc : ?f' ?y = None |- _] => apply Ha in Hb; crush
      end.

  - intros.
    unfold inv in *; andDestruct.
      match goal with
      | [Ha : forall x' α', ?m x' = Some α' -> exists y', ?f y' = Some x',
           Hb : ?m ?x = Some ?y |- _] => apply Ha in Hb; destruct_exists
      end.
    match goal with
    | [Ha : forall x' y', ?f x' = Some y' -> ?f' y' = Some x',
         Hb : ?f ?x = Some ?y |- _] => apply Ha in Hb; eauto
    end.

  - intros.
    match goal with
    | [Ha : bind (?f ?x) ?m = Some ?α |- _] =>
      let Hnone := fresh in 
      destruct (partial_map_dec x f) as [|Hnone];
        [unfold inv in *; andDestruct; destruct_exists
        |rewrite Hnone in Ha; simpl in Ha; crush]
    end.
    match goal with
    | [Ha : forall x' y', ?f x' = Some y' -> ?f' y' = Some x',
         Hb : ?f ?x = Some ?y |- exists _, ?f' _ = Some ?x ] => apply Ha in Hb; eauto
    end.

  - unfold wf_rename in *; andDestruct;
      split.
    + eapply inv_one_to_one; eauto.
    + unfold inv in *; andDestruct.
      auto.
Qed.

Hint Resolve map_equiv_sym.

Lemma contn_equiv_sym :
  forall f c1 c2, contn_equiv f c1 c2 ->
             forall f', inv f f' ->
                   contn_equiv f' c2 c1.
Proof.
  intros; eauto.
  match goal with
  | [H : contn_equiv _ _ _ |- _] => inversion H; subst
  end.

  - equiv_unfold;
      equiv_auto; eauto.
    unfold inv in *; andDestruct; auto.
  - equiv_unfold;
      equiv_auto; eauto.
Qed.

Hint Resolve contn_equiv_sym.

Lemma wf_rename_inv :
  forall f, wf_rename f ->
       forall f', inv f f' ->
             wf_rename f'.
Proof.
  intros.
  unfold wf_rename in *; andDestruct; split.
  - eapply inv_one_to_one; eauto.
  - unfold inv in *;
      andDestruct;
      auto.
Qed.

Hint Resolve wf_rename_inv.

Lemma frame_equiv_sym :
  forall f ϕ1 ϕ2, frame_equiv f ϕ1 ϕ2 ->
             forall f', inv f f' ->
                   frame_equiv f' ϕ2 ϕ1.
Proof.
  intros.
  equiv_unfold.
  apply eq_frm;
    eauto.
Qed.

Hint Resolve frame_equiv_sym.

Lemma stack_equiv_sym :
  forall ψ1 ψ2, stack_equiv ψ1 ψ2 ->
           stack_equiv ψ2 ψ1.
Proof.
  intros ψ1 ψ2 Heq;
    induction Heq;
    intros;
    auto.
  equiv_unfold.
  edestruct (one_to_one_exists_inv) with (f:=f) as [f']; auto.
  apply eq_cons with (f:=f'); eauto.
Qed.

Hint Resolve stack_equiv_sym.

Lemma config_equiv_sym :
  forall σ1 σ2, config_equiv σ1 σ2 ->
           config_equiv σ2 σ1.
Proof.
  intros;
    equiv_unfold; eauto.
Qed.

Hint Resolve config_equiv_sym.

Lemma equivalent_reductions :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      M_wf M ->
                      forall σ1', config_equiv σ1 σ1' ->
                             exists σ2', M1 ⦂ M2 ⦿ σ1' ⤳… σ2' /\
                                    config_equiv σ2 σ2'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  - link_unique_auto.
    match goal with
    | [Hred : ?M ∙ ?σ1 ⤳ ?σ2,
              Hequiv : config_equiv ?σ1 ?σ1',
                       Hwf : M_wf M|- _] =>
      let σ2' := fresh "σ" in 
      destruct (equivalent_reduction_exists M σ1 σ2 Hred Hwf σ1') as [σ2']; auto
    end.
    match goal with
    | [Hred1 : ?M ∙ ?σ1 ⤳ ?σ2,
               Hred2 : ?M ∙ ?σ1' ⤳ ?σ2',
                       Hequiv : config_equiv ?σ1 ?σ1',
                                Hwf : M_wf ?M |- _] =>
      let Hconf := fresh in
      assert (Hconf : config_equiv σ2 σ2');
        [eapply equivalent_reduction; eauto|]
    end.
    eexists; split; eauto.
    eapply pr_single; intros; eauto.

  - link_unique_auto.
    match goal with
    | [IH : forall M, _ ∘ _ ≜ _ -> _ -> forall σ1', _ -> exists _, _ /\ _,
         Hlink : _ ∘ _ ≜ ?M',
         Hconf : config_equiv _ ?σ |- _] =>
      let σ2 := fresh "σ" in 
      destruct IH with (M:=M')(σ1':=σ) as [σ2];
        auto;
        andDestruct
    end.
    match goal with
    | [_ : config_equiv ?σa ?σb,
           _ : ?M' ∙ ?σa ⤳ ?σc |- _] =>
      let H := fresh in
      let σ := fresh "σ" in 
      destruct equivalent_reduction_exists
        with (M:=M')(σ1:=σa)(σ2:=σc)(σ1':=σb)
        as [σ H]; auto
    end.
    match goal with
    | [Hred1 : ?M0 ∙ ?σa ⤳ ?σb,
               Hred2 : ?M0 ∙ ?σa' ⤳ ?σb',
                       Hconf : config_equiv ?σa ?σa' |- _] =>
      let H := fresh in 
      assert (H : config_equiv σb σb');
        [eapply equivalent_reduction
           with (M:=M0)(σ1:=σa)(σ2:=σb)
                (σ1':=σa')(σ2':=σb');
         auto
        |]
    end.
    match goal with
    | [_ : _ ⦂ _ ⦿ ?σ1 ⤳… ?σ2,
           _ : _ ∙ ?σ2 ⤳ ?σ3,
               _ : _ ⦂ _ ⦿ ?σ1' ⤳… ?σ2',
                   _ : _ ∙ ?σ2' ⤳ ?σ3' |- exists _ : config, _ /\ _] =>
      exists σ3'; split; eauto
    end.

Qed.

Ltac equiv_reduction_auto :=
  match goal with
  | [Hred : ?M ∙ ?σa ⤳ ?σb,
            Hconf : config_equiv ?σa ?σa' |- _] =>
    match goal with
    | [Hred' : _ ∙ σa' ⤳ ?σb',
               Hconf' : config_equiv σb ?σb'|- _] =>
      idtac
    | [Hred' : _ ∙ σa' ⤳ ?σb' |- _] =>
      assert (config_equiv σb σb');
      [apply equivalent_reduction with (M:=M)(σ1:=σa)(σ1':=σa'); auto|]
    | [|- _] =>
      let σ := fresh "σ" in 
      destruct equivalent_reduction_exists
        with (M:=M)(σ1:=σa)(σ2:=σb)(σ1':=σa')
        as [σ];
      auto
    end
  end.

Ltac equiv_reductions_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σa ⤳… ?σb,
            Hconf : config_equiv ?σa ?σa',
                    Hlink : ?M1 ∘ ?M2 ≜ ?M |- _] =>
    match goal with
    | [Hred' :  M1 ⦂ M2 ⦿ σa' ⤳… ?σb',
                Hconf' : config_equiv σb ?σb' |- _] =>
      idtac
    | [|- _] =>
      let σ := fresh "σ" in 
    destruct (equivalent_reductions)
      with (M1:=M1)(M2:=M2)(M:=M)(σ1:=σa)(σ2:=σb)(σ1':=σa')
      as [σ];
    auto;
    andDestruct
    end
  end.

Lemma equivalent_pair_reduction_exists :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      M_wf M ->
                      forall σ1', config_equiv σ1 σ1' ->
                             exists σ2', M1 ⦂ M2 ⦿ σ1' ⤳ σ2' /\
                                    config_equiv σ2 σ2'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    subst;
    intros.
  link_unique_auto.
  repeat equiv_reductions_auto.
  repeat equiv_reduction_auto.
  eexists; split; eauto.
Qed.

Inductive reductions' : mdl -> mdl -> config -> config -> Prop :=
| reds_single : forall M1 M2 σ,
    (forall C, classOf this σ C ->
          exists CDef : classDef, M1 C = Some CDef) ->
    reductions' M1 M2 σ σ
| reds_trans : forall M1 M2 M σ1 σ2 σ3,
    M1 ∘ M2 ≜ M ->
    reductions' M1 M2 σ1 σ2 ->
    M ∙ σ2 ⤳ σ3 ->
    (forall C, classOf this σ3 C ->
          exists CDef : classDef, M1 C = Some CDef) ->
    reductions' M1 M2 σ1 σ3.

Hint Constructors reductions'.

Lemma reductions_alt_1 :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall M, (exists σ, M1 ∘ M2 ≜ M ->
                            M ∙ σ1 ⤳ σ /\
                            (forall C, classOf this σ1 C ->
                                  M1 C = None) /\
                            (forall C, classOf this σ C ->
                                  exists CDef : classDef, M1 C = Some CDef) /\
                            reductions' M1 M2 σ σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intro.

  - exists σ'; repeat split; intros; link_unique_auto; auto.

  - match goal with
    | [IH : forall M, exists σ', ?M1 ∘ ?M2 ≜ M ->
                       M ∙ ?σ1 ⤳ σ' /\
                       (forall C', classOf this ?σ1 C' -> ?M1 C' = None) /\
                       (forall C, classOf this σ' C -> exists CDef, ?M1 C = Some CDef) /\
                       reductions' ?M1 ?M2 σ' ?σ,
         Hlink : ?M1 ∘ ?M2 ≜ ?M |- _] =>
      let σ0 := fresh "σ" in
      let H := fresh in
      destruct (IH M) as [σ0 H];
        destruct (H Hlink);
        andDestruct
    end.
    eexists; intros.
    link_unique_auto.
    eauto.
Qed.

Lemma reductions_alt_2 :
  forall M1 M2 M σ1 σ2 σ, M1 ∘ M2 ≜ M /\
                     M ∙ σ1 ⤳ σ /\
                     (forall C, classOf this σ1 C ->
                           M1 C = None) /\
                     (forall C, classOf this σ C ->
                           exists CDef : classDef, M1 C = Some CDef) /\
                     reductions' M1 M2 σ σ2 ->
                     M1 ⦂ M2 ⦿ σ1 ⤳… σ2.
Proof.
  intros M1 M2 M σ1 σ2 σ Hred';
    andDestruct.
  match goal with
  | [Hred : reductions' M1 M2 ?σa ?σb |- _] =>
    induction Hred
  end;
    eauto.
Qed.

(*Lemma reductions'_thing :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall σ2', M1 ⦂ M2 ⦿ σ1 ⤳… σ2' ->
                        (reductions' M1 M2 σ2 σ2' \/
                         σ2 = σ2' \/
                         reductions' M1 M2 σ2' σ2).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros σ2' Hred';
    induction Hred'.

  - link_unique_auto.
    reduction_auto.

  - link_unique_auto.
    destruct IHHred' as [|Htmp];
      auto;
      [|destruct Htmp];
      subst;
      eauto.
    inversion H6; subst; eauto.
    link_unique_auto.
    

Qed.*)

(*Lemma reductions'_unique :
  forall M1 M2 σ1 σ2, reductions' M1 M2 σ1 σ2 ->
                 forall M σ, M1 ∘ M2 ≜ M ->
                        M ∙ σ2 ⤳ σ ->
                        (forall C, classOf this σ C ->
                              M1 C = None) ->
                        forall σ2', reductions' M1 M2 σ1 σ2' ->
                               forall σ', M ∙ σ2' ⤳ σ' ->
                                     (forall C, classOf this σ' C ->
                                           M1 C = None) ->
                                     σ2 = σ2'.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred.
  intros M σ0 Hlink H0 H1 σ2' Hred'.
  induction Hred'; intros; auto.
  admit.
  intros M0 σ0 Hlink H2 H3 σ2' Hred'.
  induction Hred'; intros; auto.
  inversion H3; subst; auto.
  link_unique_auto.
  
Qed.*)

Lemma pair_reduction_unique :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall σ2', M1 ⦂ M2 ⦿ σ1 ⤳ σ2' ->
                        σ2 = σ2'.
Proof.
Admitted.

Ltac equiv_pair_reduction_auto :=
  match goal with
  | [Hred : ?M1 ⦂ ?M2 ⦿ ?σa ⤳ ?σb,
            Hconf : config_equiv ?σa ?σa',
                    Hlink : ?M1 ∘ ?M2 ≜ ?M |- _] =>
    match goal with
    | [Hred' :  M1 ⦂ M2 ⦿ σa' ⤳ ?σb',
                Hconf' : config_equiv σb ?σb' |- _] =>
      idtac
    | [|- _] =>
      let σ := fresh "σ" in 
    destruct (equivalent_pair_reduction_exists)
      with (M1:=M1)(M2:=M2)(M:=M)(σ1:=σa)(σ2:=σb)(σ1':=σa')
      as [σ];
    auto;
    andDestruct
    end
  end.

Ltac reduction_auto :=
  match goal with
  | [Hred1 : ?M ∙ ?σ ⤳ ?σa,
             Hred2 : ?M ∙ ?σ ⤳ ?σb |- _] =>
    apply reduction_unique
      with
        (σ2:=σa)
      in Hred2;
    subst;
    auto
  | [Hred1 : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σa,
             Hred2 : ?M1 ⦂ ?M2 ⦿ ?σ ⤳ ?σb |- _] =>
    apply pair_reduction_unique
      with
        (σ2:=σa)
      in Hred2;
    subst;
    auto
  end.

Lemma equivalent_pair_reduction :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 forall M, M1 ∘ M2 ≜ M ->
                      M_wf M ->
                      forall σ1', config_equiv σ1 σ1' ->
                             forall σ2', M1 ⦂ M2 ⦿ σ1' ⤳ σ2' ->
                                    config_equiv σ2 σ2'.
Proof.
  intros.
  equiv_pair_reduction_auto.
  reduction_auto.
Qed.

Inductive list_equiv : partial_map var var -> list var -> list var -> Prop :=
| eql_nil : forall f, list_equiv f nil nil
| eql_cons : forall f x y l1 l2, f x = Some y ->
                            list_equiv f l1 l2 ->
                            list_equiv f (x::l1) (y::l2).

Inductive varSet_equiv : partial_map var var -> varSet -> varSet -> Prop :=
| eq_set_hole : forall f n, varSet_equiv f (s_hole n) (s_hole n)
| eq_set_bind : forall f Σ1 Σ2, list_equiv f Σ1 Σ2 ->
                           varSet_equiv f (s_bind Σ1) (s_bind Σ2).

Inductive avar_equiv : partial_map var var -> a_var -> a_var -> Prop :=
| eqa_hole : forall f n, avar_equiv f (a_hole n) (a_hole n)
| eqa_bind : forall f x y, f x = Some y ->
                      avar_equiv f (a_bind x) (a_bind y).

Ltac avar_equiv_unfold :=
  match goal with
  | [H : avar_equiv _ (a_hole _) _ |- _] => inversion H; subst; clear H
  | [H : avar_equiv _ (a_bind _) _ |- _] => inversion H; subst; clear H
  end.

Definition rename_avar (f : partial_map var var) :=
  fun a => match a with
        | a_bind x => match (f x) with
                     | Some y => Some (a_bind y)
                     | _ => Some a
                     end
        | _ => Some a
        end.

Inductive asrt_equiv : partial_map var var -> asrt -> asrt -> Prop :=
| eqa_exp : forall f e1 e2, exp_equiv f e1 e2 ->
                       asrt_equiv f (a_exp e1) (a_exp e2)
| eqa_eq : forall f e1 e1' e2 e2', exp_equiv f e1 e2 ->
                              exp_equiv f e1' e2' ->
                              asrt_equiv f (a_eq e1 e1') (a_eq e2 e2')
| eqa_class : forall f e1 e2 C, exp_equiv f e1 e2 ->
                           asrt_equiv f (a_class e1 C) (a_class e2 C)
| eqa_set : forall f e1 e2 Σ1 Σ2, exp_equiv f e1 e2 ->
                             varSet_equiv f Σ1 Σ2 ->
                             asrt_equiv f (a_set e1 Σ1) (a_set e2 Σ2)
| eqa_arr : forall f A1 A1' A2 A2', asrt_equiv f A1 A2 ->
                               asrt_equiv f A1' A2' ->
                               asrt_equiv f (a_arr A1 A1') (a_arr A2 A2')
| eqa_and : forall f A1 A1' A2 A2', asrt_equiv f A1 A2 ->
                               asrt_equiv f A1' A2' ->
                               asrt_equiv f (a_and A1 A1') (a_and A2 A2')
| eqa_or : forall  f A1 A1' A2 A2', asrt_equiv f A1 A2 ->
                               asrt_equiv f A1' A2' ->
                               asrt_equiv f (a_or A1 A1') (a_or A2 A2')
| eqa_neg : forall f A1 A2, asrt_equiv f A1 A2 ->
                       asrt_equiv f (a_neg A1) (a_neg A2)
| eqa_all_x : forall f A1 A2, asrt_equiv f A1 A2 ->
                         asrt_equiv f (a_all_x A1) (a_all_x A2)
| eqa_all_Σ : forall f A1 A2, asrt_equiv f A1 A2 ->
                         asrt_equiv f (a_all_Σ A1) (a_all_Σ A2)
| eqa_ex_x : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_ex_x A1) (a_ex_x A2)
| eqa_ex_Σ : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_ex_Σ A1) (a_ex_Σ A2)
| eqa_acc : forall f x1 y1 x2 y2, avar_equiv f x1 x2 ->
                             avar_equiv f y1 y2 ->
                             asrt_equiv f (a_acc x1 y1) (a_acc x2 y2)
| eqa_call : forall f x1 x2 y1 y2 m ps1 ps2, avar_equiv f x1 x2 ->
                                        avar_equiv f y1 y2 ->
                                        (forall p x, ps1 p = Some (a_bind x) ->
                                                exists y, f x = Some y) ->
                                        ps2 = (fun x => bind (ps1 x) (rename_avar f)) ->
                                        asrt_equiv f (a_call x1 y1 m ps1) (a_call x2 y2 m ps2)

| eqa_next : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_next A1) (a_next A2)

| eqa_will : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_will A1) (a_will A2)

| eqa_prev : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_prev A1) (a_prev A2)

| eqa_was : forall f A1 A2, asrt_equiv f A1 A2 ->
                        asrt_equiv f (a_was A1) (a_was A2)

| eqa_in : forall f A1 A2 Σ1 Σ2, asrt_equiv f A1 A2 ->
                            varSet_equiv f Σ1 Σ2 ->
                            asrt_equiv f (a_in A1 Σ1) (a_in A2 Σ2)
| eqa_extrn : forall f x1 x2, avar_equiv f x1 x2 ->
                         asrt_equiv f (a_extrn x1) (a_extrn x2)
| eqa_intrn : forall f x1 x2, avar_equiv f x1 x2 ->
                         asrt_equiv f (a_intrn x1) (a_intrn x2).

Hint Constructors asrt_equiv.

Ltac asrt_equiv_unfold :=
  match goal with
  | [H : asrt_equiv ?f (a_exp ?e) _ |- _] =>
    inversion H; subst; clear H
  | [H : asrt_equiv _ (a_eq _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_class _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_set _ _) _ |- _] => inversion H; subst; clear H

  | [H : asrt_equiv _ (a_arr _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_and _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_or _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_neg _) _ |- _] => inversion H; subst; clear H

  | [H : asrt_equiv ?f (a_all_x ?A) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_all_Σ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_ex_x _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_ex_Σ _) _ |- _] => inversion H; subst; clear H

  | [H : asrt_equiv _ (a_acc _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_call _ _ _ _) _ |- _] => inversion H; subst; clear H

  | [H : asrt_equiv _ (a_next _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_will _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_prev _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_was _ _) _ |- _] => inversion H; subst; clear H

  | [H : asrt_equiv _ (a_in _ _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_extrn _) _ |- _] => inversion H; subst; clear H
  | [H : asrt_equiv _ (a_intrn _) _ |- _] => inversion H; subst; clear H
  end.

Ltac varSet_equiv_auto :=
  match goal with
  | [H : list_equiv _ nil ?l |- _] => inversion H; subst; clear H
  | [H : list_equiv _ (?x::?l1) ?l2 |- _] => inversion H; subst; clear H
  | [H : varSet_equiv ?f (s_bind ?Σ1) ?Σ2 |- _] => inversion H; subst; clear H
  | [H : varSet_equiv ?f (s_hole ?n1) ?Σ |- _] => inversion H; subst; clear H
  end.

Ltac sat_auto :=
  match goal with
  | [|- ?M1 ⦂ ?M2 ◎ ?σ ⊨ (a_exp _)] => eapply sat_exp
  | [H1 : exp_equiv ?f ?e1 ?e1',
          H2 : exp_equiv ?f ?e2 ?e2',
               Heval1 : ?M ∙ ?σ ⊢ ?e1 ↪ ?v,
                        Heval2 : ?M ∙ ?σ ⊢ ?e2 ↪ ?v
     |- _ ⦂ _ ◎ _ ⊨ (a_eq ?e1' ?e2')] => eapply sat_eq with (v:=v)
  | [|- _ ⦂ _ ◎ _ ⊨ (a_eq _ _)] => eapply sat_eq
  | [|- _ ⦂ _ ◎ _ ⊨ (a_class _ _)] => eapply sat_class
  | [|- _ ⦂ _ ◎ _ ⊨ (a_set _ _)] => eapply sat_set

  | [|- _ ⦂ _ ◎ _ ⊨ (a_and _ _)] => apply sat_and
  | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ?A |- _ ⦂ _ ◎ ?σ ⊨ (a_or ?A _)] =>
    apply sat_or1
  | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ?A |- _ ⦂ _ ◎ ?σ ⊨ (a_or _ ?A)] =>
    eapply sat_or2
  | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊨ ?A |- _ ⦂ _ ◎ ?σ ⊨ (a_arr _ ?A)] =>
    apply sat_arr1
  | [H : ?M1 ⦂ ?M2 ◎ ?σ ⊭ ?A |- _ ⦂ _ ◎ ?σ ⊨ (a_arr ?A _)] =>
    eapply sat_arr2
  end.

Ltac eval_equiv_auto :=
  match goal with
  | [H : ?M ∙ (?χ, ?ϕ::?ψ) ⊢ ?e1 ↪ ?v,
         Heq : exp_equiv ?f ?e1 ?e2
     |- ?M ∙ (?χ, ?ϕ'::?ψ') ⊢ ?e2 ↪ ?v] =>
    eapply equivalent_evaluation
      with (σ:=(χ, ϕ::ψ))
           (e:=e1);
    eauto
  end.

Lemma equivalent_interpretation_Σ :
  forall Σ χ ϕ ψ As, ⌊ Σ ⌋ (χ, ϕ::ψ) ≜′ As ->
               forall f Σ' ϕ' ψ', list_equiv f Σ Σ' ->
                             frame_equiv f ϕ ϕ' ->
                             ⌊ Σ' ⌋ (χ, ϕ'::ψ') ≜′ As.
Proof.
  intros Σ χ ϕ ψ As Hint;
    remember (χ, ϕ::ψ) as σ;
    generalize χ, ϕ, ψ, Heqσ;
    clear Heqσ χ ϕ ψ;  
    induction Hint;
    intros χ ϕ ψ Heq;
    subst;
    intros f Σ' ϕ' ψ';
    subst;
    intros.

  - varSet_equiv_auto; auto.

  - repeat varSet_equiv_auto;
      apply int_cons; eauto.
    eapply equivalent_interpretation_x; eauto.
Qed.

Lemma link_exists :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                 exists M, M1 ∘ M2 ≜ M.
Proof.
  intros M1 M2 σ1 σ2 Hred;
    inversion Hred;
    subst.
    eauto.
Qed.

Lemma adaptation_implies_finite_2 :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall χ ϕ ψ, σ2 = (χ, ϕ::ψ) ->
                      finite_ϕ ϕ.
Proof.
  intros σ1 σ2 σ Hadapt;
    inversion Hadapt;
    subst;
    intros.
  finite_auto; simpl; intros.
  match goal with
  | [H : (_, _) = (_, _) |- _] => inversion H; subst
  end.
  simpl.
  eapply dom_finite; eauto.
Qed.

Lemma bind_empty :
  forall A B `{Eq A} (m : partial_map A B), (fun x => bind (empty x) m) = empty.
Proof.
  intros A B HeqA m.
  apply functional_extensionality;
    intros a; auto.
Qed.

Hint Rewrite bind_empty.
Hint Resolve bind_empty.

Lemma extend_empty :
  forall A B `{Eq A} (m : partial_map A B), extend empty m = m.
Proof.
  intros A B HeqA m;
    repeat map_rewrite.
  apply functional_extensionality;
    intros a; auto.
Qed.

Hint Rewrite extend_empty.
Hint Resolve extend_empty.

Lemma partial_map_dec_alt :
  forall A B `{Eq A} (m : partial_map A B),
    {m = empty} + {exists a b, m a = Some b}.
Proof.
  intros A B H m.
  remember (exists a b, m a = Some b) as P.
  destruct (excluded_middle P); subst; auto.
  left.
  apply functional_extensionality;
    intros a.
  apply exists_neg_forall with (a:=a) in n.
  repeat map_rewrite.
  apply not_some_implies_none;
    intros b.
  intros Hcontra.
  contradiction n; eexists; eauto.
Qed.

(*Lemma adaptation_implies_finite_2 :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             forall χ ϕ ψ
               χ' ϕ' ψ', σ1 = (χ, ϕ::ψ) ->
                         σ2 = (χ', ϕ'::ψ') ->
                         σ = (χ', (frm (vMap ϕ) (contn ϕ'))::ψ') \/ finite_ϕ ϕ.
Proof.
  intros σ1 σ2 σ Hadapt;
    inversion Hadapt;
    subst;
    intros.
  finite_auto.
  match goal with
  | [H : (_, _) = (_, _) |- _] => inversion H; subst
  end.
  destruct zs as [|z zs'];
    [left|right; auto].

  destruct (partial_map_dec_alt var var) with (m:=f);
    [subst|].

  - rewrite bind_empty, extend_empty.
    rewrite empty_rename; auto.

Qed.*)

(*TODO*)
Parameter equivalence_preserves_finiteness :
  forall f m1 m2, map_equiv f m1 m2 ->
             finite m1 ->
             finite m2.

Lemma equivalence_preserves_not_stuck :
  forall f c1 c2, contn_equiv f c1 c2 ->
             not_stuck c1 ->
             not_stuck c2.
Proof.
  intros f c1 c2 Heq Hns.
  destruct c1;
    equiv_unfold;
    auto.
  inversion Hns.
Qed.

Lemma equivalent_adaptation_exists :
  forall σ1 σ2 σ, σ1 ◁ σ2 ≜ σ ->
             finite_σ σ2 ->
             forall χ1 ϕ1 ψ1
               χ2 ϕ2 ψ2
               ϕ ψ, σ1 = (χ1, ϕ1::ψ1) ->
                    σ2 = (χ2, ϕ2::ψ2) ->
                    σ = (χ2, ϕ::ψ) ->
                    forall f1 ϕ1' ψ1'
                      f2 ϕ2' ψ2', frame_equiv f1 ϕ1 ϕ1' ->
                                  frame_equiv f2 ϕ2 ϕ2' ->
                                  exists f f' ϕ' ψ', (χ1, ϕ1'::ψ1') ◁ (χ2, ϕ2'::ψ2') ≜ (χ2, ϕ'::ψ') /\
                                                frame_equiv f ϕ ϕ2 /\
                                                frame_equiv f' ϕ2' ϕ' /\
                                                frame_equiv (fun x => bind ((fun y => bind (f y) f2) x) f') ϕ ϕ'.
Proof.
  intros σ1 σ2 σ Hadapt;
    inversion Hadapt;
    subst;
    intros.
  
(*  intros σ1 σ2 σ Hadapt;
    inversion Hadapt;
    subst;
    intros.
  repeat equiv_unfold.
  destruct adaptation_exists
    with
      (σ1:=(χ, ϕ0::ψ3))(χ1:=χ)(ϕ1:=ϕ0)(ψ1:=ψ3)
      (σ2:=(χ', ϕ2::ψ0))(χ2:=χ')(ϕ2:=ϕ2)(ψ2:=ψ0)
    as [σ];
    eauto.

  - apply equivalence_preserves_finiteness
      with (f:=f1)(m1:=β); eauto.

  - apply equivalence_preserves_finiteness
      with (f:=f0)(m1:=β'); eauto.
    finite_auto.
    assert (Hrewrite : β' = vMap (frm β' (c_stmt s)));
      [auto|rewrite Hrewrite].
    apply H; simpl; eauto.

  - match goal with
    | [H : frame_equiv ?f' ?ϕ' ?ϕ |- not_stuck_ϕ ?ϕ] =>
      eapply equivalence_preserves_not_stuck with (f:=f'); eauto; crush
    end.

  - exists σ; split;
      auto.
    inversion H2; subst.
    repeat match goal with
           | [H : (_,_) = (_,_)|-_] => inversion H; subst; clear H
           end.
    apply eq_conf.
    simpl in H1; subst;
      repeat equiv_unfold.
    assert (Htmp : exists f', inv f f');
      [admit|destruct Htmp as [f']].
    apply eq_cons with (f:=(fun x => bind (f' x) f2)); auto. *)
   

Admitted.

  

Lemma equivalent_satisfaction :
  (forall M1 M2 σ1 A1,  M1 ⦂ M2 ◎ σ1 ⊨ A1 ->
                   M_wf M1 ->
                   forall M, M1 ∘ M2 ≜ M ->
                        M_wf M ->
                        forall χ ϕ1 ψ1,
                          σ1 = (χ, ϕ1::ψ1) ->
                          forall f A2 ϕ2 ψ2,
                            asrt_equiv f A1 A2 ->
                            frame_equiv f ϕ1 ϕ2 ->
                            stack_equiv ψ1 ψ2 ->
                            M1 ⦂ M2 ◎ (χ, ϕ2::ψ2) ⊨ A2) /\
  (forall M1 M2 σ1 A1,  M1 ⦂ M2 ◎ σ1 ⊭ A1 ->
                   M_wf M1 ->
                   forall M, M1 ∘ M2 ≜ M ->
                        M_wf M ->
                        forall χ ϕ1 ψ1,
                          σ1 = (χ, ϕ1::ψ1) ->
                          forall f A2 ϕ2 ψ2,
                            asrt_equiv f A1 A2 ->
                            frame_equiv f ϕ1 ϕ2 ->
                            stack_equiv ψ1 ψ2 ->
                            M1 ⦂ M2 ◎ (χ, ϕ2::ψ2) ⊭ A2).
Proof.
  apply sat_mutind; intros; subst;
    repeat equiv_unfold;
    repeat asrt_equiv_unfold;
    try sat_auto;
    eauto;
    try solve [eval_equiv_auto].

  - varSet_equiv_auto.
    sat_auto; eauto.
    + eval_equiv_auto.
    + eapply equivalent_interpretation_Σ; eauto.

  - apply sat_all_x; intros.
    unfold mapp in H4.
    unfold configMapStack in H4.
    simpl in H4.
    unfold mapp, stackMap in H4.
    destruct (H11 y v); auto.
    assert (Hex : exists z', fresh_x z' (χ, ϕ1::ψ1) A);
      [admit|destruct Hex as [z']].
    apply H
      with (M:=M)(y:=x)(v:=v)(z:=z')(ϕ2:=update_ϕ_map ϕ1 z' v)(ψ2:=ψ1)(f0:=update z z' f); auto.
    + admit.
    + admit. (* substitution preserves equivalence *)
    + admit.

  - eapply sat_ex_x; intros.
    + admit.
    + admit.
    + admit. (* substitution preserves equivalence *)

  - admit.

  - admit.

  - repeat avar_equiv_unfold.
    apply sat_access1 with (α:=α); auto.
    eapply equivalent_interpretation_x; eauto.
    eapply equivalent_interpretation_x with (x:=y); eauto.

  - repeat avar_equiv_unfold.
    eapply sat_access2; eauto;
      eapply equivalent_interpretation_x; eauto.

  - repeat avar_equiv_unfold.
    match goal with
    | [H : (_, _) = (_, _)|- _] => inversion H; subst
    end.
    inversion H6; subst.
    + rewrite e0 in H3; inversion H3.
    + eapply sat_access3 with (α1:=α1)(α2:=α2)(ϕ:=ϕ2)(ψ:=ψ2)(χ:=χ0)(s:=s2); auto.
      * eapply equivalent_interpretation_x with (x:=x)(f:=f); eauto.
      * eapply equivalent_interpretation_x with (x:=this)(f:=f); eauto.
        inversion H8; subst; auto.
      * eapply equivalent_interpretation_x with (x:=y); eauto.
      * admit.
      * admit.

  - repeat avar_equiv_unfold.
    admit.

  - repeat avar_equiv_unfold.
    eapply sat_extrn; eauto.
    eapply equivalent_interpretation_x; eauto.

  - repeat avar_equiv_unfold.
    eapply sat_intrn; eauto.
    eapply equivalent_interpretation_x; eauto.

  - repeat varSet_equiv_auto.
    eapply sat_in.
    admit. (* restriction equivalence *)
    admit. (* apply induction hyp *)

  - match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    destruct equivalent_pair_reduction_exists
          with (M:=M)(M1:=M1)(M2:=M2)
             (σ1:=(χ0, ϕ1::nil))(σ2:=σ')
             (σ1':=(χ0, ϕ2::nil)) as [σ2'];
      andDestruct;
      eauto.
    inversion a; subst.
    repeat match goal with
           | [H : (_, _) = (_, _) |- _] => inversion H; subst; clear H
           end.
    simpl in *.
    let someσ:= fresh "σ" in
    destruct equivalent_adaptation_exists
      with
        (σ1:=(χ0, ϕ1::nil))(σ2:=σ')(σ:=σ'')(σ1':=(χ0, ϕ2::nil))(σ2':=σ2')
      as
        [someσ];
      auto;
      andDestruct.
    + admit. (* adaptation ignores the rest of the stack *)
    + admit. (* reduction preserves finiteness  *)
    + eapply eq_conf, eq_cons; eauto.
    + apply sat_next with (ϕ:=ϕ2)(ψ:=ψ2)(χ:=χ0)(σ':=σ2')(σ'':=σ); eauto.
      * admit. (* adaptation ignores the rest of the stack *)
      * 
        inversion Ha0; subst.
        inversion Hb0; subst.
        inversion H16; subst.
        inversion a; subst.
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end.
        match goal with
        | [H : (_, _) = (_, _) |- _] => inversion H; subst
        end.
        inversion H4; subst.
        apply H
          with (M:=M)(f:=f1)
               (ϕ1:={| vMap := extend (fun x : var => bind (f2 x) β'0) β0; contn := c_stmt (❲ f2 ↦ s1 ❳) |})
               (ψ1:=ψ3);
          auto.
        simpl in H7.
        repeat (equiv_unfold; simpl in *; subst).
        assert (f3 = f1);
          [admit|subst f3].
        assert (f4 = f1);
          [admit|subst f4].
        admit. (* all  *)
    

Admitted.

(*Lemma map_update_ϕ_neq :
  forall x y, x <> y ->
         forall ϕ v, vMap (update_ϕ_map ϕ x v) y = vMap ϕ y.
Proof.
  intros.
  unfold update_ϕ_map, update, t_update; simpl.
  destruct x as [n]; destruct y as [m].
  destruct (eq_dec m n) as [|Hneq];
    [subst; contradiction H; auto
    |apply Nat.eqb_neq in Hneq; rewrite Hneq; auto].
Qed.

Hint Rewrite map_update_ϕ_neq.
Hint Resolve map_update_ϕ_neq.

Lemma map_update_σ_neq :
  forall x y, x <> y ->
         forall σ v, mapp (update_σ_map σ x v) y = mapp σ y.
Proof.
  intros x y Hneq σ v.
  destruct σ as [χ ψ].
  unfold update_σ_map, mapp,
  update_ψ_map, mapp,
  configMapStack, mapp,
  stackMap, mapp; simpl.
  destruct ψ as [|ϕ ψ'];
    auto.
Qed.

Lemma map_σ_map_ψ :
  forall σ x, mapp σ x = mapp (snd σ) x.
Proof.
  intros; auto.
Qed.

Ltac map_rewrite :=
  match goal with
  | [H : context[mapp _ _] |-_] => unfold mapp in H
  | [|- context[mapp _ _]] => unfold mapp
  | [H : context[update_σ_map _ _] |-_] => unfold update_σ_map in H
  | [|- context[update_σ_map _ _]] => unfold update_σ_map
  | [H : context[update_ψ_map _ _] |-_] => unfold update_ψ_map in H
  | [|- context[update_ψ_map _ _]] => unfold update_ψ_map
  | [H : context[configMapStack _ _] |-_] => unfold configMapStack in H
  | [|- context[configMapStack _ _]] => unfold configMapStack
  | [H : context[stackMap _ _] |-_] => unfold stackMap in H
  | [|- context[stackMap _ _]] => unfold stackMap
  | [H : context[update _ _] |-_] => unfold update in H
  | [|- context[update _ _]] => unfold update
  | [H : context[t_update _ _] |-_] => unfold t_update in H
  | [|- context[t_update _ _]] => unfold t_update
  end.

Lemma subst_simpl_acc_f :
  forall x n e f, ([x /s n] (e_acc_f e f)) = (e_acc_f ([x /s n] e) f).
Proof.
  auto.
Qed.

Ltac subst_simpl :=
  match goal with
  | [H : context[[_ /s _](e_acc_f _ _)] |- _] => rewrite subst_simpl_acc_f in H
  | [|- context[[_ /s _](e_acc_f _ _)]] => rewrite subst_simpl_acc_f
  end.

Inductive ref_equiv : partial_map var value -> ref -> partial_map var value -> ref -> Prop :=
| eq_var : forall m1 x1 m2 x2, m1 x1 = m2 x2 ->
                          (x1 = this -> x2 = this) ->
                          (x2 = this -> x1 = this) ->
                          ref_equiv m1 (r_var x1) m2 (r_var x2)
| eq_fld : forall m1 x1 f m2 x2, m1 x1 = m2 x2 ->
                            (x1 = this -> x2 = this) ->
                            (x2 = this -> x1 = this) ->
                            ref_equiv m1 (r_fld x1 f) m2 (r_fld x2 f).

Hint Constructors ref_equiv.

Inductive exp_equiv : partial_map var value -> exp -> partial_map var value -> exp -> Prop :=
| eq_e_val : forall m1 v m2, exp_equiv m1 (e_val v) m2 (e_val v)
| eq_e_var : forall m1 x1 m2 x2, m1 x1 = m2 x2 ->
                            exp_equiv m1 (e_var x1) m2 (e_var x2)
(*| eq_e_var2 : forall m1 x1 m2 x2, m1 x1 = m2 x2 ->
                             m1 x2 = None ->
                             m2 x1 = None ->
                             exp_equiv m1 (e_var x1) m2 (e_var x2)*)
| eq_e_hole : forall m1 m2 n, exp_equiv m1 (e_hole n) m2 (e_hole n)
| eq_e_eq : forall m1 e1 e1' m2 e2 e2', exp_equiv m1 e1 m2 e2 ->
                                   exp_equiv m1 e1' m2 e2' ->
                                   exp_equiv m1 (e_eq e1 e1') m2 (e_eq e2 e2')
| eq_e_if : forall m1 e1 ea1 eb1 m2 e2 ea2 eb2,
    exp_equiv m1 e1 m2 e2 ->
    exp_equiv m1 ea1 m2 ea2 ->
    exp_equiv m1 eb1 m2 eb2 ->
    exp_equiv m1 (e_if e1 ea1 eb1) m2 (e_if e2 ea2 eb2)
| eq_e_acc_f : forall m1 e1 f m2 e2, exp_equiv m1 e1 m2 e2 ->
                                exp_equiv m1 (e_acc_f e1 f) m2 (e_acc_f e2 f)
| eq_e_acc_g : forall m1 e1 p1 g m2 e2 p2, exp_equiv m1 e1 m2 e2 ->
                                      exp_equiv m1 p1 m2 p2 ->
                                      exp_equiv m1 (e_acc_g e1 g p1) m2 (e_acc_g e2 g p2).

Hint Constructors exp_equiv.

Inductive exp_equiv_c : config -> exp -> config -> exp -> Prop :=
| eqc_cons : forall χ ϕ1 ψ1 e1 ϕ2 ψ2 e2, exp_equiv (vMap ϕ1) e1 (vMap ϕ2) e2 ->
                                    exp_equiv_c (χ, ϕ1::ψ1) e1 (χ, ϕ2::ψ2) e2.

Hint Constructors exp_equiv_c.

Lemma equivalent_refl_exp :
  forall e m, exp_equiv m e m e.
Proof.
  intros e;
    induction e;
    intros;
    eauto.
Qed.

Hint Resolve equivalent_refl_exp.

Lemma equivalent_refl_exp_σ :
  forall χ ϕ ψ e, exp_equiv_c (χ, ϕ::ψ) e (χ, ϕ::ψ) e.
Proof.
  intros; eauto.
Qed.

Print update.

(*Lemma equivalent_exp_update :
  forall m1 e1 m2 e2, exp_equiv m1 e1 m2 e2 ->
                 forall x v, exp_equiv (update x v m1) e1 (update x v m2) e2.
Proof.
  intros m1 e1 m2 e2 Hequiv;
    induction Hequiv;
    intros;
    eauto.
  admit.
  apply eq_e_var1; repeat map_rewrite.
  
  
Qed.*)

Print Eq.

Print eqb.
Check nat_Eq.(eqb_refl).

Hint Resolve eqb_refl.

Instance eqOption (A : Type) `{Eq A} : Eq (option A) :=
  {
    eqb o1 o2 := match o1, o2 with
                 | None, None => true
                 | Some a1, Some a2 => eqb a1 a2
                 | _, _ => false
                 end
  }.
Proof.
  intros; destruct a; eauto.

  intros a1 a2; destruct a1, a2; intros; eauto with eqDB.

  intros a1 a2; destruct a1, a2; intros;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [Heq : eqb ?a1 ?a2 = true |- _] => apply eqb_eqp in Heq;
                                             subst;
                                             auto
        end;
    auto.

  intros a1 a2; destruct a1, a2; intros;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [Heq : eqb ?a1 ?a2 = false |- _] => apply eqb_neq in Heq;
                                              subst;
                                              crush
        end;
    crush.

  intros a1 a2; destruct a1, a2; intros;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [ |- eqb ?a1 ?a2 = false] => apply neq_eqb; crush
        end;
    crush.

  intros o1 o2; destruct o1, o2; intros; auto;
    try match goal with
        |[|- {Some _ = None} + {Some _ <> None} ] => right; crush
        |[|- {None = Some _} + {None <> Some _} ] => right; crush
        |[|- {Some ?a1 = Some ?a2} + {Some ?a1 <> Some ?a2} ] => destruct (eq_dec a1 a2) as [Heq|Hneq];
                                                                subst;
                                                                auto;
                                                                right;
                                                                crush
        end.

Defined.

Print value.

Instance eqValue : Eq value :=
  {
    eqb v1 v2 :=
      match v1, v2 with
      | v_true, v_true => true
      | v_false, v_false => true
      | v_null, v_null => true
      | v_addr n1, v_addr n2 => eqb n1 n2
      | _, _ => false
      end
  }.
Proof.
  intros a; destruct a; auto.

  intros a1 a2; destruct a1, a2; intros; auto with eqDB.

  intros a1 a2; destruct a1, a2; intros; auto;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [H : eqb ?a1 ?a2 = true |- _] => apply eqb_eqp in H;
                                           subst;
                                           auto
        end.

  intros a1 a2; destruct a1, a2; intros;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [Heq : eqb ?a1 ?a2 = false |- _] => apply eqb_neq in Heq;
                                              subst;
                                              crush
        end;
    crush.

  intros a1 a2; destruct a1, a2; intros;
    try match goal with
        | [Hcontra : true = false |-_] => inversion Hcontra
        | [Hcontra : false = true |-_] => inversion Hcontra
        end;
    try match goal with
        | [ |- eqb ?a1 ?a2 = false] => apply neq_eqb
        end;
    try solve [crush].

  intros a1 a2; destruct a1, a2; intros; auto;
    try match goal with
        |[|- {_ = _} + {v_true <> v_false} ] => right; crush
        |[|- {_ = _} + {v_true <> v_null} ] => right; crush
        |[|- {_ = _} + {v_true <> v_addr _} ] => right; crush
        |[|- {_ = _} + {v_false <> v_true} ] => right; crush
        |[|- {_ = _} + {v_false <> v_null} ] => right; crush
        |[|- {_ = _} + {v_false <> v_addr _} ] => right; crush
        |[|- {_ = _} + {v_null <> v_true} ] => right; crush
        |[|- {_ = _} + {v_null <> v_false} ] => right; crush
        |[|- {_ = _} + {v_null <> v_addr _} ] => right; crush
        |[|- {_ = _} + {v_addr _ <> v_true} ] => right; crush
        |[|- {_ = _} + {v_addr _ <> v_false} ] => right; crush
        |[|- {_ = _} + {v_addr _ <> v_null} ] => right; crush
        |[|- {v_addr ?a1 = v_addr ?a2} + {v_addr ?a1 <> v_addr ?a2} ] =>
         destruct (eq_dec a1 a2) as [Heq|Hneq];
           subst;
           auto;
           right;
           crush
        end.
  
Qed.

Lemma equivalent_exp_refl :
  forall e m1 m2, (forall x, m1 x <> m2 x ->
                   notin_exp e x) ->
             exp_equiv m1 e m2 e.
Proof.
  intros e;
    induction e;
    intros;
    eauto.

  apply eq_e_var.
  destruct (eq_dec (m1 v) (m2 v)) as [|Hneq];
    [auto|apply H in Hneq; inversion Hneq; subst; crush].

  apply eq_e_eq; eauto.
  apply IHe1; intros.
  apply H in H0; inversion H0; auto.
  apply IHe2; intros.
  apply H in H0; inversion H0; auto.

  apply eq_e_if; eauto.
  apply IHe1; intros.
  apply H in H0; inversion H0; auto.
  apply IHe2; intros.
  apply H in H0; inversion H0; auto.
  apply IHe3; intros.
  apply H in H0; inversion H0; auto.

  apply eq_e_acc_f; eauto.
  apply IHe; intros.
  apply H in H0; inversion H0; auto.

  apply eq_e_acc_g; eauto.
  apply IHe1; intros.
  apply H in H0; inversion H0; auto.
  apply IHe2; intros.
  apply H in H0; inversion H0; auto.

Qed.

Lemma ghost_field_equiv :
  forall m1 m2 x, m1 this = m2 this ->
             m1 x = m2 x ->
             forall M C CDef g e,
               M_wf M ->
               M C = Some CDef ->
               (c_g_fields CDef) g = Some (x, e) ->
               exp_equiv m1 e m2 e.
Proof.
  intros.

  match goal with
  | [Hwf : M_wf ?M |-_] => inversion Hwf; subst  
  end.
  match goal with
  | [Hcls : forall C' CDef',  ?M C' = Some CDef' -> cls_wf CDef',
       HDef : ?M C = Some ?CDef  |-_] => apply H6 in HDef; inversion HDef; subst
  end; simpl in *.
  match goal with
  | [Hwf : gFields_wf _ |- _] => inversion Hwf; subst
  end.

  apply equivalent_exp_refl; intros.
  destruct (eq_dec x0 x) as [Heq1|Hneq1];
    [subst; crush
    |];
    destruct (eq_dec x0 this) as [Heq2|Hneq2];
    [subst; crush
    |apply H9 with (g:=g)(x:=x); auto].
Qed.

Lemma exp_equiv_stack_head :
  forall σ1 e1 σ2 e2, exp_equiv_c σ1 e1 σ2 e2 ->
                 exists χ ϕ1 ψ1 ϕ2 ψ2, σ1 = (χ, ϕ1::ψ1) /\
                                  σ2 = (χ, ϕ2::ψ2).
Proof.
  intros.
  inversion H; subst; repeat eexists.
Qed.

Ltac config_decompose :=
  match goal with
  | [H : exp_equiv_c ?σ1 ?e1 ?σ2 ?e2 |-_] => let χ := fresh "χ" in
                                           let Ha := fresh in 
                                           destruct (exp_equiv_stack_head σ1 e1 σ2 e2 H) as [χ Ha];
                                           let ϕ1 := fresh "ϕ1" in
                                           destruct Ha as [ϕ1 Ha];
                                           let ψ1 := fresh "ψ1" in
                                           destruct Ha as [ψ1 Ha];
                                           let ϕ2 := fresh "ϕ2" in
                                           destruct Ha as [ϕ2 Ha];
                                           let ψ2 := fresh "ψ2" in
                                           destruct Ha as [ψ2 Ha];
                                           andDestruct;
                                           subst
  end.

Lemma ghost_field_equiv_c :
  forall σ1 σ2 χ ϕ1 ψ1 ϕ2 ψ2 x,
    σ1 = (χ, ϕ1::ψ1) ->
    σ2 = (χ, ϕ2::ψ2) ->
    mapp σ1 this = mapp σ2 this ->
    mapp σ1 x = mapp σ2 x ->
    forall M C CDef g e,
      M_wf M ->
      M C = Some CDef ->
      (c_g_fields CDef) g = Some (x, e) ->
      exp_equiv_c σ1 e σ2 e.
Proof.
  intros; subst.
  repeat map_rewrite; simpl in *.
  apply eqc_cons.
  eapply ghost_field_equiv; eauto.
Qed.

Lemma evaluation_under_equivalent_configurations :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             M_wf M ->
             forall σ' e', exp_equiv_c σ e σ' e' ->
                      M ∙ σ' ⊢ e' ↪ v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    config_decompose;
    repeat map_rewrite; simpl in *;
      try solve [inversion H0; subst;
                 inversion H8; subst;
                 try eapply v_if_true;
                 try eapply v_equals;
                 try eapply v_nequals;
                 eauto].

  - inversion H1; subst;
      inversion H9; subst;
        rewrite H4 in H; eauto.

  - inversion H2; subst;
      inversion H10; subst; eauto.

  - inversion H3; subst;
      inversion H11; subst; eauto;
        eapply v_f_ghost; eauto;
          apply IHHeval3; auto;
            repeat map_rewrite; simpl in *;
              apply ghost_field_equiv_c
                with
                  (χ:=χ)(ψ1:=ψ1)(ψ2:=ψ2)(x:=x)(M:=M)(C:=cname o)(CDef:=C)(g:=f)
                  (ϕ1:=update_ϕ_map (update_ϕ_map ϕ1 x v) this (v_addr α))
                  (ϕ2:=update_ϕ_map (update_ϕ_map ϕ2 x v) this (v_addr α)); auto;
                repeat map_rewrite; simpl in *;
                  repeat map_rewrite;
                  rewrite eqb_refl;
                  destruct (eqb x this); simpl; auto.

  - inversion H0; subst;
      inversion H8; subst;
        apply v_if_false; eauto.

  - inversion H1; subst;
      inversion H9; subst;
        eapply v_nequals; eauto.
Qed.



Inductive stmt_equiv : partial_map var value -> stmt -> partial_map var value -> stmt -> Prop :=
| eq_asgn : forall m1 x1 y1 m2 x2 y2 s1 s2,
    ref_equiv m1 x1 m2 x2 ->
    ref_equiv m1 y1 m2 y2 ->
    stmt_equiv m1 s1 m2 s2 ->
    stmt_equiv m1 (s_stmts (s_asgn x1 y1) s1) m2 (s_stmts (s_asgn x2 y2) s2)

| eq_meth : forall m1 x1 y1 m vMap1 m2 x2 y2 vMap2 s1  s2,
    m1 x1 = m2 x2 ->
    m1 y1 = m2 y2 ->
    stmt_equiv m1 s1 m2 s2 ->
    (x1 = this -> x2 = this) ->
    (x2 = this -> x1 = this) ->
    (forall D, dom vMap1 D ->
          dom vMap2 D) ->
    (forall D, dom vMap2 D ->
          dom vMap1 D) ->
    (forall x z1 z2, vMap1 x = Some z1 ->
                vMap2 x = Some z2 ->
                m1 z1 = m2 z2) ->
    stmt_equiv m1 (s_stmts (s_meth x1 y1 m vMap1) s1) m2 (s_stmts (s_meth x2 y2 m vMap2) s2)

| eq_new : forall m1 x1 C pMap1 m2 x2 pMap2 s1 s2,
    m1 x1 = m2 x2 ->
    stmt_equiv m1 s1 m2 s2 ->
    (x1 = this -> x2 = this) ->
    (x2 = this -> x1 = this) ->
    (forall D, dom pMap1 D ->
          dom pMap2 D) ->
    (forall D, dom pMap2 D ->
          dom pMap1 D) ->
    compose pMap1 m1 = compose pMap2 m2 ->
    stmt_equiv m1 (s_stmts (s_new x1 C pMap1) s1) m2 (s_stmts (s_new x2 C pMap2) s2)

(*| eq_stmts : forall m1 s1 s1' m2 s2 s2',
    stmt_equiv m1 s1 m2 s2 ->
    stmt_equiv m1 s1' m2 s2' ->
    stmt_equiv m1 (s_stmts s1 s1') m2 (s_stmts s2 s2')*)

| eq_rtrn1 : forall m1 x1 m2 x2 s1 s2,
    m1 x1 = m2 x2 ->
    stmt_equiv m1 s1 m2 s2 ->
    stmt_equiv m1 (s_stmts (s_rtrn x1) s1) m2 (s_stmts (s_rtrn x2) s2)

| eq_rtrn2 : forall m1 x1 m2 x2,
    m1 x1 = m2 x2 ->
    stmt_equiv m1 (s_rtrn x1) m2 (s_rtrn x2).

Hint Constructors stmt_equiv.

Inductive contn_equiv : partial_map var value -> continuation -> partial_map var value -> continuation -> Prop :=
| eq_stmt : forall m1 s1 m2 s2, stmt_equiv m1 s1 m2 s2 ->
                           contn_equiv m1 (c_stmt s1) m2 (c_stmt s2)
| eq_hole : forall m1 x1 s1 m2 x2 s2, stmt_equiv m1 s1 m2 s2 ->
                                 m1 x1 = m2 x2 ->
                                 (x1 = this -> x2 = this) ->
                                 (x2 = this -> x1 = this) ->
                                 contn_equiv m1 (c_hole x1 s1) m2 (c_hole x2 s2).

Hint Constructors contn_equiv.

Inductive frame_equiv : frame -> frame -> Prop :=
| eq_frm : forall ϕ1 ϕ2, contn_equiv (vMap ϕ1) (contn ϕ1) (vMap ϕ2) (contn ϕ2) ->
                    vMap ϕ1 this = vMap ϕ2 this ->
                    frame_equiv ϕ1 ϕ2.

Hint Constructors frame_equiv.

Inductive stack_equiv : stack -> stack -> Prop :=
| eq_empty_stack : stack_equiv nil nil
| eq_cons_stack : forall ϕ1 ϕ2 ψ1 ψ2, frame_equiv ϕ1 ϕ2 ->
                                 stack_equiv ψ1 ψ2 ->
                                 stack_equiv (ϕ1::ψ1) (ϕ2::ψ2).

Hint Constructors stack_equiv.

Inductive config_equiv :  config -> config -> Prop :=
| conf_equiv : forall χ ψ1 ψ2, stack_equiv ψ1 ψ2 ->
                          config_equiv (χ, ψ1) (χ, ψ2).

Hint Constructors config_equiv.

Lemma equivalent_interpretation_x :
  forall x χ ϕ ψ v, ⌊ x ⌋ (χ, ϕ::ψ) ≜ v ->
               forall ϕ' ψ' y, vMap ϕ x = vMap ϕ' y ->
                          ⌊ y ⌋ (χ, ϕ'::ψ') ≜ v.
Proof.
  intros.
  match goal with
  | [H : ⌊ ?x ⌋ ?σ ≜ ?v |- _ ] => inversion H; subst; simpl in *; crush
  end.
  eapply int_x; simpl; eauto; crush.
Qed.

Lemma cname_interpretation :
  forall x χ ψ α, ⌊ x ⌋ (χ, ψ) ≜ v_addr α ->
             forall o C, χ α = Some o ->
                    classOf x (χ, ψ) C ->
                    cname o = C.
Proof.
  intros.
  match goal with
  | [H : ⌊ ?x ⌋ ?σ ≜ ?v |- _] => inversion H; simpl in *; subst
  end.
  match goal with
  | [H : classOf ?x ?σ ?C |- _] => inversion H; simpl in *; subst
  end.
  interpretation_rewrite.
  crush.
Qed.

Ltac equiv_unfold :=
  match goal with
  | [H : ref_equiv ?m1 ?r1 ?m2 ?r2 |- _] => inversion H; subst; clear H

  | [H : stmt_equiv ?m1 (s_asgn _ _) ?m2 ?s2 |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?m1 (s_meth _ _ _ _) ?m2 ?s2 |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?m1 (s_new _ _ _) ?m2 ?s2 |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?m1 (s_stmts _ _) ?m2 ?s2 |- _] => inversion H; subst; clear H
  | [H : stmt_equiv ?m1 (s_rtrn _) ?m2 ?s2 |- _] => inversion H; subst; clear H

  | [H : contn_equiv ?m1 ?c1 ?m2 ?c2 |- _] => inversion H; subst; clear H
  | [H : frame_equiv ?ϕ1 ?ϕ2 |- _] => inversion H; subst; clear H

  | [H : stack_equiv (_ :: _) ?ψ2 |- _] => inversion H; subst; clear H
  | [H : config_equiv ?σ1 ?σ2 |- _] => inversion H; subst; clear H
  end.

Lemma equivalent_class_of :
  forall x χ ϕ ψ C, classOf x (χ, ϕ::ψ) C ->
               forall y ϕ' ψ', vMap ϕ x = vMap ϕ' y ->
                          classOf y (χ, ϕ'::ψ') C.
Proof.
  intros.
  inversion H; simpl in *; subst.
  apply cls_of with (α:=α)(χ:=χ0)(o:=o); auto.
  eapply int_x; simpl; eauto.
  inversion H1; subst; crush.
Qed.

Lemma reduction_under_equivalent_configurations_exists :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall σ1', config_equiv σ1 σ1' ->
                    exists σ2', M ∙ σ1' ⤳ σ2'.
Proof.
  intros M σ1 σ2 Hred;
    inversion Hred;
    subst;
    intros.

  - (* meth *)
    repeat equiv_unfold;
      simpl in *;
      [|crush].
    + repeat match goal with
             | [H : contn ?ϕ = ?s, H' : context[contn ?ϕ] |- _] => rewrite H in H'
             end.
      crush.
      repeat equiv_unfold.
      exists (χ, (frm (update this (v_addr α) (compose vMap2 (vMap ϕ2))) (c_stmt s))
              :: (frm (vMap ϕ2) (c_hole x2 s2'))
              :: ψ0).
      apply r_mth
        with (ϕ:=ϕ2)(ψ:=ψ0)(x:=x2)(y:=y2)(m:=m)
             (ps:=vMap2)(zs:=zs)(α:=α)(o:=o)(s:=s)
             (s':=s2')(C:=C);
        auto.
      
      apply int_x with (ϕ:=ϕ2)(ψ:=ψ0); auto.
      match goal with
      | [Hrewrite : _ = vMap ?ϕ ?x |- context[vMap ?ϕ ?x]] => rewrite <- Hrewrite
      end.
      match goal with
      | [Hint : ⌊ ?y ⌋ (_, ?ϕ :: _) ≜ ?a |- vMap ?ϕ ?y = Some ?a] =>
        inversion Hint; subst; simpl in *; crush
      end.

  - (* vAssgn *)
    repeat equiv_unfold;
      simpl in *;
      [|crush].
    repeat match goal with
           | [H : contn ?ϕ = ?s, H' : context[contn ?ϕ] |- _] => rewrite H in H'
           end.
    crush.
    repeat equiv_unfold.
    exists (χ, (update_ϕ_map ϕ2 x3 v) :: ψ0); auto.
    repeat map_rewrite; simpl in *.
    apply r_vAssgn
      with
        (ϕ:=ϕ2)(σ':=(χ, update_ϕ_map ϕ2 x3 v :: ψ0))(M:=M)
        (σ:=(χ, ϕ2::ψ0))(x:=x3)(y:=x0)(f:=f)(s:=s2')(χ:=χ)
        (ψ:=ψ0)(α:=α)(v:=v)(o:=o)(C:=C);
      auto.
    + match goal with
      | [ |- ⌊ _ ⌋ (_, ?ϕ' :: ?ψ') ≜ _] => apply int_x with (ϕ:=ϕ')(ψ:=ψ'); auto
      end.
      match goal with
      | [H1 : _ = vMap ?ϕ ?x,
              H2 : ⌊ _ ⌋ _ ≜ _ |- vMap ?ϕ ?x = Some _] => rewrite <- H1; inversion H2; crush
      end.

    + eapply equivalent_class_of; eauto.

    + apply equivalent_class_of with (x:=y)(ϕ:=ϕ)(ψ:=ψ); eauto.

  - (* fAssgn *)
    repeat equiv_unfold.
    + (* stmt *)
      repeat match goal with
             | [H : c_stmt ?s = contn ?ϕ |-_] => rewrite <- H in *
             end.
      inversion H0; subst.
      repeat equiv_unfold.
      remember {| vMap := vMap ϕ2; contn := c_stmt s2' |} as ϕ'.
      remember (update α {| cname := cname o; flds := update f v (flds o); meths := meths o |} χ) as χ'.
      remember (χ', ϕ' :: ψ0) as σ'.
      exists σ'.
      apply r_fAssgn
        with (ϕ:=ϕ2)(ϕ':=ϕ')(χ':=χ')(x:=x0)(y:=x3)(f:=f)(s:=s2')
             (ψ:=ψ0)(χ:=χ)(α:=α)(v:=v)(o:=o)(C:=C)
             (o':=new (cname o) (update f v (flds o)) (meths o));
        auto.
      * eapply equivalent_interpretation; eauto.
      * eapply equivalent_interpretation; eauto.
      * eapply equivalent_class_of; eauto.
      * apply equivalent_class_of with (x:=y)(ϕ:=ϕ)(ψ:=ψ); eauto.

    + (* hole *)
      rewrite H0 in H8; inversion H8.

  - (* new *)
    repeat equiv_unfold; [|crush].
    + match goal with
      | [H : contn ?ϕ = c_stmt (s_stmts _ _) |- _] => rewrite H in *
      end.
      crush.
      repeat equiv_unfold.
      remember {| vMap := update x2 (v_addr α) (vMap ϕ2); contn := c_stmt s2' |} as ϕ'.
      remember {| cname := C; flds := compose pMap2 (vMap ϕ2); meths := c_meths CDef |} as o.
      exists (update α o χ, ϕ'::ψ0).
      apply r_new
        with
          (χ:=χ)(ψ:=ψ0)(ϕ:=ϕ2)
          (ϕ':=ϕ')(α:=α)(x:=x2)(C:=C)(fMap:=pMap2)
          (s:=s2')(o:=o)(CDef:=CDef);
        auto.
      intros f y Hmap.
      apply equal_f with (x0:=f) in H21;
        unfold compose in H21.
      rewrite Hmap in H21.
      apply in_map_implies_in_dom with (d:=c_flds CDef) in Hmap; auto.
      apply in_dom_implies_in_map with (m:=fMap) in Hmap; auto.
      destruct_exists.
      rewrite H0 in H21.
      rewrite <- H21.
      destruct (H5 f x0); auto.
      eexists; eauto.

  - (* ret1 *)
    repeat equiv_unfold;
      [crush
      |
      |crush
      |crush].

    repeat match goal with
           | [H : _ = contn ?ϕ |- _] => rewrite <- H in *
           end.
    crush.
    equiv_unfold.
    exists (χ, (update_ϕ_contn (update_ϕ_map ϕ0 x2 α) (c_stmt s3)) :: ψ2).
    eapply r_ret1; eauto.
    eapply equivalent_interpretation; eauto.

  - (* ret2 *)
    repeat equiv_unfold;
      [crush
      |
      |crush
      |crush].
    repeat match goal with
           | [H : _ = contn ?ϕ |- _] => rewrite <- H in *
           end.
    crush.
    repeat equiv_unfold.
    exists (χ, (update_ϕ_contn (update_ϕ_map ϕ0 x2 α) (c_stmt s3)) :: ψ2).
    eapply r_ret2; try solve [simpl; eauto].
    eapply equivalent_interpretation; eauto.
Qed.

Lemma same_dom_maps_some :
  forall {A B : Type} `{Eq A} (m1 : partial_map A B) D,
    dom m1 D ->
    forall {C : Type} (m2 : partial_map A C),
      dom m2 D ->
      (forall a b, m1 a = Some b ->
              exists c, m2 a = Some c).
Proof.
  intros.

  eapply in_dom_implies_in_map; eauto.
  eapply in_map_implies_in_dom with (m:=m1); eauto.
Qed.

Lemma same_dom_maps_none :
  forall {A B : Type} `{Eq A} (m1 : partial_map A B) D,
    dom m1 D ->
    forall {C : Type} (m2 : partial_map A C),
      dom m2 D ->
      (forall a, m1 a = None ->
            m2 a = None).
Proof.
  intros.

  apply not_some_implies_none; intros; intros Hcontra.
  match goal with
  | [H : ?m _ = Some _,
     Hdom : dom ?m ?D |- _] => apply in_map_implies_in_dom with (d:=D) in H; auto
  end.
  match goal with
  | [H : ?m' _ = None,
         Hdom : dom ?m' ?D,
                Hin : In _ ?D |- _] => apply in_dom_implies_in_map with (m:=m') in Hin; auto
  end;
    destruct_exists;
    crush.
Qed.

Lemma equal_composition :
  forall {A B : Type} `{Eq A} `{Eq B} (ps1 : partial_map A B) D,
    dom ps1 D ->
    forall ps2, dom ps2 D ->
           forall {C : Type} (m1 m2 : partial_map B C),
             (forall p b1 b2, ps1 p = Some b1 ->
                         ps2 p = Some b2 ->
                         m1 b1 = m2 b2) ->
             compose ps1 m1 =  compose ps2 m2.
Proof.
  intros.
  apply functional_extensionality;
    intros p.
  unfold compose.

  remember (ps1 p) as b1; destruct b1.
  - destruct (same_dom_maps_some ps1 D) with (C:=B)(m2:=ps2)(a:=p)(b:=b); auto;
      crush.
    eauto.

  - symmetry in Heqb1.
    match goal with
    | [Hmap : ?m1 _ = None,
              Hdom1 : dom ?m1 ?D,
                      Hdom2 : dom ?m2 ?D |-_] =>
      eapply (same_dom_maps_none m1 D Hdom1 m2) in Hmap; auto
    end;
      crush.
Qed.

Lemma ref_equivalence_refl :
  forall m r, ref_equiv m r m r.
Proof.
  intros;
    destruct r;
    simpl;
    auto.
Qed.

Hint Resolve ref_equivalence_refl.
Hint Rewrite ref_equivalence_refl.

Lemma stmt_equivalence_refl :
  forall m s, stmt_equiv m s m s.
Proof.
  intros m s;
    generalize m;
    clear m;
    induction s;
    intros;
    auto.

  - apply eq_meth; crush.

Qed.

Hint Resolve stmt_equivalence_refl.
Hint Rewrite stmt_equivalence_refl.

Lemma equivalent_reduction :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall σ1' σ2', config_equiv σ1 σ1' ->
                        M ∙ σ1' ⤳ σ2' ->
                        config_equiv σ2 σ2'.
Proof.
  intros M σ1 σ2 Hred;
    inversion Hred;
    intros σ1' σ2' Hequiv Hred';
    subst;
    intros.

  - (* r_meth *)
    repeat equiv_unfold;
      [
      |crush].
    match goal with
    | [H : contn ϕ = _ |- _] => rewrite H in *
    end.
    crush.
    repeat equiv_unfold.
    inversion Hred';
      subst;
      match goal with
      | [H1 : contn _ = c_stmt (s_stmts (s_meth _ _ _ _) _),
              H2 : contn _ = c_stmt (s_stmts (s_meth _ _ _ _) _) |- _] => idtac
      | [|- _] => crush
      end.
    match goal with
    | [H : (_, _) = (_, _) |- _] => inversion H; subst
    end.
    apply conf_equiv.
    rewrite H9 in H10;
      inversion H10;
      subst.
    apply equivalent_interpretation with (ϕ':=ϕ)(ψ':=ψ)(y:=y) in H12;
      auto.
    interpretation_rewrite;
      match goal with
      | [H : v_addr _ = v_addr _ |- _] => inversion H; subst
      end.
    apply eq_cons_stack; simpl.
    + apply eq_frm; auto.
      
      * apply eq_stmt; auto.
        simpl.
        repeat match goal with
               | [H1 : ?f ?x = Some ?y1,
                       H2 : ?f ?x = Some ?y2 |- _] => rewrite H1 in H2; inversion H2; subst
               end.
        rewrite equal_composition with (D:=zs0)(ps1:=ps)(ps2:=ps0)(m2:=vMap ϕ0); auto.
        
    + apply eq_cons_stack; auto.
      apply eq_frm; auto.
      simpl.
      apply eq_hole; auto.

  - (* fAssgn *)
    repeat equiv_unfold; [|crush].
    match goal with
    | [H1 : contn _ = c_stmt (s_stmts (s_asgn _ _) _) |- _] => rewrite H1 in *
    end.
    match goal with
    | [H : c_stmt _ = c_stmt _ |- _] => inversion H; subst
    end.
    repeat equiv_unfold.
    inversion Hred';
      subst;
      match goal with
      | [H1 : contn _ = c_stmt (s_stmts (s_asgn _ _) _),
              H2 : contn _ = c_stmt (s_stmts (s_asgn _ _) _) |- _] => idtac
      | [|- _] => crush
      end;
      [|crush].
    match goal with
    | [H : (_, _::_) = (_, _::_) |- _] => inversion H; subst
    end.
    repeat map_rewrite; simpl in *.
    apply conf_equiv.
    apply eq_cons_stack; auto.
    match goal with
    | [H1 : contn ?ϕ = c_stmt _,
            H2 : _ = contn ?ϕ |- frame_equiv _ (update_ϕ_map ?ϕ _ _)] =>
      rewrite H1 in H2;
        inversion H2;
        subst
    end.
    match goal with
    | [H1 : ⌊ ?y1 ⌋ (?χ, ?ϕ1::?ψ1) ≜ ?v1,
            H2 : ⌊ ?y2 ⌋ (?χ, ?ϕ2::?ψ2) ≜ ?v2 |- frame_equiv (update_ϕ_map ?ϕ2 _ _) (update_ϕ_map ?ϕ1 _ _)] =>
      apply equivalent_interpretation with (ϕ':=ϕ2)(ψ':=ψ2)(y:=y2) in H1;
        auto;
        interpretation_rewrite;
        inversion H1;
        subst
    end.
    interpretation_rewrite.
    apply eq_frm; simpl; eauto.
    repeat match goal with
           | [H : contn ?ϕ = _ |- context[contn ?ϕ]] => rewrite H
           end.
    apply eq_stmt; simpl.
    match goal with
    | [|- stmt_equiv _ (s_stmts _ _) _ (s_stmts _ _)] =>
      apply eq_stmts
    end;
      eauto.

    
Qed.
                        
                   

Lemma reductions_under_equivalent_configurations :
  forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳… σ2 ->
                 forall σ1', config_equiv σ1 σ2 ->
                        exists .
*)