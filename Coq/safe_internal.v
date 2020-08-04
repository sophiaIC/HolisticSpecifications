Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import exp.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import hoare.
Require Import always.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

  (**
     #<h1>#Safe#</h1>#
    In this file I provide a proof of the Safe example in the FASE2020 paper.
   *)

(*Lemma not_always :
  forall M1 M2 σ0 χ ϕ ψ A, M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: ψ) ⊨ (¬ always_will A) ->
                      M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: ψ) ⊨ A ->
                      (exists σ, M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ /\
                            M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ ⊨ A /\
                            M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ ⊨ ¬ A) \/
                      M1 ⦂ M2 ◎ σ0 … (χ, ϕ :: ψ) ⊨ (a_next (¬ A)).
Proof.
  intros M1 M2 σ0 χ ϕ ψ A;
    intros.
  inversion H; subst.
  inversion H6;
    subst.
  inversion H7;
    subst.
  simpl_crush.

  destruct (pair_reduction_change M1 M2 σ0 σ') with (P:=fun M1 M2 σ => M1 ⦂ M2 ◎ (χ0, ϕ0 :: ψ0) … σ ⊨ A);
    auto.

  destruct (sat_excluded_middle M1 M2 σ0 (χ0, ϕ0 :: ψ0) (a_next (¬ A)));
    [right; auto|left].

  Print pair

  - exists σ'; repeat split; auto.
    
Qed.*)

Module SafeExample.

  (** #<h3>#Definitions#</h3># *)

  Definition Safe := classID 1.

  Definition treasure := fieldID 0.

  Definition secret := fieldID 1.

  Definition take := methID 0.

  Definition scr := bnd 1.

  Definition x := bnd 2.

  Definition y := bnd 3.

  (**
     #<h3>#Safe Definition#</h3>#
   *)

  Definition takeBody := ((r_ x) ≔ (r_exp (e_val (v_null)))) ;;
                         (((r_ y) ≔ (this ◌ treasure)) ;;
                          ((s_if ((e_var scr) ⩵ (e_acc_f (e_var this) secret))
                                 (((this ◌ treasure) ≔ (r_ x)) ;;
                                  (s_rtrn y))
                                 (s_rtrn x)) ;;
                           (s_rtrn x))).

  Definition SafeDef := clazz Safe
                              (treasure :: secret :: nil)
                              nil
                              (update
                                 take (scr :: nil, takeBody)
                                 empty)
                              empty.

  Definition MyModule := (update
                            Safe SafeDef
                            empty).

  Definition safeInternalBody := (((e_hole 0) ⩵ (e_var this))
                                    ⩒
                                    ((e_hole 0) ⩵ (e_acc_f (e_var this) secret))).
(*                                       ⩒
                                       (e_acc_g (e_acc_f (e_var this) secret) private (e_hole 0)))).*)
  (**
#<h3>#internal_to#</h3>#
We define the #<code>#internal_to#</code># predicate below. We assume that
every data structure uses a ghost field define what is 
considered "internal".

Question: do we want to define a "default" internal? i.e. 
#<code>#internal_to x y := x == y ∨ x.internal_g(y)#</code>#
  *)
(*  Definition internal_to (x y: a_var) :=
    a_expr (ex_acc_g (ex_var x) internal_g (ex_var y)).*)
  
(**
#<h3>#always#</h3>#
Below we provide some definitions of "always": 
#<code>#always_will A#</code>#, #<code>#always_was A#</code>#, and #<code>#always A#</code>#
These are used in the proof, of the Safe example, but perhaps they might be pushed to a more
general file.
 *)

(**
#<h2>#Proof Sketch#</h2>#
Here I provide a sketch of the proof.

We first prove the following lemma: #<code>#safe_does_not_expose_secret#</code># that 
states that for all Safes #<code>#s#</code>#, if no objects external to #<code>#s#</code>#
have access to #<code>#s.secret#</code>#, then there will never be an external object 
with access to #<code>#s.secret#</code>#.

*)

(*  Lemma safe_does_not_expose_secret :
    forall M σ σ0 s s', MyModule ⦂ M ◎ σ … σ0 ⊨ (a_class s Safe) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (ex_acc_f (ex_var s) secret ⩶ (ex_var s')) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (¬ (∃x∙ (¬ (internal_to s (a♢ 0))
                                                    ∧
                                                    ((a♢ 0) access s')))) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ always_will (¬ (∃x∙ (¬ (internal_to s (a♢ 0))
                                                                ∧
                                                                ((a♢ 0) access s')))).
  Proof.
    intros.
    unfold always_will.
    apply sat_not.
    apply not_sat_implies_nsat.
    intro Hcontra.
    inversion Hcontra;
      subst.
    apply negate_elim_sat in H9.
    inversion H9;
      subst.
    simpl in *;
      a_prop.
    
    
  Admitted.*)

(**
The second lemma is given below (#<code>#treasure_removed_implies_will_external_access#</code>#).
We demonstrate that if the treasure of s is ever changed, then it follows that at some point in 
the future a call to #<code>#take#</code># will be made with #<code>#s.secret#</code># as the 
argument.
*)

(*  Lemma treasure_removed_implies_take_called :
    forall M σ σ0 s s', MyModule ⦂ M ◎ σ … σ0 ⊨ (a_class s Safe) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (ex_acc_f (ex_var s) secret ⩶ (ex_var s')) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ ((ex_acc_f (ex_var s) treasure) ⩶̸ (ex_null)) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (a_will ((ex_acc_f (ex_var s) treasure) ⩶̸ (ex_null))) ->
                   exists x β, MyModule ⦂ M ◎ σ … σ0 ⊨ ((x calls s ▸ (am_ take) ⟨ β ⟩) ∨
                                                   (a_will (x calls s ▸ (am_ take) ⟨ β ⟩))).
  Proof.
  Admitted.*)

(**
By the law of the excluded middle, the x referenced in the above lemma, is
either internal to #<code>#s#</code># or it is not. If it is, then since 
the current object is external to #<code>#s#</code># it follows that there 
is 
 *)

  Parameter internal_step_MyModule :
    forall M σ, internal_step MyModule M σ ->
           exists x y myScr s, contn_is (s_meth x y take (update scr myScr empty) ;; s) σ.

  Lemma external_step_access_to_this :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                   external_step M1 M2 σ1 ->
                   forall σ0 α1 α2, M1 ⦂ M2 ◎ σ0 … σ1 ⊨ a_name α1 this ->
                               M1 ⦂ M2 ◎ σ0 … σ2 ⊨ a_name α2 this ->
                               M1 ⦂ M2 ◎ σ0 … σ1 ⊨ (α1 access α2).
  Proof.
    
  Admitted.

  Parameter safe_private :
    forall {M σ0 σ s x}, MyModule ⦂ M ◎ σ0 … σ ⊨ a_private (a_ s) (a_ x) ->
                    MyModule ⦂ M ◎ σ0 … σ ⊨ a_class (a_ s) Safe ->
                    MyModule ⦂ M ◎ σ0 … σ ⊨ (((e_ s) ⩶ (e_ x)) ∨ (ex_acc_f (e_ s) secret ⩶ (e_ x))).

  Parameter secret_immutable :
    forall M σ0 σ s v, MyModule ⦂ M ◎ σ0 … σ ⊨ (a_class (a_ s) Safe) ->
                  MyModule ⦂ M ◎ σ0 … ̱ ⊨
                           {pre: (ex_acc_f (e_ s) secret) ⩶ (ex_val v) }
                           σ
                           {post: (ex_acc_f (e_ s) secret) ⩶ (ex_val v)}.

  Lemma this_not_internal :
    forall {M1 M2 σ0 σ x}, M1 ⦂ M2 ◎ σ0 … σ ⊨ a_name x this ->
                      forall {σ'}, M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                              M1 ⦂ M2 ◎ σ0 … σ ⊨ ¬ (x internal).
  Proof.
    intros.
    a_contradiction.
    match goal with
    | [H : _ ⦂ _ ◎ _ … _ ⊨ (_ internal) |-_] =>
      inversion H;
        subst;
        destruct_exists_loo
    end.
    match goal with
    | [H : _ ⦂ _ ◎ _ … _ ⊨ (a_name _ _) |-_] =>
      inversion H;
        subst
    end.
    match goal with
      | [H : _ ⦂ _ ⦿ _ ⤳ _ |- _] =>
        apply pair_reduction_external_self2 in H
    end.
    unfold external_self, is_external in *;
      repeat destruct_exists_loo;
      andDestruct.
    repeat simpl_crush.
  Qed.

  Lemma safe_is_internal :
    forall M σ0 σ x, MyModule ⦂ M ◎ σ0 … σ ⊨ (a_class x Safe) ->
                MyModule ⦂ M ◎ σ0 … σ ⊨ (x internal).
  Proof.
    intros.
    match goal with
    | [H : _ ⦂ _ ◎ _ … _ ⊨ a_class _ _ |- _] =>
      inversion H;
        subst
    end.
    eapply sat_intrn; eauto.
    exists SafeDef.
    eauto.
  Qed.

  Lemma invariant_class_name :
    forall {M1 M2 σ0 σ α C}, M1 ⦂ M2 ◎ σ0 … ̱ ⊨ {pre: a_class α C} σ {post: a_class α C}.
  Proof.
    intros.
    apply ht_pr;
      intros.
    inversion H;
      subst.
    match goal with
    | [H : ?Ma ⦂ ?Mb ◎ _ … ?σa ⊨ a_class ?α ?C |-
       ?Ma ⦂ ?Mb ◎ _ … ?σb ⊨ a_class ?α ?C] =>
      edestruct (pair_reduction_preserves_addr_classes);
        eauto
    end.
    andDestruct.
    eapply sat_class;
      eauto.
  Qed.

  Lemma safe_does_not_expose_secret :
    forall M s myScr σ0 σ, MyModule ⦂ M ◎ σ0 … ̱ ⊨
                               {pre: (a_class (a_ s) Safe)
                                     ∧
                                     ((ex_acc_f (e_ s) secret) ⩶ (e_ myScr))
                                     ∧
                                     (¬ is_private (a_ s) this)
                                     ∧
                                     ∀x∙ ((a_private (a_ s) (a♢ 0))
                                          ∨
                                          (¬ ((a♢ 0) access (a_ myScr))))}
                               σ
                               {post: (a_class (a_ s) Safe)
                                      ∧
                                      ((ex_acc_f (e_ s) secret) ⩶ (e_ myScr))
                                      ∧
                                      (¬ is_private (a_ s) this)
                                      ∧
                                      ∀x∙ ((a_private (a_ s) (a♢ 0))
                                           ∨
                                           (¬ ((a♢ 0) access (a_ myScr))))}.
  Proof.
    intros.
    apply ht_pr;
      intros.
    destruct (pair_reduction_inversion_hoare MyModule M σ σ');
      auto.

(*    - a_prop;
        simpl in *;
        auto.

      + destruct (wf_exists_self σ) as [α];
          auto;
          destruct_exists_loo;
          andDestruct.

        unfold is_private in *;
          a_prop.

        a_intros.
        a_contradiction.
        a_prop.

        specialize (H2 α o);
          auto_specialize.
        a_prop.
        destruct H2.

        * inversion H2;
            subst.
          inversion H14;
            subst.
          crush.
        * apply safe_private in H8;
            auto;
            a_prop.
          ** destruct H8.
             *** exp_auto;
                   simpl_crush.
                 match goal with
                 | [ H : _ ⦂ _ ◎ _ … ?σ ⊨ a_class _ _,
                     Hred : _ ⦂ _ ⦿ ?σ ⤳ _ |- _] =>
                 eapply (hoare_triple_pr_inversion
                           (invariant_class_name)
                           Hred)
                   in H
                 end.
                 match goal with
                 | [H : _ ⦂ _ ◎ _ … ?σ ⊨ a_class _ _ |- _] =>
                   apply safe_is_internal in H
                 end.
                 match goal with
                 | [H : _ ⦂ _ ◎ _ … ?σ ⊨ a_name _ this,
                    Hred : _ ⦂ _ ⦿ _ ⤳ ?σ |- _] =>
                   eapply (this_not_internal) in H;
                     [inversion H; subst|apply Hred]
                 end.
                 a_prop.

             *** exp_auto.
                 admit.
          ** *)
        

  Admitted.

  Definition treasure_removed_implies_access :
    forall M σ0 σ s myScr, MyModule ⦂ M ◎ σ0 … σ ⊨ (a_class (a_ s) Safe) ->
                      MyModule ⦂ M ◎ σ0 … σ ⊨ ((ex_acc_f (e_ s) secret) ⩶ (e_ myScr)) ->
                      MyModule ⦂ M ◎ σ0 … σ ⊨ ((ex_acc_f (e_ s) treasure) ⩶̸ (ex_null)) ->
                      MyModule ⦂ M ◎ σ0 … σ ⊨ (a_will ((ex_acc_f (e_ s) treasure) ⩶ (ex_null))) ->
                      MyModule ⦂ M ◎ σ0 … σ ⊨ (a_will (∃x∙ ((a_name (a♢ 0) this)
                                                            ∧
                                                            ((a♢ 0) access (a_ myScr))
                                              ))).
  Proof.

  Admitted.

  Definition HolisticSpec := (∀x∙ (∀x∙(((¬ is_private (a♢ 1) this)
                                        ∧
                                        (a_class (a♢1) Safe)
                                        ∧
                                        ((ex_acc_f (e♢1) secret) ⩶ (e♢0))
                                        ∧
                                        ((ex_acc_f (e♢1) treasure) ⩶̸ (ex_null))
                                        ∧
                                        (a_will ((ex_acc_f (e♢1) treasure) ⩶ (ex_null))))
                                         ⟶
                                         (∃x∙ ((¬ a_private (a♢2) (a♢0))
                                               ∧
                                               ((a♢0) access (a♢1))))
                             ))).

  Lemma Safe_satisfies_HolisticSpec :
    MyModule ⊨m HolisticSpec.
  Proof.
    unfold mdl_sat, HolisticSpec;
      intros.
    a_intros;
      a_prop;
      simpl in *.

    assert (Hacc : MyModule ⦂ M' ◎ σ0 … σ ⊨ (a_will (∃x∙ ((a_name (a♢ 0) this)
                                                  ∧
                                                  ((a♢ 0) access (a_ α0))
           ))));
      [eapply treasure_removed_implies_access; eauto|].

    apply (entails_implies (not_all_x_ex)).

    a_contradiction.
    inversion H7;
      subst;
      simpl in *.

    assert (Hinv : MyModule ⦂ M' ◎ σ0 … σ ⊨ ((a_class (a_ α) Safe)
                                             ∧
                                             ((ex_acc_f (e_ α) secret) ⩶ (e_ α0))
                                             ∧
                                             (¬ is_private (a_ α) this)
                                             ∧
                                             ∀x∙ ((a_private (a_ α) (a♢ 0))
                                                  ∨
                                                  (¬ ((a♢ 0) access (a_ α0))))));
      auto.
    - a_prop;
        auto.
      + unfold is_private.
        apply (entails_implies not_ex_x_all_not_2).
        a_intros.
        a_contradiction.
        a_prop.
        specialize (H4 α1 o1);
          auto_specialize.
        a_prop.
        destruct H4;
          a_prop.
      + a_intros.
        specialize (Hcontra α1 o1);
          auto_specialize.
        a_prop.
        destruct Hcontra;
          [left|right];
          a_prop;
          auto.
    - apply invariant_always_will in Hinv;
        [|apply safe_does_not_expose_secret].
      repeat (a_always; andDestruct).
      a_prop.
      apply (always_will_will_conj Hb) in Hacc.
      apply (always_will_will_conj Hb0) in Hacc.
      inversion Hacc;
        subst;
        simpl in *.
      a_prop;
        simpl in *.
      inversion H9;
        subst;
        simpl in *.
      a_prop.
      specialize (H14 α1 o1);
        auto_specialize.
      a_prop.
      destruct H14;
        subst;
        a_prop.
      + apply sat_and with (A2:=a_name (a_ α1) this) in H14;
          [|auto].
        apply (entails_implies a_private_is_private) in H14.
        a_prop.
  Qed.

End SafeExample.
