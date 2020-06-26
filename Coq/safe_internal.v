Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import hoare.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

  (**
     #<h1>#Safe#</h1>#
    In this file I provide a proof of the Safe example in the FASE2020 paper.
   *)

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
                                    (((e_hole 0) ⩵ (e_acc_f (e_var this) secret))
                                       ⩒
                                       (e_acc_g (e_acc_f (e_var this) secret) internal_g (e_hole 0)))).
  (**
#<h3>#internal_to#</h3>#
We define the #<code>#internal_to#</code># predicate below. We assume that
every data structure uses a ghost field define what is 
considered "internal".

Question: do we want to define a "default" internal? i.e. 
#<code>#internal_to x y := x == y ∨ x.internal_g(y)#</code>#
  *)
  Definition internal_to (x y: a_var) :=
    a_expr (ex_acc_g (ex_var x) internal_g (ex_var y)).
  
(**
#<h3>#always#</h3>#
Below we provide some definitions of "always": 
#<code>#always_will A#</code>#, #<code>#always_was A#</code>#, and #<code>#always A#</code>#
These are used in the proof, of the Safe example, but perhaps they might be pushed to a more
general file.
 *)
  
  Definition always_will (A : asrt) :=
    ¬ (a_will (¬ A)).

  Definition always_was (A : asrt) :=
    ¬ (a_was (¬ A)).

  Definition always (A : asrt) :=
    A ∧ (always_was A) ∧ (always_will A).

(**
#<h2>#Proof Sketch#</h2>#
Here I provide a sketch of the proof.

We first prove the following lemma: #<code>#safe_does_not_expose_secret#</code># that 
states that for all Safes #<code>#s#</code>#, if no objects external to #<code>#s#</code>#
have access to #<code>#s.secret#</code>#, then there will never be an external object 
with access to #<code>#s.secret#</code>#.

*)

  Lemma safe_does_not_expose_secret :
    forall M σ σ0 s s', MyModule ⦂ M ◎ σ … σ0 ⊨ (a_class s Safe) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (ex_acc_f (ex_var s) secret ⩶ (ex_var s')) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (¬ (∃x∙ (¬ (internal_to s (a♢ 0))
                                                    ∧
                                                    ((a♢ 0) access s')))) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ always_will (¬ (∃x∙ (¬ (internal_to s (a♢ 0))
                                                                ∧
                                                                ((a♢ 0) access s')))).
  Proof.
  Admitted.

(**
The second lemma is given below (#<code>#treasure_removed_implies_will_external_access#</code>#).
We demonstrate that if the treasure of s is ever changed, then it follows that at some point in 
the future a call to #<code>#take#</code># will be made with #<code>#s.secret#</code># as the 
argument.
*)

  Lemma treasure_removed_implies_take_called :
    forall M σ σ0 s s', MyModule ⦂ M ◎ σ … σ0 ⊨ (a_class s Safe) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (ex_acc_f (ex_var s) secret ⩶ (ex_var s')) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ ((ex_acc_f (ex_var s) treasure) ⩶̸ (ex_null)) ->
                   MyModule ⦂ M ◎ σ … σ0 ⊨ (a_will ((ex_acc_f (ex_var s) treasure) ⩶̸ (ex_null))) ->
                   exists x β, MyModule ⦂ M ◎ σ … σ0 ⊨ ((x calls s ▸ (am_ take) ⟨ β ⟩) ∨
                                                   (a_will (x calls s ▸ (am_ take) ⟨ β ⟩))).
  Proof.
  Admitted.

(**
By the law of the excluded middle, the x referenced in the above lemma, is
either internal to #<code>#s#</code># or it is not. If it is, then since 
the current object is external to #<code>##</code># it follows that there is a
*)

  Lemma 

  Definition HolisticSpec := (∀x∙ (∀x∙(((∀x∙ ((a_name (a♢ 0) this)
                                                ⟶
                                                (¬ internal_to (a♢ 2) (a♢ 0))))
                                        ∧
                                        (a_class (a♢1) Safe)
                                        ∧
                                        ((ex_acc_f (e♢1) secret) ⩶ (e♢0))
                                        ∧
                                        ((ex_acc_f (e♢1) treasure) ⩶̸ (ex_null))
                                        ∧
                                        (a_will ((ex_acc_f (e♢1) treasure) ⩶ (ex_null))))
                                         ⟶
                                         (∃x∙ ((¬ internal_to (a♢2) (a♢0))
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
  Qed.

End SafeExample.
