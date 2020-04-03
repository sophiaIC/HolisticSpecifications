Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module SafeExample.

  (** #<h3># Safe example: #</h3># *)
  (** ---------------------------------------------------- *)
  (** #<code># >MyModule = { #</code># *)
  (** #<code># >  Inside = {} #</code># *)
  (** #<code># >  Boundary = { #</code># *)
  (** #<code># >    field inside : Inside #</code># *)
  (** #<code># >    meth expose() = {return this.inside} #</code># *)
  (** #<code># >  } #</code># *)
  (** #<code># >} #</code># *)
  (** --------------------------------------------------- *)
  (** #<code># we want to prove: #</code># *)
  (**  *)
  (** #<code># >MyModule ⊨  #</code># *)
  (** #<code># >(∀ b, b : Boundary, ∀ i, (b.inside = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
  (** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
  (** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
  (**  *)
  (**  *)

(*  Definition Inside := classID 6.

  Definition InsideDef := clazz Inside
                                nil
                                empty
                                empty.

  (** Boundary Definition *)

  Definition Boundary := classID 7.

  Definition inside := fieldID 0.

  Definition expose := methID 0.

  Definition x := bnd 10.

  Definition exposeBody := s_stmts (s_asgn (r_var x) (r_fld this inside))
                                   (s_rtrn x).

  Definition BoundaryDef := clazz Boundary
                                  (inside :: nil)
                                  (update
                                     expose (nil, exposeBody)
                                     empty)
                                  empty.

  (** MyModule Definition *)

  Definition MyModule := (update
                            Boundary BoundaryDef
                            (update
                               Inside InsideDef
                               empty)).

  

  Theorem safe :
    ∀x∙ (((a_class (a♢0) Safe)
          ∧
          (¬ ((e_acc_f (a♢0) treasure) ⩦ e_null))
          ∧
          (a_will (((e_acc_f (a♢0) treasure) ⩦ e_null))))
           ⇒
           (∃x∙((a♢ 0) external
                ∧
                (∀x∙((e_acc_f (a♢2) treasure) ⩦ (e♢0)) ⇒ ((a♢ 1) access (a♢0)))
               )
           )
        ).*)

End SafeExample.
