Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Print reduction.

Module SafeExample.

(**
∀s.[s : Safe ∧ s.treasure <> null ∧ will(s.treasure = null) 
        ⟶ ∃o.[external(o) ∧ (o access s.secret)]]
 *)
  

  (** DAO Definition *)

  Definition Safe := classID 1.

  Definition treasure := fieldID 0.

  Definition secret := fieldID 1.

  Definition take := methID 0.

  Definition scr := bnd 0.

  Definition x := bnd 1.

  Definition y := bnd 2.

  Definition takeBody := (x ⩦ (e_null);
                         (s_if ((e_var scr) ⩵ (e_acc_f (e_var this) secret))
                               ((r_ y) ⩦′ (this ◌ secret) ; ((this ◌ secret) ⩦′ (r_ x)) ; (s_rtrn y))
                               (s_rtrn x)) ;
                         (s_rtrn x)).

  Definition SafeDef := clazz Safe
                              (treasure :: secret :: nil)
                              (update
                                 take (scr :: nil, takeBody)
                                 empty)
                              empty.

  (** MyModule Definition *)

  Definition MyModule := (update
                            Safe SafeDef
                            empty).

End SafeExample.
