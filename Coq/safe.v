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
  

  (** Safe Definition *)

  Definition Safe := classID 1.

  Definition treasure := fieldID 0.

  Definition secret := fieldID 1.

  Definition take := methID 0.

  Definition scr := bnd 0.

  Definition takeBody := s_stmts (s_if (e_eq scr (e_acc_f this secret) )).

  Definition SafeDef := clazz Safe
                              (treasure :: secret :: nil)
                              (update
                                 take (nil, takeBody)
                                 empty)
                              empty.

  (** MyModule Definition *)

  Definition MyModule := (update
                            Boundary BoundaryDef
                            (update
                               Inside InsideDef
                               empty)).

End SafeExample.
