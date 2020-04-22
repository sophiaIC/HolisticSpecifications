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

Module DAOExample.
  

  (** DAO Definition *)

  Definition DAO := classID 1.

  Definition ether := fieldID 0.

  Definition amt := bnd 0.

  Definition x := bnd 1.

  Definition y := bnd 2.

  Definition repay := methID 0.

  Definition deposit := methID 1.

  Definition depositBody := ((r_ x) ≔ (this ◌ ether) ;;
                             ((r_ y) ≔ r_exp (e_plus (e_var amt) (e_var x))) ;;
                             ((this ◌ ether) ≔ (r_ y)) ;;
                             s_rtrn amt).

  Definition repayBody := ((r_ x) ≔ (this ◌ ether) ;;
                           ((r_ y) ≔ r_exp (e_int 0)) ;;
                           ((this ◌ ether) ≔ (r_ y)) ;;
                           s_rtrn x).

  Definition DAODef := clazz DAO
                              (ether :: nil)
                              (update
                                 repay (nil, repayBody)
                                 (update
                                    deposit (amt :: nil, depositBody)
                                    empty))
                              empty.

  (** MyModule Definition *)

  Definition MyModule := (update
                            DAO DAODef
                            empty).

End DAOExample.
