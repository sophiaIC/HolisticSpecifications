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

Module DAOExample.

  Definition x := bnd 1.

  Definition y := bnd 2.

  Definition z := bnd 3.

  Definition amt := bnd 4.

  Definition id := bnd 5.

  (* List Definition *)

  Definition List := classID 1.

  Definition head := fieldID 1.

  Definition tail := fieldID 2.

  Definition getHead := methID 1.

  Definition getHeadBody := (r_ x) ≔ (this ◌ head) ;;
                            (s_rtrn x).

  Definition getTail := methID 2.

  Definition getTailBody := (r_ x) ≔ (this ◌ tail) ;;
                            (s_rtrn x).

  Definition ListDef := clazz List
                              (tail :: head :: nil)
                              (update getHead (nil, getHeadBody)
                                      (update getTail (nil, getTailBody)
                                              empty))
                              empty.

  Definition Account := classID 2.

  Definition name := fieldID 3.

  Definition balance := fieldID 4.

  Definition deposit := methID 3.

  Definition depositBody := (r_ x) ≔ (this ◌ name) ;;
                            ((s_if ((e_var x) ⩵ (e_var id))
                                   (((r_ y) ≔ (this ◌ balance) ;;
                                     (z ≔′ (e_plus (e_var y) (e_var amt)) ;;
                                      ((this ◌ balance) ≔ (r_ z) ;;
                                       (s_rtrn x)))))
                                   (s_rtrn x)) ;;
                             (s_rtrn x)).

  Definition withdraw := methID 4.

  Definition withdrawBody := (r_ x) ≔ (this ◌ balance) ;;
                             (y ≔′ (e_null) ;; 
                              (s_if ((e_var x) ⩾ (e_var amt))
                                    ((z ≔′ e_plus (e_var x) (e_var amt));;
                                     ((this ◌ balance) ≔ (r_ z);; s_rtrn y))
                                    (s_rtrn y)) ;;
                              (s_rtrn y)).
  
  
  (** DAO Definition *)

  Definition DAO := classID 1.

  Definition accountBook := fieldID 3.

  Definition ether := fieldID 4.

  (*Definition x := bnd 1.

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
                            empty).*)

End DAOExample.
