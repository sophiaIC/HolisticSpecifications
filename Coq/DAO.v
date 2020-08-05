Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import function_operations.
Require Import hoare.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ZArith.

Module SimpleDAO.

  Definition a := bnd 1.

  Definition b := bnd 2.

  Definition c := bnd 3.

  Definition x := bnd 4.

  Definition y := bnd 5.

  Definition z := bnd 6.
  
  Definition id := bnd 7.

  Definition amt := bnd 8.

  Definition name := fieldID 1.

  Definition balance := fieldID 2.

  Definition ether := fieldID 3.

  Definition send := methID 1.

  Definition repay := methID 2.

  Definition repayDef1 := (a ≔′ e_int 0) ;;
                          ((r_ x ≔ (this ◌ balance)) ;;
                           ((r_ y ≔ (this ◌ ether)) ;;
                            ((b ≔′ e_minus (e_var y) (e_var x)) ;;
                             ((s_if ((e_var x) ⩽ (e_var y))
                                    (
                                      s_if (e_var id ⩵ e_acc_f (e_var this) name)
                                           (this ◌ ether ≔ (r_ b) ;;
                                            (s_meth z id send (update amt x empty) ;;
                                             (this ◌ balance ≔ (r_ a))))
                                           (s_rtrn a)
                                    )
                                    (s_rtrn a)) ;;
                              s_rtrn a)))).

  Definition repayDef2 := (a ≔′ e_int 0) ;;
                          ((r_ x ≔ (this ◌ balance)) ;;
                           ((r_ y ≔ (this ◌ ether)) ;;
                            ((b ≔′ e_minus (e_var y) (e_var x)) ;;
                             ((s_if ((e_var x) ⩽ (e_var y))
                                    (
                                      s_if (e_var id ⩵ e_acc_f (e_var this) name)
                                           (this ◌ ether ≔ (r_ b) ;;
                                            ((this ◌ balance ≔ (r_ a)) ;;
                                             s_meth z id send (update amt x empty)))
                                           (s_rtrn a)
                                    )
                                    (s_rtrn a)) ;;
                              s_rtrn a)))).

  Definition DAO := classID 1.

  Definition DAODef1 := clazz DAO
                              (name :: balance :: ether :: nil)
                              nil
                              (update repay ((id :: nil),repayDef1) empty)
                              empty.

  Definition DAODef2 := clazz DAO
                              (name :: balance :: ether :: nil)
                              nil
                              (update repay ((id :: nil),repayDef2) empty)
                              empty.

  Definition DAOModule1 := update DAO DAODef1 empty.

  Definition DAOModule2 := update DAO DAODef2 empty.

  Definition DAOSPEC1 :=
    (∀x∙ ((a_class (a♢ 0) DAO ∧
           (a_expr (ex_acc_f (e♢ 0) balance ⩽′ (ex_acc_f (e♢ 0) ether))))
            ⟶
            (a_next (a_expr (ex_acc_f (e♢ 0) balance ⩽′ (ex_acc_f (e♢ 0) ether))))
    )).

  Definition Client := classID 2.

  Definition sendBody := s_rtrn amt.

  Definition ClientDef := clazz Client
                                nil
                                nil
                                (update send (amt :: nil, sendBody) empty)
                                empty.

  Definition ClientModule := update Client ClientDef empty.

  Definition αthis := address 0.

  Definition Object := new Object empty.

  Definition χ0 := (update αthis Object empty).

  Definition β0 := update this (v_addr αthis) empty.

  Definition client := bnd 9.

  Definition αclient := address 1.

  Definition αDAO := address 2.

  Definition clientObj := new Client empty.

  Definition daoFields := update name (v_addr αclient)
                                 (update balance (v_int 10)
                                         (update ether (v_int 10)
                                                 empty)).

  Definition DAOObj := new DAO daoFields.

  Definition dao := bnd 10.

  Definition ten := bnd 11.

  Definition daoParams := update name client
                                 (update balance ten
                                         (update ether ten
                                                 empty)).

  Definition s0 := (s_new client Client empty) ;;
                   ((ten ≔′ (e_int 10)) ;;
                    ((s_new dao DAO daoParams) ;;
                     (s_meth c dao repay (update id client empty) ;;
                      (s_rtrn c)))).

  Definition c0 := c_stmt s0.

  Definition ϕ0 := frm β0 c0.

  Definition σ0 := (χ0, ϕ0 :: nil).

  Definition χA := (update αDAO DAOObj
                           (update αclient clientObj χ0)).

  Definition βA := (update dao (v_addr αDAO)
                           (update ten (v_int 10)
                                   (update client (v_addr αclient) β0))).

  Definition sA := (s_meth c dao repay (update id client empty) ;;
                    s_rtrn c).

  Definition cA := c_stmt sA.

  Definition ϕA := frm βA cA.

  Definition σA := (χA, ϕA :: nil).

  Definition updatedDAO := new DAO
                               (update ether (v_int 0) daoFields).

  Definition χB := update αDAO updatedDAO
                          χA.

  Definition βB' := update b (v_int 0)
                           (update y (v_int 10)
                                   (update x (v_int 10)
                                           (update a (v_int 0)
                                                   (update this (v_addr αDAO) empty)))).

  Definition sB' := s_rtrn a.

  Definition cB' := c_hole z sB'.

  Definition ϕB' := frm βB' cB'.

  Definition βB := (update this (v_addr αclient) empty).

  Definition cB := c_stmt (s_rtrn a).

  Definition ϕB := frm βB cB.

  Definition σB := (χB, ϕB :: ϕB' :: nil).

  Lemma exists_linking_of_DAOModule1_ClientModule :
    exists M, DAOModule1 ⋄ ClientModule ≜ M.
  Proof.

  Admitted.

  Lemma σ0_initial :
    initial σ0.
  Proof.

  Admitted.

  Lemma σ0_reduces_to_σA :
    DAOModule1 ⦂ ClientModule ⦿ σ0 ⤳⋆ σA.
  Proof.
    
  Admitted.

  Lemma σA_maps_αDAO_to_DAOObj :
    ⟦ αDAO ↦ DAOObj ⟧ ∈ σA.
  Proof.
    repeat map_rewrite;
      simpl.
    unfold χA.
    repeat map_rewrite.
  Qed.

  Lemma σA_reduces_to_σB :
    DAOModule1 ⦂ ClientModule ⦿ σA ⤳ σB.
  Proof.

  Admitted.

  Lemma balance_neq_ether :
    balance <> ether.
  Proof.
    unfold balance, ether;
      crush.
  Qed.

  Lemma balance_neq_name :
    balance <> name.
  Proof.
    unfold balance, name;
      crush.
  Qed.

  Lemma σA_satisfies_SPEC_premise :
    DAOModule1 ⦂ ClientModule ◎ σ0 … σA
               ⊨ (a_class (a_ αDAO) DAO
                  ∧ a_expr (ex_acc_f (e_ αDAO) balance ⩽′ ex_acc_f (e_ αDAO) ether)).
  Proof.
    a_prop.

    - apply sat_class with (o:=DAOObj);
        auto.

    - destruct exists_linking_of_DAOModule1_ClientModule as [M].
      apply sat_exp with (M:=M)(e':=e_acc_f (e_val (v_addr αDAO)) balance ⩽
                                            e_acc_f (e_val (v_addr αDAO)) ether);
        auto.
      + apply decoupling.is_if;
          auto with chainmail_db.
      + apply v_if_false.
        * Open Scope Z_scope.
          apply v_nlt with (i1:=10)(i2:=10);
            [| |crush].
          Close Scope Z_scope.
          ** apply v_f_heap with (α:=αDAO)(o:=DAOObj);
               eauto with loo_db.
          ** apply v_f_heap with (α:=αDAO)(o:=DAOObj);
               eauto with loo_db.
        * apply v_if_true;
            auto with loo_db.
          apply v_equals with (v:=v_int 10).
          ** apply v_f_heap with (α:=αDAO)(o:=DAOObj);
               eauto with loo_db.
          ** apply v_f_heap with (α:=αDAO)(o:=DAOObj);
               eauto with loo_db.
  Qed.

  Lemma DAO1_nsat :
    ~ DAOModule1 ⊨m DAOSPEC1.
  Proof.
    unfold mdl_sat.
    intro Hcontra.
    specialize (Hcontra ClientModule).
    specialize (Hcontra σ0 σA exists_linking_of_DAOModule1_ClientModule).
    specialize (Hcontra σ0_initial).
    specialize (Hcontra σ0_reduces_to_σA).
    inversion Hcontra;
      subst;
      simpl in *.
    specialize (H4 αDAO DAOObj σA_maps_αDAO_to_DAOObj).
    a_prop.
    assert (DAOModule1 ⦂ ClientModule ◎ σ0 … σA
                       ⊨ (a_class (a_ αDAO) DAO
                          ∧ a_expr (ex_acc_f (e_ αDAO) balance ⩽′ ex_acc_f (e_ αDAO) ether)));
      [apply σA_satisfies_SPEC_premise|auto_specialize].
    repeat a_prop.
    inversion H4;
      subst.
    unfold σA in H2;
      repeat simpl_crush. 
    assert (DAOModule1 ⦂ ClientModule ⦿ σA ⤳ σB);
      [apply σA_reduces_to_σB|].
    (*unique_reduction_auto.

    inversion H9;
      subst.
    repeat match goal with
           | [H : is_exp _ _ |- _] =>
             inversion H;
               subst;
               clear H
           end.
    inversion H11;
      subst.
    - inversion H12;
        subst.
      
      inversion H6;
        subst.
      inversion H7;
        subst.
      repeat map_rewrite.
      simpl in H16.
      unfold χB in H16.
      repeat map_rewrite.
      inversion H16;
        subst.
      simpl in *.
      repeat map_rewrite.
      assert (balance <> ether);
        [apply balance_neq_ether|eq_auto].
      unfold daoFields in *;
        repeat map_rewrite.
      assert (balance <> name);
        [apply balance_neq_name|eq_auto; simpl_crush].

      inversion H10;
        subst.
      inversion H17;
        subst.
      repeat map_rewrite;
        simpl in *;
        unfold χB in *;
        repeat map_rewrite;
        simpl_crush.
      simpl in *;
        repeat map_rewrite;
        simpl_crush.
      crush.

    - inversion H13;
        subst.

      + inversion H14;
          subst.
        inversion H8;
          subst.
        repeat map_rewrite.
        simpl in *.
        unfold χB in *.
        repeat map_rewrite.
        inversion H6;
          subst.
        simpl in *.
        simpl_crush.
        simpl in *.
        repeat map_rewrite.
        assert (balance <> ether);
          [apply balance_neq_ether|eq_auto].
        unfold daoFields in *;
          repeat map_rewrite.
        assert (balance <> name);
          [apply balance_neq_name|eq_auto; simpl_crush].

        inversion H10;
          subst.
        inversion H17;
          subst.
        repeat map_rewrite;
          simpl in *;
          unfold χB in *;
          repeat map_rewrite;
          simpl_crush.
        simpl in *;
          repeat map_rewrite.
        simpl_crush.

      + inversion H15.*)
  Admitted. (* Julian: this used to work. I need figure out how it was broken *)

  Lemma repay_pre_post :
    forall M σ x y z, DAOModule2 ⦂ M ⦿ {pre:contn_is (s_meth x y repay (update id z empty))} σ {post:∅}.
  Proof.
    intros M σ.
  Admitted.

  Lemma DAO2_sat :
    DAOModule2 ⊨m DAOSPEC1.
  Proof.
    
  Admitted.
  

End SimpleDAO.

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
                              nil
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

End DAOExample.
