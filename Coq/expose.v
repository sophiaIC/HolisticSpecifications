Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import chainmail_properties.
Require Import classical_properties.
Require Import chainmail_extended_properties.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module ExposeExample.

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

  (** Inside Definition  *)

  Definition Inside := classID 6.

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


(*  Theorem expose_example_will :
    MyModule ⊨m (∀x∙∀x∙(((a_class (e♢1) Boundary)
                         ∧
                         ((e_acc_f (e♢1) inside) ⩶ (e♢0))
                         ∧
                         ((guards (a♢1) (a♢0))))
                        ∧
                        (a_will (¬ guards (a♢1) (a♢0)))
                          ⇒
                          (a_will (∃x∙((a♢0) calls (a♢2) ∎ expose ⟨ empty ⟩)) ∨
                           ((a_ this) calls (a♢1) ∎ expose ⟨ empty ⟩)))).
  Proof.
    unfold mdl_sat;
      intros;    
      repeat (a_intros; a_prop);
      simpl in *.
    
    repeat destruct_exists_loo.
    destruct σ as [χ]; simpl in *; subst.

    inversion H6; subst.
    inversion H10; subst.

    - right.
      admit.

    - assert (σ_wf (χ0, ϕ0::ψ0)).
      match goal with
      | [H : update_σ_map _ _ _ = ?σ |- context[?σ]] =>
        rewrite <- H
      end.
      repeat (eapply σ_wf_update; eauto).
      apply arising_wf with (M1:=MyModule)(M2:=M'); auto.
      let someσ := fresh "σ" in
      destruct (adaptation_exists_wf (χ0,ϕ0::ψ0) σ) as [someσ];
        auto.
      apply pair_reduction_preserves_config_wf
        with (M1:=MyModule)(M2:=M')
             (σ1:=(χ0, ϕ0::nil));
        auto.
      eapply σ_wf_top_frame; eauto.

      destruct (sat_excluded_middle MyModule M' σ0 (guards (a_ z) (a_ z0))) as [Hsat|Hnsat].

      + destruct will_change_pair_reduction
          with (M1:=MyModule)(M2:=M')
               (A:=guards (a_ z) (a_ z0))
               (σ1:=σ)(σ1':=σ0)
               (σ2:=σ')(σ2':=σ'')
               (σ:=(χ0,ϕ0::ψ0));
          eauto with loo_db.
        * crush.
        * repeat destruct_exists_loo;
            andDestruct.
          left.
          let Ha := fresh "H" in
          let Hb := fresh "H" in
          destruct (pair_reductions_alt_definition MyModule M' σ σ1)
            as [Ha Hb];
            match goal with
            | [H : MyModule ⦂ M' ⦿ σ ⤳⋆ σ1 |- _] =>
              specialize (Ha H);
                destruct Ha
            end.

          ** destruct (pair_reduction_change_implies_method_call MyModule M' σ σ1);
               eauto with loo_db.
             *** repeat destruct_exists_loo;
                   andDestruct;
                   subst.
                 apply sat_will with (χ:=χ0)(ψ:=ψ0)(ϕ:=ϕ0)(σ':=(χ1,ϕ1::ψ1))(σ'':=σ0);
                   eauto with loo_db.
                 rewrite H9; auto.
                 admit.

             *** admit.

          ** admit.

        * admit.

      + admit.

  Admitted.*)

  (**
     expose_example_was does not work, because there is no way to ensure that 
     some frame in the stack below the identified frame in the past does not
     have access to inside. Thus, access could be granted purely by returning 
     from some method call. expose_example_will works because will restricts
     the stack to just the top frame, thus removing the possibility of returning
     to some lower frame.
   *)

  Theorem expose_example_was :
    MyModule ⊨m (∀x∙∀x∙((a_was (((a_class (e♢1) Boundary)
                                 ∧
                                 ((e_acc_f (e♢1) inside) ⩶ (e♢0)))
                                ∧
                                ((guards (a♢1) (a♢0))))
                         ∧
                         (¬ guards (a♢1) (a♢0)))
                          ⇒
                          a_was(∃x∙((a♢0) calls (a♢2) ∎ expose ⟨ empty ⟩)))).
  Proof.
    unfold mdl_sat;
      intros.
    repeat (a_intros; a_prop).
    simpl in *.    

    inversion H5; subst.
    apply sat_was; intros.
    specialize (H11 σ0);
      repeat auto_specialize.
    destruct H11 as [σ' Htmp];
      destruct Htmp as [σ''];
      andDestruct.
    inversion Hb; subst.

    assert (Hwf : σ_wf σ');
      [eauto with loo_db|].

    destruct (was_change_pair_reduction MyModule M')
      with (σ:=(update_σ_map (update_σ_map σ z v) z0 v0))
           (σ':=σ')(A:=¬ guards (a_ z) (a_ z0))(σ'':=σ'')
      as [Hwas|Hwas];
      auto;
      [apply sat_not, nsat_not; auto| |destruct Hwas as [Hwas|Hwas]].

    - destruct Hwas as [σ1 Htmp];
        destruct Htmp as [σ1' Htmp];
        destruct Htmp as [σ2 Htmp];
        destruct Htmp as [σ2' Htmp];
        andDestruct.
      exists σ1, σ1';
        repeat split; eauto with loo_db.
      (*destruct (pair_reduction_change_implies_method_call MyModule M' σ1 σ2)
        as [Hcont|Hcont];
        eauto with loo_db;
        [|destruct Hcont as [Hcont|Hcont]].
      * destruct Hcont as [χ1 Hcont];
          destruct Hcont as [ϕ1 Hcont];
          destruct Hcont as [ψ1 Hcont];
          destruct Hcont as [x' Hcont];
          destruct Hcont as [y' Hcont];
          destruct Hcont as [m Hcont];
          destruct Hcont as [ps Hcont];
          destruct Hcont as [s Hcont];
          andDestruct;
          subst.

        admit.

      * admit.

      * admit.*)
      admit.

    - destruct Hwas as [σ1 Htmp];
        destruct Htmp as [σ1' Htmp];
        andDestruct.
      exists σ1, σ1';
        repeat split; eauto with loo_db.
    
  Abort.

End ExposeExample.
