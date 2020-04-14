Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupling.
Require Import decoupled_classical_properties.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive has_access_to : config -> addr -> addr -> Prop :=
| acc_eq  : forall σ α, has_access_to σ α α
| acc_fld : forall σ α1 o f α2, mapp σ α1 = Some o ->
                           flds o f = Some (v_addr α2) ->
                           has_access_to σ α1 α2
| acc_contn : forall χ ϕ ψ α1 x α2 s, ⌊ this ⌋ (χ, ϕ::ψ) ≜ (v_addr α1) ->
                                 ⌊ x ⌋ (χ, ϕ::ψ) ≜ v_addr α2 ->
                                 contn ϕ = c_stmt s ->
                                 in_stmt x s ->
                                 has_access_to (χ, ϕ::ψ) α1 α2.

Hint Constructors has_access_to : chainmail_db.

Ltac acc_auto :=
  match goal with
  | [ |- has_access_to _ ?α ?α] =>
    apply acc_eq
  | [ H : ~ has_access_to _ ?α ?α |- _] =>
    contradiction H; acc_auto
  | [ Hmap : mapp ?σ ?α1 = Some ?o,
      Hfld : flds ?o ?f = Some (v_addr ?α2) |- has_access_to ?σ ?α1 ?α2] =>
    eapply acc_fld; eauto
  | [ Hmap : ?χ ?α1 = Some ?o,
      Hfld : flds ?o ?f = Some (v_addr ?α2) |- has_access_to (?χ, _) ?α1 ?α2] =>
    eapply acc_fld; eauto
  | [ Hthis : ⌊ this ⌋ (?χ, ?ϕ::?ψ) ≜ (v_addr ?α1),
      Hint : ⌊ ?x ⌋ (?χ, ?ϕ::?ψ) ≜ (v_addr ?α2),
      Hcontn : contn ?ϕ = c_stmt ?s,
      Hin : in_stmt ?x ?s |- has_access_to ?σ ?α1 ?α2] =>
    eapply acc_contn; eauto
  end.

Lemma meth_call :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall χ ϕ1 ψ1, σ1 = (χ, ϕ1::ψ1) ->
                        forall x y m β s, contn ϕ1 = c_stmt (s_stmts (s_meth x y m β) s) ->
                                     forall α1 α2, ~ has_access_to σ1 α1 α2 ->
                                              has_access_to σ2 α1 α2 ->
                                              ⌊ y ⌋ σ1 ≜ (v_addr α1) /\
                                              (exists p, (β ∘ (mapp σ1)) p = Some (v_addr α2)) /\
                                              (forall α, ⌊ this ⌋ σ1 ≜ (v_addr α) ->
                                                    (has_access_to σ1 α α2)).
Proof.
  intros M σ1 σ2 Hred;
    inversion Hred; intros; subst;
      simpl_crush;
      match goal with
      | [Ha : contn ?ϕ = _,
              Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb; inversion Hb; subst
      end.

  match goal with
  | [H : has_access_to _ _ _ |- _] =>
    inversion H; subst
  end;
    try acc_auto.
    - repeat map_rewrite; simpl in *.
      match goal with
      | [H : ~ has_access_to _ _ _ |- _] =>
        contradiction H
      end.
      acc_auto.
    - repeat split; intros; simpl in *.
      + repeat map_rewrite; simpl in *.
        match goal with
        | [H : c_stmt ?s1 = c_stmt ?s2 |- _] =>
          inversion H; subst
        end.
        destruct (eq_dec α α1); subst; auto.
        inversion H9; simpl in *; subst.
        simpl_crush; simpl in *; crush.

      + inversion H10; subst; simpl in *; simpl_crush; simpl in *.
        destruct (eq_dec x this); subst;
          [interpretation_rewrite;
           crush|].
        unfold update, t_update in H7;
          eq_auto;
          eauto.

      + assert (Hex : exists p, (β ∘ (mapp (χ0, ϕ1::ψ1))) p = Some (v_addr α2)).
        * inversion H10; subst; simpl in *; simpl_crush; simpl in *.
          destruct (eq_dec x this); subst;
            [interpretation_rewrite;
             crush|].
          unfold update, t_update in H8;
            eq_auto;
            eauto.
        * let H := fresh in
          destruct Hex as [p H];
            simpl in H;
            let x' := fresh "x" in
            destruct (partial_map_dec p β) as [Hsome|Hnone];
              [destruct Hsome as [x' Htmp]; rewrite Htmp in *
              |rewrite Hnone in H; inversion H];
              unfold mapp in H;
              repeat map_rewrite; simpl in *;
                apply acc_contn with (x:=x')(s:=(s_stmts (s_meth x0 y0 m0 β) s0));
                auto.
          eapply int_x; simpl; eauto.
          apply in_stmts_1.
          apply in_meth_3.
          eauto.
Qed.

Ltac interpretation_auto :=
  match goal with
  | [|- ⌊ ?x ⌋ (?χ,?ϕ::?ψ) ≜ ?v] =>
    match goal with
    | [|- ⌊ x ⌋ (χ,ϕ::nil) ≜ v] => fail 1
    | _ => idtac
    end;
    rewrite interpretation_x_cons; eauto
  | [H : ⌊ ?x ⌋ (?χ,?ϕ::?ψ) ≜ ?v |- _] =>
    notHyp (⌊ x ⌋ (χ,ϕ::nil) ≜ v);
    rewrite interpretation_x_cons in H; eauto
  end.

Lemma classOf_cons :
  forall x χ ϕ ψ C, classOf x (χ, ϕ::ψ) C <->
               classOf x (χ, ϕ::nil) C.
Proof.
  intros x χ ϕ ψ C; split;
    intros Hclass;
    inversion Hclass;
    subst;
    eapply cls_of; eauto;
      interpretation_auto.
Qed.

Ltac classOf_auto :=
  match goal with
  | [|- classOf ?x (?χ, ?ϕ::?ψ) ?C] =>
    match goal with
    | [|- classOf x (χ,ϕ::nil) C] => fail 1
    | _ => idtac
    end;
    rewrite classOf_cons; eauto
  | [H : classOf ?x (?χ,?ϕ::?ψ) ?C |- _] =>
    notHyp (classOf x (χ,ϕ::nil) C);
    rewrite classOf_cons in H; eauto
  end.
               

Lemma stack_append_reduction_equiv :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall ψ, M ∙ (σ1 ◁ ψ) ⤳ (σ2 ◁ ψ).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst;
    unfold stack_append;
    simpl.

  - eapply r_mth; eauto.
    eapply interpretation_x_append in H2; eauto.

  - eapply r_vAssgn with (C:=C); eauto;
      repeat classOf_auto;
      repeat interpretation_auto.

  - eapply r_fAssgn; eauto;
      repeat interpretation_auto;
      repeat classOf_auto.

  - eapply r_new; eauto.

  - eapply r_ret1; eauto.
    repeat interpretation_auto.

  - eapply r_ret2; eauto.
    repeat interpretation_auto.
Qed.

Hint Resolve stack_append_reduction_equiv : loo_db.
Hint Rewrite stack_append_reduction_equiv : loo_db.

Lemma stack_append_reductions_equiv :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             forall ψ, reductions M (σ1 ◁ ψ) (σ2 ◁ ψ).
Proof.
  intros M σ1 σ2 Hred ψ;
    induction Hred;
    eauto with loo_db.
Qed.

Hint Resolve stack_append_reduction_equiv : loo_db.
Hint Rewrite stack_append_reduction_equiv : loo_db.
Print reduction.
Lemma return_from_method_block_1 :
  forall M σ1 σ2, reductions M σ1 σ2 ->
             σ_wf σ1 ->
             forall σ3, M ∙ σ2 ⤳ σ3 ->
                   forall χ1 ϕ1 χ2 ϕ2 ψ2 x,
                     σ1 = (χ1, ϕ1::nil) ->
                     σ2 = (χ2, ϕ2::ψ2) ->
                     contn ϕ2 = (c_stmt (s_rtrn x)) ->
                     (exists χ3 ϕ3 y z m β s α2 α3 v,
                         σ3 = (χ3, ϕ3::nil) /\
                         contn ϕ1 = c_stmt (s_stmts (s_meth y z m β) s) /\
                         contn ϕ3 = c_stmt s /\
                         ⌊ this ⌋ σ1 ≜ (v_addr α3) /\
                         ⌊ this ⌋ σ3 ≜ (v_addr α3) /\
                         ⌊ z ⌋ σ1 ≜ (v_addr α2) /\
                         ⌊ this ⌋ σ2 ≜ (v_addr α2) /\
                         vMap ϕ2 x = Some v /\
                         vMap ϕ3 = (update y v (vMap ϕ1))) \/
                     (exists χ' ϕ' ψ' χ3 ϕ3 y z m β s α2 α3 v,
                         reductions M σ1 (χ', ϕ'::ψ') /\
                         σ3 = (χ3, ϕ3::ψ') /\
                         contn ϕ' = c_stmt (s_stmts (s_meth y z m β) s) /\
                         contn ϕ3 = c_stmt s /\
                         ⌊ this ⌋ (χ', ϕ'::ψ') ≜ (v_addr α3) /\
                         ⌊ this ⌋ σ3 ≜ (v_addr α3) /\
                         ⌊ z ⌋ (χ', ϕ'::ψ') ≜ (v_addr α2) /\
                         ⌊ this ⌋ σ2 ≜ (v_addr α2) /\
                         vMap ϕ2 x = Some v /\
                         vMap ϕ3 = (update y v (vMap ϕ'))).
Proof.
  intros M σ1 σ2 Hred;
    induction Hred;
    intros;
    subst.

  - match goal with
    | [H : ?M ∙ (_, ?ϕ2::_) ⤳ ?σ3,
           Hcontn : contn ?ϕ2 = c_stmt (s_rtrn _) |- _] =>
      inversion H; subst
    end;
      repeat simpl_crush;
      match goal with
      | [ Ha : contn ?ϕ = _,
               Hb : contn ?ϕ = _ |- _] =>
        rewrite Ha in Hb; inversion Hb; subst
      end.
    left.
    inversion H; subst;
      repeat simpl_crush.
    crush;
      simpl in *.
    remember ({| vMap := vMap ϕ0; contn := c_hole y s |}) as ϕ'.
    exists χ, (update_ϕ_contn (update_ϕ_map ϕ' y α) (c_stmt s)), y, y0, m, ps, s, α0.
    admit.

  - admit.
    
Admitted.
  

Lemma reduce_access_change :
  forall M σ1 σ2, M ∙ σ1 ⤳ σ2 ->
             forall α1 α2, ~ has_access_to σ1 α1 α2 ->
                      has_access_to σ2 α1 α2 ->
                      
                                    

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

  Theorem expose_example_will :
    MyModule ⊨m (∀x∙∀x∙(((a_class (a♢1) Boundary)
                         ∧
                         ((ex_acc_f (e♢1) inside) ⩦ (e♢0))
                         ∧
                         ((guards (a♢1) (a♢0))))
                        ∧
                        (a_will (¬ guards (a♢1) (a♢0)))
                          ⇒
                          (a_will (∃x∙((a♢0) calls (a♢2) ▸ expose ⟨ empty ⟩)) ∨
                           (∃x∙ ((a♢0) calls (a♢2) ▸ expose ⟨ empty ⟩))))).
  Proof.
    unfold mdl_sat;
      intros.
    repeat (a_intros; simpl).
    a_prop.
    inversion H4; subst.
    eapply entails_implies in H14;
      [|apply not_all_x_ex_not_1].
    inversion H14; subst; simpl in *.
    eapply entails_implies in H15;
      [|apply neg_distributive_or_1].
    a_prop.
    apply negate_elim_sat in H7.
    
    Search a_neg.
    
    apply sat_all_x; intros; simpl.
    apply sat_all_x; intros; simpl.
    apply sat_arr1.
    
    
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

  Admitted.

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
                                 ((e_acc_f (e♢1) inside) ⩦ (e♢0)))
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
      destruct (pair_reduction_change_implies_method_call MyModule M' σ1 σ2)
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

      * admit.

    - destruct Hwas as [σ1 Htmp];
        destruct Htmp as [σ1' Htmp];
        andDestruct.
      exists σ1, σ1';
        repeat split; eauto with loo_db.
    
  Abort.

End ExposeExample.
