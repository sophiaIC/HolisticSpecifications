Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import classical_properties.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** #<h1># Basic Arithmetic Assertions: #</h1># *)

(** #<h3># Class Identifiers: #</h3># *)
Definition Zero := classID 1.

Definition True_ := classID 2.

Definition False_ := classID 3.

Definition String_ := classID 4.

Definition Client := classID 5.

(** #<h3># Field Identifiers:#</h3>#  *)

Definition isEven := fieldID 50.

(** #<h3># Ghost Field Identifiers:#</h3>#  *)

Definition isEvenG := gFieldID 100.

(** #<h3># Addresses:#</h3>#  *)

Definition TrueLoc := address 250.

Definition vTrueLoc := v_addr TrueLoc.

Definition FalseLoc := address 251.

Definition vFalseLoc := v_addr FalseLoc.

Definition ZeroLoc := address 252.

Definition vZeroLoc := v_addr ZeroLoc.

Definition StringLoc := address 253.

Definition vStringLoc := v_addr StringLoc.

Definition ClientLoc := address 254.

Definition vClientLoc := v_addr ClientLoc.

(** #<h3># Variable Identifiers:#</h3>#  *)

Definition z := bind 200.

Definition z_ := r_var z.

Definition t := bind 201.

Definition t_ := r_var t.

Definition f := bind 202.

Definition f_ := r_var f.

Definition s := bind 203.

Definition s_ := r_var s.

Definition client := bind 204.

Definition client_ := r_var client.

Definition isEvenX := bind 205.

(** #<h3># Class Definitions:#</h3># *)

Definition TrueDef := clazz True_ nil empty empty.

Definition FalseDef := clazz False_ nil empty empty.

Definition ZeroDef := clazz Zero
                            (isEven::nil)
                            empty
                            (update
                               isEvenG (isEvenX, (e_acc_f (e_var this) isEven))
                               empty).

Definition StringDef := clazz String_ nil empty empty.

Definition ClientDef := clazz Client nil empty empty.

(** #<h3># Module Definitions:#</h3>#  *)

Definition ArithMdl := (update False_ FalseDef
                               (update True_ TrueDef
                                       (update Zero ZeroDef
                                               empty))).

Definition StringMdl := (update String_ StringDef empty).

Definition ClientMdl := (update Client ClientDef empty).

(** #<h3># Object Definitions:#</h3>#  *)

Definition TrueObj := new True_ empty empty.

Definition FalseObj := new False_ empty empty.

Definition ZeroObj := new Zero (update isEven vTrueLoc empty) empty.

Definition StringObj := new String_ empty empty.

Definition ClientObj := new Client empty empty.

(** #<h3># Configuration Definitions:#</h3>#  *)

Definition myχ : heap := (update
                            StringLoc StringObj
                            (update ZeroLoc ZeroObj
                                    (update FalseLoc FalseObj
                                            (update TrueLoc TrueObj
                                                    (update
                                                       ClientLoc ClientObj
                                                       empty))))).

Definition myMap : state := (update
                               s vStringLoc
                               (update
                                  f vFalseLoc
                                  (update
                                     t vTrueLoc
                                     (update
                                        z vZeroLoc
                                        (update
                                           client vClientLoc
                                           (update
                                              this vClientLoc
                                              empty)))))).

Definition myϕ : frame := frm myMap (c_stmt (s_rtrn z)).

Definition myψ : stack := myϕ :: nil.

Definition myσ : config := (myχ, myψ).

(** ArithMdl ⦂ M ◎ myσ ⊨ true *)
Theorem ArithMdlSatisfiesTrue :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_exp (e_true)).
Proof.
  intros.
  apply sat_exp.
  apply v_value.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ t:True_ *)
Theorem ArithMdlSatisfiesClass :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_class (e_var t) True_).
Proof.
  intros.
  apply sat_class with (α:=TrueLoc)(o:=TrueObj); auto.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ internal⟨t⟩, where t is the variable in σ pointing to TrueObj *)
Theorem ArithMdlSatisfiesInternal :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_intrn (a_bind t)).
Proof.
  intros.
  apply sat_intrn with (α:=TrueLoc)(o:=TrueObj)(C:=True_);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
  exists TrueDef; auto.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ external⟨s⟩, where s is the variable in σ pointing to StringObj *)
Theorem ArithMdlSatisfiesExternal :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_extrn (a_bind s)).
Proof.
  intros.
  apply sat_extrn with (α:=StringLoc)(o:=StringObj)(C:=String_);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
Qed.

(*(** The following is an example of undefined satisfaction: *)
(** external⟨x⟩ can be neither satisfied nor ~satisfied in the case *)
(** that x is not included in the heap. *)
Theorem externalIfNotInternal :
  forall M1 M2 σ x,
    M1 ⦂ M2 ◎ σ ⊭ (a_intrn x) ->
    M1 ⦂ M2 ◎ σ ⊨ (a_extrn x).
Proof.
  intros.
  inversion H; subst.
  apply sat_extrn with (α:=α)(o:=o)(C:=cname o);
    auto.
Abort.*)

Theorem ClientExternalToArithMdl :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_extrn (a_bind client)).
Proof.
  intros.
  apply sat_extrn with (α:=ClientLoc)(o:=ClientObj)(C:=Client);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
Qed.

Theorem ArithMdlSatisfiesAccess :
  forall M, ArithMdl ⦂ M ◎ myσ ⊭ (a_acc (a_bind client) (a_bind t)).
Proof.
  intros.
  apply nsat_access; intros.
  
  (** case 1: client and t do not point to the same object in the heap *)
  inversion H; subst;
    inversion H0; subst;
      simpl in *;
      inversion H4; subst;
        inversion H2; subst;
          intro Hcontra; subst;
            simpl in *;
            rewrite <- H3 in H5;
            unfold myMap, update, t_update in H5; simpl in H5;
              inversion H5.

  (** case 2: client does not have a field that has access to t *)
  inversion H; subst; simpl in *.
  inversion H4; subst; simpl in *.
  inversion H5; subst.
  unfold common.map, configMapHeap in H0; simpl in *.
  unfold myχ, update, t_update in H0; simpl in *.
  inversion H0; subst.
  simpl in H1.
  inversion H1.

  (** case 3: client is either not the current object (it is), or t is not in the current continuation*)
  right; intros.
  inversion H; inversion H0; subst; simpl in *.
  inversion H4; inversion H10; subst; simpl in *.
  assert (Heq : z0 = client \/ z0 = s \/ z0 = t \/ z0 = f \/ z0 = this).
  unfold myMap, update, t_update in H11.
  destruct (eq_dec z0 s) as [Heq|Hneqs];
    [auto
    |apply neq_eqb in Hneqs;
     rewrite Hneqs in H11].
  destruct (eq_dec z0 f) as [Heq|Hneqf];
    [subst; crush
    |apply neq_eqb in Hneqf;
     rewrite Hneqf in H11].
  destruct (eq_dec z0 t) as [Heq|Hneqt];
    [subst; crush
    |apply neq_eqb in Hneqt;
     rewrite Hneqt in H11].
  destruct (eq_dec z0 z) as [Heq|Hneqz];
    [subst
    |apply neq_eqb in Hneqz;
     rewrite Hneqz in H11].
  inversion H; inversion H0; subst.
  unfold myσ, myψ, myϕ in H6, H14;
    simpl in H6, H14;
    inversion H6;
    inversion H14;
    subst;
    simpl in H7, H15;
    unfold myMap in H7, H15;
    simpl in H7, H15.
  unfold update, t_update, t, s in H7; crush.
  destruct (eq_dec z0 client) as [Heq|Hneqcl];
    [subst; crush
    |apply neq_eqb in Hneqcl;
     rewrite Hneqcl in H11].
  destruct (eq_dec z0 this) as [Heq|Hneqthis];
    [subst; crush
    |apply neq_eqb in Hneqthis;
     rewrite Hneqthis in H11].
  unfold empty, t_empty in H11; inversion H11.
  unfold myσ in H1.
  inversion H1; subst.
  unfold myϕ in H2; simpl in H2.
  inversion H2; subst.
  destruct Heq as [|Heq]; subst;
    [intros Hcontra; inversion Hcontra|].
  destruct Heq as [|Heq]; subst;
    [intros Hcontra; inversion Hcontra|].
  destruct Heq as [|Heq]; subst;
    [intros Hcontra; inversion Hcontra|].
  destruct Heq as [|Heq]; subst;
    [intros Hcontra; inversion Hcontra|].
  intros Hcontra; inversion Hcontra.
Qed.

Lemma will_next :
  forall M1 M2 σ1 σ2,
    M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
    forall σ, M1 ⦂ M2 ⦿ σ ⤳⋆ σ1 ->
         σ_wf σ ->
         forall σ1' σ2' A,
           σ ◁ σ1 ≜ σ1' ->
           σ ◁ σ2 ≜ σ2' ->
           M1 ⦂ M2 ◎ σ1' ⊨ A ->
           M1 ⦂ M2 ◎ σ2' ⊭ A ->
           exists σi σj,
           forall σi' σj', σ ◁ σi ≜ σi' ->
                      σ ◁ σj ≜ σj' ->
                      ((M1 ⦂ M2 ◎ σi' ⊨ A) /\
                       (M1 ⦂ M2 ◎ σj' ⊭ A) /\
                       (M1 ⦂ M2 ⦿ σi ⤳ σj) /\
                       ((σi = σ1) \/
                        (M1 ⦂ M2 ⦿ σ1 ⤳⋆ σi /\
                         M1 ⦂ M2 ⦿ σi ⤳⋆ σ2))).
Proof.
  intros M1 M2 σ1 σ2 Hred;
    induction Hred;
    intros.

  exists σ1, σ2;
    intros.
  adapt_rewrite; auto.

  destruct (config_wf_decompose σ0 H1) as [χ Hσ];
    destruct Hσ as [ϕ Hσ];
    destruct Hσ as [ψ Hσ];
    subst.

  assert (Hwf : σ_wf σ);
    [eapply pair_reductions_preserves_config_wf;
     eauto
    |destruct (config_wf_decompose σ Hwf) as [χ' Hσ];
     destruct Hσ as [ϕ' Hσ];
     destruct Hσ as [ψ' Hσ]];
    subst.
  
  destruct (adaptation_exists (χ, ϕ::ψ) (χ', ϕ'::ψ'))
    with
      (χ1:=χ)(ϕ1:=ϕ)(ψ1:=ψ)
      (χ2:=χ')(ϕ2:=ϕ')(ψ2:=ψ')
    as [σ'];
    eauto;
    try solve [inversion Hwf; auto];
    try solve [inversion H1; auto].

  destruct (sat_excluded_middle M1 M2 σ' A).

  destruct (IHHred (χ, ϕ::ψ))
    with (σ1':=σ')(σ2':=σ2')(A:=A)
    as [σi Hres];
    auto;
    [eapply pair_reductions_transitive; eauto|];
    destruct Hres as [σj Hres].
  exists σi, σj;
    intros.
  destruct (Hres σi' σj') as [Ha Hb];
    auto;
    andDestruct.
  split;
    [|split];
    auto.
  destruct Hb as [Hb|Hb];
    subst;
    auto;
    andDestruct;
    split;
    auto.
  right; split; auto.
  eapply pair_reductions_transitive;
    eauto.

  exists σ1, (χ', ϕ'::ψ');
    intros;
    adapt_rewrite;
    auto.
Qed.

(** #<h3># Expose example: #</h3># *)
(** ---------------------------------------------------- *)
(** #<code># >MyModule = { #</code># *)
(** #<code># >  Internal = {} #</code># *)
(** #<code># >  Boundary = { #</code># *)
(** #<code># >    field internal : Internal #</code># *)
(** #<code># >    meth expose() = {return this.internal} #</code># *)
(** #<code># >  } #</code># *)
(** #<code># >} #</code># *)
(** --------------------------------------------------- *)
(** #<code># we want to prove: #</code># *)
(**  *)
(** #<code># >MyModule ⊨  #</code># *)
(** #<code># >(∀ b, b : Boundary, ∀ i, (b.internal = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
(** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
(** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
(**  *)
(**  *)

Definition InternalID := classID 6.

Definition BoundaryID := classID 7.

Definition InternalDef := clazz InternalID
                                nil
                                empty
                                empty.

Definition internal := fieldID 0.

Definition exposeID := methID 0.

Definition x := bind 10.

Definition exposeBody := s_stmts (s_asgn (r_var x) (r_fld this internal))
                                 (s_rtrn x).

Definition BoundaryDef := clazz BoundaryID
                                (internal :: nil)
                                (update
                                   exposeID exposeBody
                                   empty)
                                empty.

Definition MyModule := (update
                          BoundaryID BoundaryDef
                          (update
                             InternalID InternalDef
                             empty)).

(** Note: variables introduced by quantifiers in assertions are modelled using *)
(** de Bruijn indeces, thus the name of the relevant variable changes depending *)
(** the quantifier depth of the assertion *)

Theorem expose_example :
  MyModule ⊨m (a_all_x
                 (a_arr
                    (a_class (e_hole 0) BoundaryID)
                    (a_all_x
                       (a_arr
                          (a_eq (e_acc_f (e_hole 1) internal) (e_hole 0))
                          
                          (a_arr
                             
                             (a_all_x
                                (a_arr
                                   (a_acc (a_hole 0) (a_hole 1))
                                   (a_class (e_hole 0) BoundaryID)
                                )
                                
                             )
                             
                             (a_arr
                                (a_will
                                   (a_ex_x
                                      (a_and
                                         (a_acc (a_hole 0) (a_hole 1))
                                         (a_neg
                                            (a_class (e_hole 0) BoundaryID)
                                         )
                                      )
                                   )
                                )
                                (a_will
                                   (a_ex_x
                                      (a_call (a_hole 0) (a_hole 2) exposeID empty)
                                   )
                                )
                             )
                             
                          )
                       )
                    )
                 )
              ).
Proof.
  unfold mdl_sat; intros.
  apply sat_all_x;
    intros αb b ob; intros; simpl.

  destruct (sat_excluded_middle MyModule M' (update_σ_map σ z0 b) (a_class (e_var z0) BoundaryID));
    [apply sat_arr1
    |apply sat_arr2; auto].

  apply sat_all_x;
    intros αi i oi; intros; simpl.
    
  destruct (sat_excluded_middle MyModule M'
                                (update_σ_map (update_σ_map σ z0 b) z1 i)
                                (a_eq (e_acc_f (e_var z0) internal) (e_var z1)));
    [apply sat_arr1
    |apply sat_arr2; auto].

  destruct (sat_excluded_middle
              MyModule M'
              (update_σ_map (update_σ_map σ z0 b) z1 i)
              (a_all_x (a_arr (a_acc (a_hole 0) (a_bind z1)) (a_class (e_hole 0) BoundaryID))));
    [apply sat_arr1
    |apply sat_arr2; auto].

  destruct (sat_excluded_middle
              MyModule M'
              (update_σ_map (update_σ_map σ z0 b) z1 i)
              (a_will (a_ex_x (a_and (a_acc (a_hole 0) (a_bind z1)) (a_neg (a_class (e_hole 0) BoundaryID))))));
    [apply sat_arr1
    |apply sat_arr2; auto].

  
  
Admitted.