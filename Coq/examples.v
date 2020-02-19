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

Definition zed := bnd 200.

Definition zed_ := r_var zed.

Definition t := bnd 201.

Definition t_ := r_var t.

Definition f := bnd 202.

Definition f_ := r_var f.

Definition s := bnd 203.

Definition s_ := r_var s.

Definition client := bnd 204.

Definition client_ := r_var client.

Definition isEvenX := bnd 205.

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
                                        zed vZeroLoc
                                        (update
                                           client vClientLoc
                                           (update
                                              this vClientLoc
                                              empty)))))).

Definition myϕ : frame := frm myMap (c_stmt (s_rtrn zed)).

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
  apply int_x with (ψ:=nil)(ϕ:=myϕ);
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
  apply int_x with (ψ:=nil)(ϕ:=myϕ);
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
  apply int_x with (ψ:=nil)(ϕ:=myϕ);
    auto.
Qed.

(*Theorem ArithMdlSatisfiesAccess :
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
  unfold mapp, configMapHeap in H0; simpl in *.
  unfold myχ, update, t_update in H0; simpl in *.
  inversion H0; subst.
  simpl in H1.
  inversion H1.

  (** case 3: client is either not the current object (it is), or t is not in the current continuation*)
  right; intros.
  inversion H; inversion H0; subst; simpl in *.
  inversion H4; inversion H10; subst; simpl in *.
  assert (Heq : z = client \/ z = s \/ z = t \/ z = f \/ z = this).
  unfold myMap, update, t_update in H11.
  destruct (eq_dec z s) as [Heq|Hneqs];
    [auto
    |apply neq_eqb in Hneqs;
     rewrite Hneqs in H11].
  destruct (eq_dec z f) as [Heq|Hneqf];
    [subst; crush
    |apply neq_eqb in Hneqf;
     rewrite Hneqf in H11].
  destruct (eq_dec z t) as [Heq|Hneqt];
    [subst; crush
    |apply neq_eqb in Hneqt;
     rewrite Hneqt in H11].
  destruct (eq_dec z zed) as [Heq|Hneqz];
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
  destruct (eq_dec z client) as [Heq|Hneqcl];
    [subst; crush
    |apply neq_eqb in Hneqcl;
     rewrite Hneqcl in H11].
  destruct (eq_dec z this) as [Heq|Hneqthis];
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
Qed.*)

(*Lemma will_next :
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
  
  destruct (adaptation_exists χ ϕ ψ χ' ϕ' ψ')
    with
      (σ1:=(χ,ϕ::ψ))
      (σ2:=(χ',ϕ'::ψ'))
    as [σ'];
    eauto;
    try solve [inversion Hwf; auto];
    try solve [inversion H1; auto].

  destruct (sat_excluded_middle M1 M2 (χ, ϕ'::ψ') A).

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
Qed.*)

(*Lemma will_arr :
  forall A M1 M2 σ A',
    M1 ⦂ M2 ◎ σ ⊨ A ->
    M1 ⦂ M2 ◎ σ ⊨ (A ⇒ A') ->
    M1 ⦂ M2 ◎ σ ⊨ A'.
Proof.

  

Qed.*)
         
(*           σ ◁ σ2 ≜ σ2' ->
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
                         M1 ⦂ M2 ⦿ σi ⤳⋆ σ2))).*)

(*Lemma will_not :
  forall M1 M2 σ A,
    M1 ⦂ M2 ◎ σ ⊨ a_will(A) ->
    forall A', M1 ⊨m (A ⇒ A') ->
          M1 ⦂ M2 ◎ σ ⊨ a_will(A').
Proof.
  intros
Qed.    
    M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
           forall σ, σ1 ◁ σ1 ≜ σ ->
                M1 ⦂ M2 ◎ σ ⊨ A ->
                M1 ⦂ M2 ◎ σ2' ⊭ A ->
           exists σi σj,
           forall σi' σj', σ ◁ σi ≜ σi' ->
                      σ ◁ σj ≜ σj' ->
                      ((M1 ⦂ M2 ◎ σi' ⊨ A) /\
                       (M1 ⦂ M2 ◎ σj' ⊭ A) /\
                       (M1 ⦂ M2 ⦿ σi ⤳ σj) /\
                       ((σi = σ1) \/
                        (M1 ⦂ M2 ⦿ σ1 ⤳⋆ σi /\
                         M1 ⦂ M2 ⦿ σi ⤳⋆ σ2))).*)

  

(** #<h3># Expose example: #</h3># *)
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

Definition InsideID := classID 6.

Definition Boundary := classID 7.

Definition InsideDef := clazz InsideID
                              nil
                              empty
                              empty.

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

Definition MyModule := (update
                          Boundary BoundaryDef
                          (update
                             InsideID InsideDef
                             empty)).

(** Note: variables introduced by quantifiers in assertions are modelled using *)
(** de Bruijn indeces, thus the name of the relevant variable changes depending *)
(** the quantifier depth of the assertion *)

Lemma fresh_implies_sat :
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                forall σ' A' x v, fresh_x x σ' A' ->
                             σ = (update_σ_map σ' x v) ->
                             A = ([x /s 0]A') ->
                             forall y, fresh_x y σ' A' ->
                                  M1 ⦂ M2 ◎ (update_σ_map σ' y v) ⊨ ([y /s 0]A')) /\
  (forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                forall σ' A' x v, fresh_x x σ' A' ->
                             σ = (update_σ_map σ' x v) ->
                             A = ([x /s 0]A') ->
                             forall y, fresh_x y σ' A' ->
                                  M1 ⦂ M2 ◎ (update_σ_map σ' y v) ⊭ ([y /s 0]A')).
Proof.
Admitted.

Ltac sat_destruct :=
  match goal with
  | [Hand : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply and_iff in Hand;
                                       destruct Hand
  end.

Ltac frsh_auto :=
  match goal with
  | [Hfrsh : fresh_x _ _ (_ ∧ _) |- _] => apply fresh_and_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (_ ⇒ _) |- _] => apply fresh_arr_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (∀x∙ _) |- _] => apply fresh_all_elim in Hfrsh
  | [ |- fresh_x _ _ (_ ∧ _)] => apply fresh_and_intro
  | [ |- fresh_x _ _ (_ ⇒ _)] => apply fresh_arr_intro
  | [ |- fresh_x _ _ (∀x∙_)] => apply fresh_all_intro
  | [ Hfrsh : fresh_x ?x ?σ _ |- fresh_x ?x ?σ _] => auto; try (eapply fresh_notin; eauto)
  end.

Ltac a_intro :=
  match goal with
  | [|- _ ⦂ _ ◎ _ ⊨ (∀x∙ _)] => apply sat_all_x; intros; simpl
  | [|- _ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] => apply arr_prop1; intros; simpl
  end.

Ltac a_intros :=
  repeat a_intro.

Ltac a_prop :=
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> and_iff in H;
                                           destruct H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> or_iff in H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ⇒ _) |- _] => rewrite -> arr_prop in H
         | [H : context[_ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] |- _] => rewrite -> arr_prop in H
         | [H : _ ⦂ _ ◎ _ ⊨ (∀x∙_) |- _] => rewrite all_x_prop in H; simpl in H
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∧ _)] => apply sat_and
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∨ _)] => apply <- or_iff
         end.

Lemma thing :
  entails (∀x∙∀x∙
            ((a_class (e_hole 1) Boundary)
             ∧
             (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
            ∧(∀x∙((a_hole 0) access (a_hole 1) ⇒ (a_eq (e_hole 0) (e_hole 2)))))
          (∀x∙∀x∙
            ((a_class (e_hole 1) Boundary)
             ∧
             (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
            ∧(¬ ∃x∙(((a_hole 0) access (a_hole 1)) ∧ ¬(a_class (e_hole 0) Boundary)))).
Proof.
  auto.
  apply ent;
    intros.
  a_intros.
  repeat (a_prop;
          a_intros;
          auto).

  specialize (H y v H0 z H1). H1).
  
  destruct fresh_intro
    with (σ1:=σ)(σ2:=σ)
         (A1:=(∀x∙ (a_class (e_hole 1) Boundary ∧ a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
              ∧ (∀x∙ ((a_hole 0 access a_hole 1) ⇒ a_eq (e_hole 0) (e_hole 2))))
         (A2:=((∀x∙ (a_class (e_hole 1) Boundary ∧ a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
               ∧ (¬ (∃x∙ ((a_hole 0 access a_hole 1) ∧ (¬ a_class (e_hole 0) Boundary))))))
    as [x Hfrsh];
    andDestruct.
  eapply H with (y:=y)(v:=v) in Ha;
    auto.
  a_prop.
  
  apply H in H1.
  auto.
Qed.

Theorem expose_example :
  MyModule ⊨m (∀x∙∀x∙
                (
                  ((a_class (e_hole 1) Boundary)
                   ∧
                   (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
                  ∧
                  ((∀x∙((a_hole 0) access (a_hole 1) ⇒ (a_eq (e_hole 0) (e_hole 2))))
                   ∧
                   (a_will(∃x∙(((a_hole 0) access (a_hole 1)) ∧ ¬(a_class (e_hole 0) Boundary)))))
                    ⇒
                    ((∃x∙((a_hole 0) call (a_hole 2) ⋄ expose ⟨ empty ⟩)) ∨
                     a_will(∃x∙((a_hole 0) call (a_hole 2) ⋄ expose ⟨ empty ⟩)))
                )
              ).
Proof.
  unfold mdl_sat; intros.
  a_intros.
  a_prop.

  

  inversion H7; subst.
  inversion H16;
    subst;
    simpl in *.
  a_prop.
  inversion H15;
    subst.
  inversion H21;
    subst.
  

  
  Check sat_ex_x.
  a_prop.
  a_prop.
  rewrite arr_prop in H6.
  apply arr_prop2 in H2.
  
  apply sat_all_x.
    intros b αb ob; intros; simpl.
  apply sat_all_x;
    intros i αi oi; intros; simpl.

  destruct (sat_excluded_middle
              MyModule
              M'
              (update_σ_map (update_σ_map σ z0 αb) z1 αi)
              ((a_class (e_var z0) Boundary ∧ a_eq (e_acc_f (e_var z0) inside) (e_var z1))
               ∧ ((∀x∙ ((a_hole 0 access a_bind z1) ⇒ a_eq (e_hole 0) (e_var z0)))
                  ∧ a_will (∃x∙ ((a_hole 0 access a_bind z1) ∧ (¬ a_class (e_hole 0) Boundary))))))
    as [Hsat|];
    [apply sat_arr1; simpl
    |apply sat_arr2; auto].

  repeat sat_destruct.

  assert (Hneg : MyModule ⦂ M' ◎ update_σ_map (update_σ_map σ z0 αb) z1 αi
                          ⊨ (a_will (¬ ∀x∙ ((a_hole 0 access a_bind z1) ⇒ a_eq (e_hole 0) (e_var z0))))).
  inversion H5;
    subst.
  apply sat_will with (ϕ:=ϕ)(ψ:=ψ)(χ:=χ)(σ':=σ')(σ'':=σ'');
    auto.
  inversion H14;
    subst.
  apply sat_not.
  apply nsat_all_x with (y:=y)(z:=z2)(v:=v);
    auto; [|simpl in *].

  repeat frsh_auto; split; auto.
  frsh_auto.
    
  apply ni_aeq;
    auto.
  apply ni_var;
    intro Hcontra;
    subst.
  apply adaptation_preserves_mapping
    with
      (z:=z2)(v:=αb)
    in H10.
  inversion Ha;
    subst.
  unfold mapp, configMapStack in H10.
    rewrite H10 in H1;
    inversion H1.
  unfold mapp, configMapStack, mapp, stackMap; simpl.
  destruct H0 as [ϕ0 Htmp];
    destruct Htmp as [ψ0];
    subst.
  rewrite H0; simpl.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
  destruct (eq_dec z2 z1) as [|Hneq];
    [subst
    |rewrite neq_eqb; auto].
  inversion Ha; subst.
  inversion H2; subst. simpl in *; crush.

  sat_destruct.
  apply nsat_arr; auto.
  apply nsat_eq1 with (v1:=v)(v2:=αb);
    [apply v_var
    |apply v_var
    |].
  inversion H10; subst; simpl.
  unfold mapp, configMapStack, mapp, stackMap; simpl.
  unfold update, t_update;
    rewrite eqb_refl; auto.

  eapply update_fresh_preserves_map;
    eauto.
  eapply adaptation_preserves_mapping;
    eauto.
  eapply update_fresh_preserves_map;
    eauto.
  apply map_update_σ;
    auto.
  intro Hcontra;
    subst.
  inversion H13;
    subst.
  apply nsat_implies_not_sat in H19.
  contradiction H19.
  
  inversion H3;
    subst.
  inversion H17;
    subst.
  erewrite update_fresh_preserves_map with (v:=αb) in H20;
    eauto; [inversion H20; subst|apply map_update_σ; auto].

  destruct (pair_reductions_preserves_addr_classes MyModule M' (χ, ϕ::nil) σ')
    with (α:=α)(o1:=o) as [o' Hclass];
    auto;
    [|andDestruct].

  unfold mapp, configMapStack, configMapHeap in *;
    simpl in *.
  unfold update_σ_map in H8;
    simpl in H8.
  inversion H8;
    subst;
    auto.

  apply sat_class with (α:=α)(o:=o');
    auto;
    [apply v_var, map_update_σ;
     inversion H10;
     subst;
     eexists;
     eexists;
     simpl;
     eauto
    |inversion H10; subst
    |crush].
  unfold mapp, configMapHeap in *; simpl in *;
    auto.
  
  inversion Hneg; subst.
  inversion H9;
    subst;
    [apply sat_or1
    |apply sat_or2].

  (* now *)
  destruct (pair_reduction_implies_method_call MyModule M' (χ, ϕ::nil) σ') as [χ' Ha];
    auto.
  apply limited_config_wf with (ψ:=ψ).
  rewrite <- H8;
    eapply wf_update_σ_map;
    eauto;
    eapply wf_update_σ_map;
    eauto.
  destruct Ha as [ϕ' Ha];
    destruct Ha as [ψ' Ha];
    andDestruct.
  inversion Ha0;
    subst.
  
  destruct Hb as [Hcall|Hret];
    [destruct Hcall as [x Htmp];
     destruct Htmp as [y Htmp];
     destruct Htmp as [m Htmp];
     destruct Htmp as [ps Htmp];
     andDestruct
    |destruct Hret as [x Htmp];
     andDestruct].
  destruct Ha as [C Htmp];
    destruct Htmp as [CDef];
    andDestruct.
  destruct Hb1 as [zs Htmp];
    destruct Htmp as [s Hb1].

  unfold MyModule, update, t_update in Ha1.
  destruct (eq_dec C Boundary) as [|Hneq1];
    [subst;
     rewrite eqb_refl in Ha1;
     inversion Ha1;
     subst;
     simpl in Hb1
    |rewrite neq_eqb in Ha1].
  
  unfold update, t_update in Hb1.
  destruct (eq_dec m expose) as [|Hneqm];
    [subst;
     rewrite eqb_refl in Hb1
    |].

  remember (update_σ_map (update_σ_map σ z0 αb) z1 αi) as σ'''.
  assert (σ_wf σ''');
    [subst|].
  
  edestruct (fresh_x_exists_for_finite_config σ''')  as [x'];
    [|].

  apply sat_ex_x with (z:=).
  
  
  destruct (eq_dec C InsideID) as [|Hneq2];
    [subst;
     rewrite eqb_refl in Ha1;
     inversion Ha1;
     subst;
     simpl in Hb1;
     inversion Hb1
    |rewrite neq_eqb in Ha1;
     inversion Ha1;
     auto].
  
  
  apply sat_ex_x with (z:=).
  
  
  
  (* will *)
  
  
  

  destruct (will_next MyModule M' (χ, ϕ::nil) σ') as [σi Hwill].

  
  
  apply sat_class with (α:=α2)(o:=).


  
  apply sat_class with (α:=α)(o:=o); eauto.
  apply v_var.
  apply map_update_σ; auto.
  inversion H10; subst; simpl; repeat (eexists; eauto).
  
  
  
  

    

  apply and_iff in Hsat;
    destruct Hsat as [Hsat1 Hsat2].
  

  inversion Hsat; subst.
  inversion H10; subst.

  destruct (sat_excluded_middle
              MyModule
              M'
              (update_σ_map (update_σ_map σ z0 b) z1 i)
              (a_next(∃x∙ ((a_hole 0 access a_bind z1) ∧ (¬ a_class (e_hole 0) Boundary))))).

  inversion H4;
    subst.
  inversion H16;
    subst.
  inversion H19;
    subst.
  
  

  apply sat_will.

  assert (will_)

  destruct (will_next MyModule M').

Qed.

Theorem expose_example :
  MyModule ⊨m (∀x∙((a_class (e_hole 0) BoundaryID)
                     
                   ∧

                   (∀x∙((a_eq (e_acc_f (e_hole 1) inside) (e_hole 0))
                          
                        ∧

                        ((∀x∙(((a_hole 0) access (a_hole 1)) ⇒ (a_eq (e_hole 0) (e_hole 2))))
                           
                           ⇒ ((a_will(∃x∙(((a_hole 0) access (a_hole 1)) ∧ (¬ (a_class (e_hole 0) BoundaryID)))))
                                
                                ⇒ (a_will(∃x∙ (a_call (a_hole 0) (a_hole 2) exposeID empty))))
                           
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
                                (a_eq (e_acc_f (e_var z0) inside) (e_var z1)));
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

  
  
Qed.

(*


Theorem expose_example :
  MyModule ⊨m (a_all_x
                 (a_arr
                    (a_class (e_hole 0) BoundaryID)
                    (a_all_x
                       (a_arr
                          (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0))
                          
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
*)