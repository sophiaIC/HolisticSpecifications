Require Import common.
Require Import loo_def.
Require Import function_operations.
Require Import List.

(**
#<h1>#Holistic Reasoning#</h1>#
This is an attempt to separate the reasoning of configurations from the reasoning 
of chainmail assertions. We have two separate goals in designing this separation:

#<ol>#

#<li># Simplifying the construction of chainmail proofs #</li>#
#<li># Specifying a separation of chainmail from the underlying language (the OO language L#<sub>#oo#</sub># in this case) #</li>#

#</ol>#

#<h2>#Coupled vs Decoupled Specification#</h2>#
#<h3>#Coupled Specification#</h3>#

Currently, proofs in Chainmail are constructed in an integrated fashion. That is, proofs are 
constructed by reasoning directly about specific program configurations. Both chainmail proofs 
and chainmail operators themselves are tightly coupled with the definition of the underlying 
language: L#<sub>#oo#</sub>#. The coupling occurs in two ways: 

#<ol>#

#<li># Adaptation (σ1 ◁ σ2 ≜ σ): that is, σ is defined as the adaptation of σ2 with the variable map of σ1. This is necessary for the definition of temporal operators. e.g. will⟨x access y⟩ refers to some future configuration using variables defined in the current configuration. In σ, x and y refer to the same locations in the heap as they do in σ1, but the continuation matches that of σ2 (down to renaming of variables).  #</li>#
#<li># Interpretation (⌊x⌋ σ ≜ v/⌊Σ⌋ σ ≜ V): the interpretation of the variable x (or set of variables Σ) in the configuration σ is defined as v (or V), the mapping of x (or Σ) in the top frame of σ. This is necessary for checking satisfaction of important atomic assertions: viewpoint, space, control, permission. #</li>#

#</ol>#

#<p>#
These two definitions are related. Adaptation is defined in order to preserve the semantic meaning of the interpretation of variables during reduction. i.e. we want to know that if we specify A = will(x access y), then even if, during reduction, the variable map changes, A is satisfied if and only if the object represented by x has access to the object represented by y. We are not concerned with what x and y are named in this future configuration.
#</p>#

#<p>#
The tight coupling of Chainmail to L#<sub>#oo#</sub># that both of these definitions require results in fairly complex proofs that spend much time reasoning about the mechanics of L#<sub>#oo#</sub>#.
#</p>#

#<h3>#Decoupling Chainmail from L#<sub>#oo#</sub></h3>#
#<p>#
Ideally, we would like Chainmail proofs to be done at a higher level. i.e. we would like to be able use the classical properties of Chainmail to derive some results without having to spend effort reasoning about the properties of the semantics of L#<sub>#oo#</sub>#. In cases where we are required to reason about L#<sub>#oo#</sub>#, we would like to delay this to as late as possible.
#</p>#

#<p>#
Below I define a slightly modified version of chainmail that removes the concept of interpretation. In order to do this, I redefine the various atomic assertions to use heap locations rather than variables. Thus, satisfaction of assertions will be defined in terms of the heap and the continuation, and is agnostic to the variable map.
#</p>#
 *)

Inductive a_var : Type :=
| a_hole : nat -> a_var
| a_bind : addr -> a_var.

Inductive expr : Type :=
| ex_var : a_var -> expr
| ex_val : value -> expr
| ex_eq : expr -> expr -> expr
| ex_if : expr -> expr -> expr -> expr
| ex_acc_f : expr -> fld -> expr
| ex_acc_g : expr -> gfld -> expr -> expr.

Notation "'a♢' n" := (a_hole n)(at level 40).
Notation "'e♢' n" := (ex_var (a_hole n))(at level 40).
Notation "'a_' α" := (a_bind α)(at level 40).
Notation "'e_' α" := (ex_var (a_bind α))(at level 39).

(** Assertion syntax  *)

Inductive asrt : Type :=
(** Simple: *)
| a_exp : expr -> asrt
| a_class : a_var -> cls -> asrt
(*| a_set   : a_var -> a_set -> asrt*)

(** Connectives: *)
| a_arr   : asrt -> asrt -> asrt
| a_and   : asrt -> asrt -> asrt
| a_or    : asrt -> asrt -> asrt
| a_neg   : asrt -> asrt

(** Quantifiers: *)
| a_all_x : asrt -> asrt
(*| a_all_Σ : asrt -> asrt*)
| a_ex_x  : asrt -> asrt
(*| a_ex_Σ  : asrt -> asrt*)

(** Permission: *)
| a_acc   : a_var -> a_var -> asrt

(** Control: *)
| a_call  : a_var -> a_var -> mth -> partial_map var a_var  -> asrt

(** Time: *)
| a_next  : asrt -> asrt
| a_will  : asrt -> asrt
| a_prev  : asrt -> asrt
| a_was   : asrt -> asrt

(** Space: *)
(*| a_in    : asrt -> varSet -> asrt*)

(** Viewpoint: *)
| a_extrn : a_var -> asrt
| a_intrn : a_var -> asrt.

Notation "A1 '⇒' A2" := (a_arr A1 A2)(at level 40).
Notation "A1 '∧' A2" :=(a_and A1 A2)(at level 40).
Notation "A1 '∨' A2" :=(a_or A1 A2)(at level 40).
Notation "'¬' A" :=(a_neg A)(at level 40).
Notation "'∀x∙' A" :=(a_all_x A)(at level 40).
(*Notation "'∀S∙' A" :=(a_all_Σ A)(at level 40).*)
Notation "'∃x∙' A" :=(a_ex_x A)(at level 40).
(*Notation "'∃S∙' A" :=(a_ex_Σ A)(at level 40).*)
Notation "x 'internal'" :=(a_intrn x)(at level 40).
Notation "x 'external'" :=(a_extrn x)(at level 40).
Notation "x 'access' y" :=(a_acc x y)(at level 40).
Notation "x 'calls' y '▸' m '⟨' vMap '⟩'" :=(a_call x y m vMap)(at level 40).
Notation "e1 '⩦' e2" := (a_exp (ex_eq e1 e2))(at level 40).

Class Subst (A B C : Type) : Type :=
  {
    sbst : A -> B -> C -> A
  }.

Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

Instance substAVar : Subst a_var nat addr :=
  {
    sbst x n y :=
      match x with
      | a_hole m => if (m =? n)
                   then a_bind y
                   else x
      | _ => x
      end
  }.

Instance substAVarMap : Subst (partial_map var a_var) nat addr :=
  {
    sbst avMap n x := fun y => bind (avMap y) (fun z => Some ([x /s n] z))
    (*                        match avMap y with
                        | Some z => Some ([x /s n] z)
                        | None => None
                        end*)
  }.

Instance substExpr : Subst expr nat addr :=
  {
    sbst :=
      fix sbst' e n v :=
        match e with
        | ex_var x => ex_var ([v /s n] x)
        | ex_eq e1 e2 => ex_eq (sbst' e1 n v) (sbst' e2 n v)
        | ex_if e1 e2 e3 => ex_if (sbst' e1 n v) (sbst' e2 n v) (sbst' e3 n v)
        | ex_acc_f e' f => ex_acc_f (sbst' e' n v) f
        | ex_acc_g e1 g e2 => ex_acc_g (sbst' e1 n v) g (sbst' e2 n v)
        | _ => e
        end
  }.

Instance substAssertionVar : Subst asrt nat addr :=
  {sbst :=
     fix subst' A n x :=
       match A with
       | a_exp e => a_exp ([x /s n] e)
       | a_class y C       => a_class ([x /s n] y) C
       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n x) (subst' A2 n x)
       | a_and A1 A2       => a_and (subst' A1 n x) (subst' A2 n x)
       | a_or A1 A2        => a_or (subst' A1 n x) (subst' A2 n x)
       | a_neg A'          => a_neg (subst' A' n x)
       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' (S n) x)
       | a_ex_x A'       => a_ex_x (subst' A' (S n) x)
       (*permission*)
       | a_acc v1 v2       => a_acc (sbst v1 n x) (sbst v2 n x)
       (*control*)
       | a_call v1 v2 m vMap => a_call ([x /s n] v1)
                                      ([x /s n] v2) m
                                      ([x /s n] vMap)
       (*time*)
       | a_next A'         => a_next (subst' A' n x)
       | a_will A'         => a_will (subst' A' n x)
       | a_prev A'         => a_prev (subst' A' n x)
       | a_was A'          => a_was (subst' A' n x)
       (*space*)
       (*viewpoint*)
       | a_extrn v          => a_extrn ([x /s n] v)
       | a_intrn v          => a_intrn ([x /s n] v)
       end
  }.

(*Instance varSetSubst : Subst varSet nat varSet :=
  {
    sbst :=
      fix subst' Σ1 n Σ2 :=
        match Σ1 with
        | s_hole m => if (m =? n)
                     then Σ2
                     else Σ1
        | _ => Σ1
        end
  }.
        
Instance substAssertionVarSet : Subst asrt nat varSet :=
  {
    sbst :=
      fix subst' A n Σ :=
        match A with
        (*simpl*)
        | a_set e Σ'         => a_set e ([Σ /s n] Σ')

        (*connectives*)
        | a_arr A1 A2       => a_arr (subst' A1 n Σ) (subst' A2 n Σ)
        | a_and A1 A2       => a_and (subst' A1 n Σ) (subst' A2 n Σ)
        | a_or A1 A2        => a_or (subst' A1 n Σ) (subst' A2 n Σ)
        | a_neg A'          => a_neg (subst' A' n Σ)

        (*quantifiers*)      
        | a_all_x A'      => a_all_x (subst' A' n Σ)
        | a_all_Σ A'      => a_all_Σ (subst' A' (S n) Σ)
        | a_ex_x A'       => a_ex_x (subst' A' (n) Σ)
        | a_ex_Σ A'       => a_ex_Σ (subst' A' (S n) Σ)

        (*time*)
        | a_next A'         => a_next (subst' A' n Σ)
        | a_will A'         => a_will (subst' A' n Σ)
        | a_prev A'         => a_prev (subst' A' n Σ)
        | a_was A'          => a_was (subst' A' n Σ)

        (*space*)
        | a_in A' Σ'         => a_in (subst' A' n Σ) ([Σ /s n] Σ')

        | _          => A
        end;
  }.*)

Definition initial (σ : config) : Prop :=
  exists α ϕ, σ = ((update α ObjectInstance empty), ϕ :: nil) /\
         (vMap ϕ) this = Some (v_addr α) /\
         (forall x, x <> this ->
               (vMap ϕ) x = None) /\
         finite_σ σ /\
         not_stuck_σ σ.

Inductive is_exp : expr -> exp -> Prop :=
| is_addr : forall α, is_exp (e_ α) (e_val (v_addr α))
| is_val : forall v, is_exp (ex_val v) (e_val v)
| is_eq : forall e1 e1' e2 e2', is_exp e1 e1' ->
                           is_exp e2 e2' ->
                           is_exp (ex_eq e1 e2) (e_eq e1' e2')
| is_if : forall e1 e2 e3 e1' e2' e3', is_exp e1 e1' ->
                                  is_exp e2 e2' ->
                                  is_exp e3 e3' ->
                                  is_exp (ex_if e1 e2 e3) (e_if e1' e2' e3')
| is_acc_f : forall e e' f, is_exp e e' ->
                       is_exp (ex_acc_f e f) (e_acc_f e' f)
| is_acc_g : forall e1 e1' e2 e2' g, is_exp e1 e1' ->
                                is_exp e2 e2' ->
                                is_exp (ex_acc_g e1 g e2) (e_acc_g e1' g e2').

Hint Constructors is_exp : chainmail_db.

Lemma is_exp_unique :
  forall e e1, is_exp e e1 ->
          forall e2, is_exp e e2 ->
                e1 = e2.
Proof.
  intros e e1 His;
    induction His;
    let e' := fresh "e" in 
    intros e' His';
    inversion His';
    subst;
    eauto with chainmail_db loo_db;
    repeat match goal with
           | [Ha : forall e, is_exp ?e1 e -> ?e1' = e ,
                Hb : is_exp ?e1 ?e' |- _] =>
             specialize (Ha e');
               auto_specialize
           end;
    subst;
    auto with chainmail_db.

Qed.

Hint Resolve is_exp_unique : chainmail_db.

Ltac unique_loo_exp :=
  match goal with
  | [Ha : is_exp ?e ?e1,
          Hb : is_exp ?e ?e2 |- _] =>
    let H := fresh in
    assert (H : e1 = e2);
    [apply (is_exp_unique e e1 Ha e2 Hb)|subst]
  end.

Reserved Notation "M1 '⦂' M2 '◎' σ '⊨′' A"(at level 40).
Reserved Notation "M1 '⦂' M2 '◎' σ '⊭′' A"(at level 40).

Definition value_to_addr : partial_map value a_var :=
  (fun v => match v with
         | v_addr α => Some (a_ α)
         | _ => None
         end).

Inductive sat' : mdl -> mdl -> config -> asrt -> Prop :=
(** Simple: *)
| sat'_exp   : forall M1 M2 M e e' σ, is_exp e e' ->
                                 M1 ⋄ M2 ≜ M ->
                                 M ∙ σ ⊢ e' ↪ v_true ->
                                 M1 ⦂ M2 ◎ σ ⊨′ (a_exp e)

| sat'_class : forall M1 M2 σ α C o, mapp σ α = Some o -> 
                                o.(cname) = C ->
                                M1 ⦂ M2 ◎ σ ⊨′ (a_class (a_ α)  C)

(** Connectives: *)
| sat'_and   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨′ A1 ->
                                M1 ⦂ M2 ◎ σ ⊨′ A2 ->
                                M1 ⦂ M2 ◎ σ ⊨′ (A1 ∧ A2)
                                   
| sat'_or1   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨′ A1 ->
                                M1 ⦂ M2 ◎ σ ⊨′ (A1 ∨ A2)
                                   
| sat'_or2   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨′ A2 ->
                                M1 ⦂ M2 ◎ σ ⊨′ (A1 ∨ A2)

| sat'_arr1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨′ A2 ->
                                M1 ⦂ M2 ◎ σ ⊨′ (A1 ⇒ A2)

| sat'_arr2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭′ A1 ->
                                M1 ⦂ M2 ◎ σ ⊨′ (A1 ⇒ A2)
                                   
| sat'_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭′ A ->
                            M1 ⦂ M2 ◎ σ ⊨′ (¬ A)

(** Quantifiers: *)
| sat'_all_x : forall M1 M2 σ A, (forall y α, mapp σ y = Some (v_addr α) ->
                                    M1 ⦂ M2 ◎ σ ⊨′ ([α /s 0]A)) ->
                            M1 ⦂ M2 ◎ σ ⊨′ (∀x∙ A)

| sat'_ex_x  : forall M1 M2 σ A y α, mapp σ y = Some (v_addr α) ->
                                M1 ⦂ M2 ◎ σ ⊨′ ([α /s 0] A) ->
                                M1 ⦂ M2 ◎ σ ⊨′ (∃x∙ A)
                                   
(** Permission: *)
| sat'_access1 : forall M1 M2 σ x y α, ⌊x⌋ σ ≜ (v_addr α) ->
                                  ⌊y⌋ σ ≜ (v_addr α) ->
                                  M1 ⦂ M2 ◎ σ ⊨′ ((a_ α) access (a_ α))

| sat'_access2 : forall M1 M2 σ x y α α' o f, ⌊x⌋ σ ≜ (v_addr α') ->
                                         mapp σ α' = Some o ->
                                         (flds o) f = Some (v_addr α) ->
                                         ⌊y⌋ σ ≜ (v_addr α) ->
                                         M1 ⦂ M2 ◎ σ ⊨′ ((a_ α') access (a_ α))

| sat'_access3 : forall M1 M2 σ ψ ϕ χ x α1 α2 s, ⌊this⌋ σ ≜ (v_addr α1) ->
                                            ⌊x⌋ σ ≜ (v_addr α2) ->
                                            σ = (χ, ϕ :: ψ) ->
                                            (contn ϕ) = c_stmt s ->
                                            in_stmt x s ->
                                            M1 ⦂ M2 ◎ σ ⊨′ ((a_ α1) access (a_ α2))

(** Control: *)
| sat'_call : forall M1 M2 σ χ ϕ ψ x y m vMap s α1 α2,
    ⌊ this ⌋ σ ≜ (v_addr α1) ->
    ⌊ y ⌋ σ ≜ (v_addr α2) ->
    σ = (χ, ϕ :: ψ) ->
    (contn ϕ) = (c_stmt (s_stmts (s_meth x y m vMap) s)) ->
    M1 ⦂ M2 ◎ σ ⊨′ ((a_ α1) calls (a_ α2) ▸ m ⟨ vMap ∘ (mapp σ) ∘ value_to_addr⟩ )

(** Viewpoint: *)
| sat'_extrn : forall M1 M2 σ α o C, mapp σ α = Some o ->
                                o.(cname) = C ->
                                M1 C = None ->
                                M1 ⦂ M2 ◎ σ ⊨′ a_extrn (a_ α)

| sat'_intrn : forall M1 M2 σ α o C, mapp σ α = Some o ->
                                o.(cname) = C ->
                                (exists CDef, M1 C = Some CDef) ->
                                M1 ⦂ M2 ◎ σ ⊨′ a_intrn (a_ α)

(** Time: *)

| sat'_next : forall M1 M2 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                    M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ' ->
                                    M1 ⦂ M2 ◎ σ' ⊨′ A ->
                                    M1 ⦂ M2 ◎ σ ⊨′ (a_next A)

| sat'_will : forall M1 M2 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                    M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ' ->
                                    M1 ⦂ M2 ◎ σ' ⊨′ A ->
                                    M1 ⦂ M2 ◎ σ ⊨′ (a_will A)

| sat'_prev : forall M1 M2 σ A, (forall σ0 σ', initial σ0 ->
                                     M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                     M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                     M1 ⦂ M2 ◎ σ' ⊨′ A) ->
                           M1 ⦂ M2 ◎ σ ⊨′ (a_prev A)

| sat'_was : forall M1 M2 σ A, (forall σ0, initial σ0 ->
                                 M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                                 exists σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' /\
                                       M1 ⦂ M2 ⦿ σ' ⤳⋆ σ /\
                                       M1 ⦂ M2 ◎ σ' ⊨′ A) ->
                          M1 ⦂ M2 ◎ σ ⊨′ (a_was A)

where "M1 '⦂' M2 '◎' σ '⊨′' A" := (sat' M1 M2 σ A)

with
  nsat' : mdl -> mdl -> config -> asrt -> Prop :=
(*simple*)
| nsat'_exp : forall M1 M2 M σ e e', is_exp e e' ->
                                M1 ⋄ M2 ≜ M ->
                                M ∙ σ ⊢ e' ↪ v_false ->
                                M1 ⦂ M2 ◎ σ ⊭′ (a_exp e)

| nsat'_class1 : forall M1 M2 σ C C' α o, mapp σ α = Some o -> 
                                     o.(cname) = C' ->
                                     C <> C' ->
                                     M1 ⦂ M2 ◎ σ ⊭′ (a_class (a_ α) C)

| nsat'_class2 : forall M1 M2 σ (α : addr) C, mapp σ α = None ->
                                         M1 ⦂ M2 ◎ σ ⊭′ (a_class (a_ α) C)

(*connectives*)
| nsat'_and1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭′ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ (A1 ∧ A2)
                                    
| nsat'_and2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭′ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ (A1 ∧ A2)
                                    
| nsat'_or    : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭′ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ (A1 ∨ A2)

| nsat'_arr   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨′ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊭′ (A1 ⇒ A2)
                                    
| nsat'_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨′ A ->
                             M1 ⦂ M2 ◎ σ ⊭′ (¬ A)

(*quantifiers*)
| nsat'_all_x : forall M1 M2 σ A y α, mapp σ y = Some (v_addr α) ->
                                 M1 ⦂ M2 ◎ σ ⊭′ ([α /s 0]A) ->
                                 M1 ⦂ M2 ◎ σ ⊭′ (∀x∙ A) 

| nsat'_ex_x : forall M1 M2 σ A, (forall y α, mapp σ y = Some (v_addr α) ->
                                    M1 ⦂ M2 ◎ σ ⊭′ ([α /s 0]A)) ->
                            M1 ⦂ M2 ◎ σ ⊭′ (∃x∙ A)

(** Permission: *)
| nsat'_access : forall M1 M2 σ α1 α2 x y, ⌊x⌋ σ ≜ (v_addr α1)  ->
                                      ⌊y⌋ σ ≜ (v_addr α2) ->
                                      α1 <> α2 ->
                                      (forall o f α3, mapp σ α1 = Some o ->
                                                 (flds o) f = Some (v_addr α3) ->
                                                 α2 <> α3) ->
                                      (forall z, ⌊this⌋ σ ≜ (v_addr α1) ->
                                            ⌊z⌋ σ ≜ (v_addr α2) ->
                                            forall ψ ϕ χ s, σ = (χ, ϕ :: ψ) ->
                                                       (contn ϕ) = c_stmt s ->
                                                       ~ in_stmt z s) ->
                                      M1 ⦂ M2 ◎ σ ⊭′ ((a_ α1) access (a_ α2))

(** Control: *)
| nsat'_call1 : forall M1 M2 σ m vMap α1 α2, mapp σ this <> Some (v_addr α1) ->
                                        M1 ⦂ M2 ◎ σ ⊭′ ((a_ α1) calls (a_ α2) ▸ m ⟨ vMap ⟩)

| nsat'_call2 : forall M1 M2 σ ϕ ψ α1 α2 x y m vMap vMap' s, snd σ = ϕ :: ψ ->
                                                        contn ϕ = (c_stmt (s_stmts (s_meth x y m vMap) s)) ->
                                                        mapp σ y <> Some (v_addr α2) ->
                                                        M1 ⦂ M2 ◎ σ ⊭′ ((a_ α1) calls (a_ α2) ▸ m ⟨ vMap' ⟩)

| nsat'_call3 : forall M1 M2 σ ϕ ψ α1 α2 x y m vMap vMap' s, snd σ = ϕ :: ψ ->
                                                        contn ϕ = (c_stmt (s_stmts (s_meth x y m vMap) s)) ->
                                                        vMap' <> vMap ∘ (mapp σ) ∘ value_to_addr ->
                                                        M1 ⦂ M2 ◎ σ ⊭′ ((a_ α1) calls (a_ α2) ▸ m ⟨ vMap' ⟩)

(*viewpoint*) (* well-formeness? This is important!!!!*)
| nsat'_extrn1 : forall M1 M2 σ α, mapp σ α = None ->
                              M1 ⦂ M2 ◎ σ ⊭′ a_extrn (a_ α)

| nsat'_extrn2 : forall M1 M2 σ α o C, mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  (exists CDef, M1 C = Some CDef) ->
                                  M1 ⦂ M2 ◎ σ ⊭′ a_extrn (a_ α)

| nsat'_intrn1 : forall M1 M2 σ α, mapp σ α = None ->
                              M1 ⦂ M2 ◎ σ ⊭′ a_extrn (a_ α)

| nsat'_intrn2 : forall M1 M2 σ α o C, mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  M1 C = None ->
                                  M1 ⦂ M2 ◎ σ ⊭′ a_extrn (a_ α)

(*space*)
(*| nsat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                 M1 ⦂ M2 ◎ σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_in A (s_bind Σ))*)

(*time*)

| nsat'_next : forall M1 M2 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                     (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ') ->
                                     M1 ⦂ M2 ◎ σ' ⊭′ A ->
                                     M1 ⦂ M2 ◎ σ ⊭′ (a_next A)

| nsat'_will : forall M1 M2 σ A ϕ ψ χ, σ = (χ, ϕ :: ψ) ->
                                  (forall σ', (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ') ->
                                         M1 ⦂ M2 ◎ σ' ⊭′ A) ->
                                  M1 ⦂ M2 ◎ σ ⊭′ (a_will A)

| nsat'_prev : forall M1 M2 σ A σ0 σ', initial σ0 ->
                                  M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                  M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                  M1 ⦂ M2 ◎ σ' ⊭′ A ->
                                  M1 ⦂ M2 ◎ σ ⊭′ (a_prev A)

| nsat'_was : forall M1 M2 σ A σ0, initial σ0 ->
                              (forall σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                     M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                                     M1 ⦂ M2 ◎ σ' ⊭′ A) ->
                              M1 ⦂ M2 ◎ σ ⊭′ (a_was A)

where "M1 '⦂' M2 '◎' σ '⊭′' A" := (nsat' M1 M2 σ A).

Scheme sat'_mut_ind := Induction for sat' Sort Prop
  with nsat'_mut_ind := Induction for nsat' Sort Prop.

Combined Scheme sat'_mutind from sat'_mut_ind, nsat'_mut_ind.

Hint Constructors sat' nsat' : chainmail_db.

(**
#<p>#
Above I define a #<i>#more#</i># (but not completely) decoupled version of chainmail.
Assertions are not defined in terms of variables in the variable map, but rather locations
in the heap. Variables in the variable map are used, but only to indicate that the configuration
in question contains a reference to the relevant location in the heap. This is important, because
the heap size in L#<sub>#oo#</sub># increases monotonically, and if a location is defined in
one configuration, then it will be defined in all subsequent configurations.
#</p>#
 *)

(**

#<h2>#Deterministic Reduction#</h2>#
There is the potential for two forms of non-determinism in the temporal operators of Chainmail:

#<ol>#

#<li># 
Multiple potential initial configurations of a L#<sub>#oo#</sub># program allow for 
non-determinism in both the was and prev operators. If there is more than one initial
configuration that might give rise to a specific configuration, then there are more 
than one path that must be considered when determining satisfaction of an assertion 
that features was or next.
#</li>#
#<li># 
The possibility of concurrency means that even given a single specific starting configuration,
multiple future configurations might arise in a non-deterministic manner. This means that 
if reduction of the underlying language is non-deterministic, future configurations are
also non-deterministic. At the moment, the evaluation of L#<sub>#oo#</sub># terms is
deterministic, and so we need not currently consider this case.
#</li>#

#</ol>#

#<p>#
Ignoring for the moment, the second case of non-determinism, the first poses a problem for expressing 
certain properties, especially when nesting temporal operators. We can see this in the 
expression of the expose example that used nested temporal operators. will(was (A)) is an 
almost meaningless assertion because the assertion A has no relation to the current configuration.
The introduction of was means we must consider all starting configurations, not just the current one.
#</p>#

#<p>#
In order to give nested temporal operators (such as will(was(A))) meaning would be to restrict the possible 
starting configurations to one. It would be possible to do this by parameterizing satisfaction on 
the initial configuration, 
i.e.: M1 ⦂ M2 ◎ σ0 … σ ⊨ A
I define this alternate version of satisfaction below.
#</p>#

 *)

Reserved Notation "M1 '⦂' M2 '◎' σ0 '…' σ '⊨' A"(at level 40).
Reserved Notation "M1 '⦂' M2 '◎' σ0 '…' σ '⊭' A"(at level 40).

Inductive sat : mdl -> mdl -> config -> config -> asrt -> Prop :=
(** Simple: *)
(**
Note: #<code>#is_exp e e'#</code># simply maps an #<code>#expr#</code># (defined above) to an expression (#<code>#exp#</code>#) in L#<sub>#oo#</sub>#. #<code>#expr#</code># differs from #<code>#exp#</code># in L#<sub>#oo#</sub># only in that an #<code>#expr#</code># may not contain any variables.
To aid readability, I ignore this distinction between #<code>#e#</code># and #<code>#e'#</code># in the descriptions of #<code>#sat_exp#</code># and #<code>#nsat_exp#</code>#.
 *)
| sat_exp   : forall M1 M2 M σ0 σ e e', is_exp e e' ->
                                   M1 ⋄ M2 ≜ M ->
                                   M ∙ σ ⊢ e' ↪ v_true ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_exp e)
(**
[[[
                     M1 ⋄ M2 ≜ M 
                 M ∙ σ ⊢ e' ↪ v_true
               -----------------------                   (Sat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ e
]]]
 *)

| sat_class : forall M1 M2 σ0 σ α C o, mapp σ α = Some o -> 
                                  o.(cname) = C ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_class (a_ α)  C)
(**
[[[
              (α ↦ o) ∈ σ     o has class C
               ----------------------------                   (Sat-Class)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (α : C)
]]]
 *)

(** Connectives: *)
| sat_and   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)
(**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-And)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)
]]]
 *)

| sat_or1   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
(**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
               ----------------------------                   (Sat-Or1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
 *)

| sat_or2   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
(**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Or2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
 *)

| sat_arr1  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
(**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Arr1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
 *)

| sat_arr2  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
(**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               ----------------------------                   (Sat-Arr2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
 *)

| sat_not   : forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                              M1 ⦂ M2 ◎ σ0 … σ ⊨ (¬ A)
(**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊭ A
               -----------------------                   (Sat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ ¬ A
]]]
 *)

(** Quantifiers: *)
| sat_all_x : forall M1 M2 σ0 σ A, (forall y α, mapp σ y = Some (v_addr α) ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α /s 0]A)) ->
                              M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀x∙ A)
(**
[[[
                (∀ y, (y ↦ α) ∈ σ → M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               -----------------------------------------------------                   (Sat-All-x)
                            M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀ x. A)
]]]
 *)

| sat_ex_x  : forall M1 M2 σ0 σ A y α, mapp σ y = Some (v_addr α) ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α /s 0] A) ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃x∙ A)
(**
[[[
                         (y ↦ α) ∈ σ 
                M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               -------------------------------                   (Sat-Ex-x)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃ x. A)
]]]
 *)

(** Permission: *)
| sat_access1 : forall M1 M2 σ0 σ α, M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α) access (a_ α))
(**
[[[
                
               ------------------------------                   (Sat-Access1)
                M1 ⦂ M2 ◎ σ0 … σ ⊨ α access α
]]]
 *)

| sat_access2 : forall M1 M2 σ0 σ α α' o f, mapp σ α' = Some o ->
                                       (flds o) f = Some (v_addr α) ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α') access (a_ α))
(**
[[[
                 (α' ↦ o) ∈ σ     o.f = α
               ------------------------------                   (Sat-Access2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α' access α
]]]
 *)

| sat_access3 : forall M1 M2 σ0 σ ψ ϕ χ x α1 α2 s, ⌊this⌋ σ ≜ (v_addr α1) ->
                                              ⌊x⌋ σ ≜ (v_addr α2) ->
                                              σ = (χ, ϕ :: ψ) ->
                                              (contn ϕ) = c_stmt s ->
                                              in_stmt x s ->
                                              M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α1) access (a_ α2))
(**
[[[
                     ⌊this⌋ σ ≜ α1
               ⌊x⌋ σ ≜ α2        x ∈ σ.(contn)
               -------------------------------                   (Sat-Access3)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α1 access α2
]]]
 *)

(** Control: *)
| sat_call : forall M1 M2 σ0 σ χ ϕ ψ x y m β s α1 α2,
    ⌊ this ⌋ σ ≜ (v_addr α1) ->
    ⌊ y ⌋ σ ≜ (v_addr α2) ->
    σ = (χ, ϕ :: ψ) ->
    (contn ϕ) = (c_stmt (s_stmts (s_meth x y m β) s)) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α1) calls (a_ α2) ▸ m ⟨ (β ∘ (mapp σ) ∘ value_to_addr) ⟩ )
(**
[[[
                               ⌊this⌋ σ ≜ α1        
               ⌊y⌋ σ ≜ α2        σ.(contn) = (x := y.m(β); s)
               ------------------------------------------------                   (Sat-Call)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α1 calls α2.m(β ∘ σ.(vMap))
]]]
 *)

(** Viewpoint: *)
| sat_extrn : forall M1 M2 σ0 σ α o C, mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  M1 C = None ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ a_extrn (a_ α)
(**
[[[
               (α ↦ o) ∈ χ   o.(className) ∉ M1
               ---------------------------------                   (Sat-Extrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α external
]]]
 *)

| sat_intrn : forall M1 M2 σ0 σ α o C, mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  (exists CDef, M1 C = Some CDef) ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊨ a_intrn (a_ α)
(**
[[[
               (α ↦ o) ∈ χ   o.(className) ∈ M1
               ---------------------------------                   (Sat-Intrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α internal
]]]
 *)

(** Time: *)
(**
Non-determinism in the temporal operators is removed by using the initial
configuration that satisfaction is defined with.
 *)
| sat_next : forall M1 M2 σ0 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                      M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ' ->
                                      M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊨ A ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_next A)
(**
[[[
                 M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ'
               M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊨ A
               ---------------------------------                   (Sat-Next)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ next A
]]]
 *)

| sat_will : forall M1 M2 σ0 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                      M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ' ->
                                      M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊨ A ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_will A)
(**
[[[
                 M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ'
               M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊨ A
               ---------------------------------                   (Sat-Will)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ will A
]]]
 *)

| sat_prev : forall M1 M2 σ0 σ A σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                M1 ⦂ M2 ◎ σ0 … σ' ⊨ A ->
(**
[[[
                    M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'
                    M1 ⦂ M2 ⦿ σ' ⤳ σ
                    M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               ---------------------------------                   (Sat-Prev)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ prev A
]]]
 *)
                                M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_prev A)

| sat_was : forall M1 M2 σ0 σ A σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                               M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                               M1 ⦂ M2 ◎ σ0 … σ' ⊨ A ->
                               M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_was A)
(**
[[[
                    M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'
                    M1 ⦂ M2 ⦿ σ' ⤳⋆ σ
                    M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               --------------------------------                   (Sat-Was)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ was A
]]]
 *)

where "M1 '⦂' M2 '◎' σ0 '…' σ '⊨' A" := (sat M1 M2 σ0 σ A)

with
  nsat : mdl -> mdl -> config -> config -> asrt -> Prop :=
(*simple*)
| nsat_exp : forall M1 M2 M σ0 σ e e', is_exp e e' ->
                                  M1 ⋄ M2 ≜ M ->
                                  M ∙ σ ⊢ e' ↪ v_false ->
                                  M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_exp e)
(**
[[[
                   M1 ⋄ M2 ≜ M
               M ∙ σ ⊢ e ↪ v_false
               --------------------                   (NSat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ e
]]]
 *)

| nsat_class1 : forall M1 M2 σ0 σ C C' α o, mapp σ α = Some o -> 
                                       o.(cname) = C' ->
                                       C <> C' ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_class (a_ α) C)
(**
[[[
                        (α ↦ o) ∈ σ     
               o has class C'      C' ≠ C
               --------------------------                   (NSat-Class1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ (α : C)
]]]
 *)

| nsat_class2 : forall M1 M2 σ0 σ (α : addr) C, mapp σ α = None ->
                                           M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_class (a_ α) C)
(**
[[[
                     ∄o.(α ↦ o) ∈ σ
               --------------------------                   (NSat-Class2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ (α : C)
]]]
 *)

(*connectives*)
| nsat_and1  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∧ A2)
(**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               --------------------------                   (NSat-And1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
 *)

| nsat_and2  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∧ A2)
(**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-And2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
 *)

| nsat_or    : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∨ A2)
(**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Or)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∨ A2
]]]
 *)

| nsat_arr   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ⇒ A2)
(**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Arr)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ⇒ A2
]]]
 *)

| nsat_not   : forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                               M1 ⦂ M2 ◎ σ0 … σ ⊭ (¬ A)
(**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊨ A
               ----------------------                   (NSat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ ¬ A
]]]
 *)

(*quantifiers*)
| nsat_all_x : forall M1 M2 σ0 σ A y α, mapp σ y = Some (v_addr α) ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ ([α /s 0]A) ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (∀x∙ A)
(**
[[[
                      (y ↦ α) ∈ σ
                M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               ----------------------------                   (NSat-All-x)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ ∀ x. A
]]]
 *)

| nsat_ex_x : forall M1 M2 σ0 σ A, (forall y α, mapp σ y = Some (v_addr α) ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ ([α /s 0]A)) ->
                              M1 ⦂ M2 ◎ σ0 … σ ⊭ (∃x∙ A)
(**
[[[
               ∀ y α. (y ↦ α) ∈ σ → M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               -------------------------------------------------                   (NSat-Ex-x)
                         M1 ⦂ M2 ◎ σ0 … σ ⊭ ∃ x. A
]]]
 *)

(** Permission: *)
| nsat_access : forall M1 M2 σ0 σ α1 α2, α1 <> α2 ->
                                    (forall o f α3, mapp σ α1 = Some o ->
                                               (flds o) f = Some (v_addr α3) ->
                                               α2 <> α3) ->
                                    (forall x, ⌊this⌋ σ ≜ (v_addr α1) ->
                                          ⌊x⌋ σ ≜ (v_addr α2) ->
                                          forall ψ ϕ χ s, σ = (χ, ϕ :: ψ) ->
                                                     (contn ϕ) = c_stmt s ->
                                                     ~ in_stmt x s) ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α1) access (a_ α2))
(**
[[[
                α1 ≠ α2        (∀ o f α3. (α1 ↦ o) ∈ σ ∧ o.f = α3 → α2 ≠ α3)
                    (∀ x. ⌊x⌋ σ ≜ α2 ∧ ⌊this⌋ ≜ α1 → x ∉ σ.(contn))
               ---------------------------------------------------------------                   (NSat-Access)
                       M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 access α2
]]]
 *)

(** Control: *)
| nsat_call1 : forall M1 M2 σ0 σ m β α1 α2, mapp σ this <> Some (v_addr α1) ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α1) calls (a_ α2) ▸ m ⟨ β ⟩)
(**
[[[
                    ⌊this⌋ σ ≜ α          α ≠ α1
               ------------------------------------------                   (NSat-Call1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 calls α2 ▸ m ⟨ β ⟩
]]]
 *)

| nsat_call2 : forall M1 M2 σ0 σ ϕ ψ α1 α2 x y m β β' s, snd σ = ϕ :: ψ ->
                                                    contn ϕ = (c_stmt (s_stmts (s_meth x y m β') s)) ->
                                                    mapp σ y <> Some (v_addr α2) ->
                                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α1) calls (a_ α2) ▸ m ⟨ β ⟩)
(**
[[[
                    σ.(contn) = (x := y.m(β'); s) 
                  ⌊y⌋ σ ≜ α                    α ≠ α2
               ------------------------------------------                   (NSat-Call2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 calls α2 ▸ m ⟨ β ⟩
]]]
 *)

| nsat_call3 : forall M1 M2 σ0 σ ϕ ψ α1 α2 x y m β' β s, snd σ = ϕ :: ψ ->
                                                    contn ϕ = (c_stmt (s_stmts (s_meth x y m β') s)) ->
                                                    β <> β' ∘ (mapp σ) ∘ value_to_addr ->
                                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α1) calls (a_ α2) ▸ m ⟨ β ⟩)
(**
[[[
                     σ.(contn) = (x := y.m(β'); s)
                         β ≠ β' ∘ (σ.(vMap))
               ------------------------------------------                   (NSat-Call2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 calls α2 ▸ m ⟨ β ⟩
]]]
 *)

(*viewpoint*) (* well-formeness? This is important!!!!*)
| nsat_extrn1 : forall M1 M2 σ0 σ α, mapp σ α = None ->
                                M1 ⦂ M2 ◎ σ0 … σ ⊭ a_extrn (a_ α)
(**
[[[
                       α ∉ σ.(heap)
               -----------------------------                   (NSat-Extrn1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α external
]]]
 *)

| nsat_extrn2 : forall M1 M2 σ0 σ α o C, mapp σ α = Some o ->
                                    o.(cname) = C ->
                                    (exists CDef, M1 C = Some CDef) ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ a_extrn (a_ α)
(**
[[[
                    (α ↦ o) ∈ σ.(heap)
                    o.(className) ∈ M1
               -----------------------------                   (NSat-Extrn2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α external
]]]
 *)

| nsat_intrn1 : forall M1 M2 σ0 σ α, mapp σ α = None ->
                                M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α) internal)
(**
[[[
                       α ∉ σ.(heap)
               -----------------------------                   (NSat-Intrn1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α internal
]]]
 *)

| nsat_intrn2 : forall M1 M2 σ0 σ α o C, mapp σ α = Some o ->
                                    o.(cname) = C ->
                                    M1 C = None ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ ((a_ α) internal)
(**
[[[
                    (α ↦ o) ∈ σ.(heap)
                    o.(className) ∉ M1
               -----------------------------                   (NSat-Intrn2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α internal
]]]
 *)

(*space*)
(*| nsat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                 M1 ⦂ M2 ◎ σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_in A (s_bind Σ))*)

(*time*)

| nsat_next : forall M1 M2 σ0 σ A ϕ ψ χ σ', σ = (χ, ϕ :: ψ) ->
                                       (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ') ->
                                       M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊭ A ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_next A)
(**
[[[
                    
                  M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ'
                M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊭ A
               ----------------------------------                   (NSat-Next)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ next A
]]]
 *)

| nsat_will : forall M1 M2 σ0 σ A ϕ ψ χ, σ = (χ, ϕ :: ψ) ->
                                    (forall σ', (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ') ->
                                           M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊭ A) ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_will A)
(**
[[[
                    
               (∀ σ'. M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ' →
                      M1 ⦂ M2 ◎ (χ, ϕ :: nil) … σ' ⊭ A)
               -----------------------------------------                   (NSat-Will)
                  M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ will A
]]]
 *)

| nsat_prev : forall M1 M2 σ0 σ A σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                 M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                 M1 ⦂ M2 ◎ σ0 … σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_prev A)
(**
[[[
                    
               M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'       M1 ⦂ M2 ⦿ σ' ⤳ σ
                          M1 ⦂ M2 ◎ σ0 … σ' ⊭ A
               -------------------------------------------                   (NSat-Prev)
                    M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ prev A
]]]
 *)

| nsat_was : forall M1 M2 σ0 σ A, (forall σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                    M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                                    M1 ⦂ M2 ◎ σ0 … σ' ⊭ A) ->
                             M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_was A)
(**
[[[
                    
               (∀ σ'. M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ∧ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ →
                      M1 ⦂ M2 ◎ σ0 … σ' ⊭ A)
               ------------------------------------------------                   (NSat-Was)
                       M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ prev A
]]]
 *)

where "M1 '⦂' M2 '◎' σ0 '…' σ '⊭' A" := (nsat M1 M2 σ0 σ A).

Scheme sat_mut_ind := Induction for sat Sort Prop
  with nsat_mut_ind := Induction for nsat Sort Prop.

Combined Scheme sat_mutind from sat_mut_ind, nsat_mut_ind.

Hint Constructors sat nsat : chainmail_db.

(**
In the above definition, satisfaction of all assertions is deterministic.
The drawback, however, is that we are limited to demonstrating satisfaction with
a single initial configuration. We are able to extend satisfaction to all 
possible initial configurations by including this as part of the definition
of satisfaction for modules.
 *)

Definition mdl_sat (M : mdl)(A : asrt) := forall M' σ0 σ, initial σ0 ->
                                                     M ⦂ M' ⦿ σ0 ⤳⋆ σ ->
                                                     M ⦂ M' ◎ σ0 … σ ⊨ A.

Notation "M '⊨m' A" := (mdl_sat M A)(at level 40).


Definition guards (x y : a_var) : asrt :=
  match x, y with
  | a_ x', a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a_ x', a♢ n => (∀x∙((¬ ((a♢ 0) access (a♢ (S n)))) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a♢ n, a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  | a♢ n, a♢ m => (∀x∙((¬ ((a♢ 0) access (a♢ (S m)))) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  end.


Inductive entails : asrt -> asrt -> Prop :=
| ent : forall A1 A2, (forall σ0 σ M1 M2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                M1 ⦂ M2 ◎ σ0 … σ⊨ A2) ->
                 entails A1 A2.

Hint Constructors entails : chainmail_db.

Definition equiv_a (A1 A2 : asrt): Prop :=
  (entails A1 A2) /\ (entails A2 A1).

(**
#<h3>#Differences with FASE2020#</h3>#
#<p>#
This version of Chainmail is not equivalent to that of the FASE2020 paper due to 
the differences between the temporal operators. The simple example specification below 
illustrates the difference.
#</p>#
#<code>#
(MySpec) ≜ ∀x. will (∃y. x access y)
#</code>#
#<p>#
In the definition of Chainmail as defined in the FASE2020 paper, the x in #<code>#MySpec#</code># 
refers to all 
variables present in the "current" configuration. y on the otherhand refers to not 
only variables present in some future configuration, but also variables present in the 
current configuration. This is due to the definition of adaptation. The adapted 
configuration includes variable maps from both the present configuration and the 
future configuration.
#</p>#
#<p>#
In the version of Chainmail defined in here, this is not the case. x still refers to
any variable present in the current configuration, but y may only refer to variables
present in the future configuration.
#</p>#
#<p>#
Given the FASE2020 definition of will, the above specification should in fact be satisfied 
by all configurations since for all x, (x access x) is satsified. The definition of
adaptation ensures that x occurs in all configurations adapated from the current one.
On the other hand, the version of Chainmail defined here, does not guarantee that MySpec
is always satsified, only in the case that there exists some future configuration that 
contains a variable mapping that has access to x. Since the quantification of x is defined
outside of the will, and x is replaced by the location in the heap, we are still able to
use x within the will operator. i.e. the following specification is always satisfied even
though x may not be defined in any future configuration.
#</p>#
#<code>#
(MySpec′) ≜ ∀x. will (x access x)
#</code>#
*)