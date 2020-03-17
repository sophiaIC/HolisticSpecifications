Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.
Require Import loo_def.
Require Import function_operations.
Require Import Coq.Logic.FunctionalExtensionality.

(** Assertion Variables *)

Inductive a_var : Type :=
| a_hole : nat -> a_var
| a_bind : var -> a_var.

(** Assertion syntax  *)

Inductive asrt : Type :=
(** Simple: *)
| a_exp   : exp -> asrt
| a_eq    : exp -> exp -> asrt (* is this necessary? isn't it a redundant subcase of a_exp? *)
| a_class : exp -> cls -> asrt
| a_set   : exp -> varSet -> asrt

(** Connectives: *)
| a_arr   : asrt -> asrt -> asrt
| a_and   : asrt -> asrt -> asrt
| a_or    : asrt -> asrt -> asrt
| a_neg   : asrt -> asrt

(** Quantifiers: *)
| a_all_x : asrt -> asrt
| a_all_Σ : asrt -> asrt
| a_ex_x  : asrt -> asrt
| a_ex_Σ  : asrt -> asrt

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
| a_in    : asrt -> varSet -> asrt

(** Viewpoint: *)
| a_extrn : a_var -> asrt
| a_intrn : a_var -> asrt.

Notation "A1 '⇒' A2" := (a_arr A1 A2)(at level 40).
Notation "A1 '∧' A2" :=(a_and A1 A2)(at level 40).
Notation "A1 '∨' A2" :=(a_or A1 A2)(at level 40).
Notation "'¬' A" :=(a_neg A)(at level 40).
Notation "'∀x∙' A" :=(a_all_x A)(at level 40).
Notation "'∀S∙' A" :=(a_all_Σ A)(at level 40).
Notation "'∃x∙' A" :=(a_ex_x A)(at level 40).
Notation "'∃S∙' A" :=(a_ex_Σ A)(at level 40).
Notation "x 'internal'" :=(a_intrn x)(at level 40).
Notation "x 'external'" :=(a_extrn x)(at level 40).
Notation "x 'access' y" :=(a_acc x y)(at level 40).
Notation "x 'calls' y '∎' m '⟨' vMap '⟩'" :=(a_call x y m vMap)(at level 40).


Notation "'a♢' n" := (a_hole n)(at level 40).
Notation "'e♢' n" := (e_hole n)(at level 40).
Notation "'a_' x" := (a_bind x)(at level 40).
Notation "'e_' x" := (e_var x)(at level 40).
Notation "e1 '⩦' e2" := (a_eq e1 e2)(at level 40).

(**
(guards x y) holds if x is the only object that has access to y.
*)

Definition guards (x y : a_var) : asrt :=
  match x, y with
  | a_ x', a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a_ x', a♢ n => (∀x∙((¬ ((a♢ 0) access (a♢ (S n)))) ∨ ((e♢ 0) ⩦ (e_ x'))))
  | a♢ n, a_ y' => (∀x∙((¬ ((a♢ 0) access y)) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  | a♢ n, a♢ m => (∀x∙((¬ ((a♢ 0) access (a♢ (S m)))) ∨ ((e♢ 0) ⩦ (e♢ (S n)))))
  end.


Class Subst (A B C : Type) : Type :=
  {
    sbst : A -> B -> C -> A
  }.

Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

Instance substExp : Subst exp nat var :=
  {
    sbst :=
      fix subst' e n x :=
        match e with
        | e_hole m => if m =? n
                     then e_var x
                     else e
        | e_eq e1 e2 => e_eq (subst' e1 n x) (subst' e2 n x)
        | e_if e1 e2 e3 => e_if (subst' e1 n x) (subst' e2 n x) (subst' e3 n x)
        | e_acc_f e' f => e_acc_f (subst' e' n x) f
        | e_acc_g e1 g e2 => e_acc_g (subst' e1 n x) g (subst' e2 n x)
        | _ => e
        end
  }.

Instance substAVar : Subst a_var nat var :=
  {
    sbst x n y :=
      match x with
      | a_hole m => if (m =? n)
                   then a_bind y
                   else x
      | _ => x
      end
  }.

Instance substAVarMap : Subst (partial_map var a_var) nat var :=
  {
    sbst avMap n x := fun y => bind (avMap y) (fun z => Some ([x /s n] z))
(*                        match avMap y with
                        | Some z => Some ([x /s n] z)
                        | None => None
                        end*)
  }.

Instance substAssertionVar : Subst asrt nat var :=
  {sbst :=
     fix subst' A n x :=
       match A with
       | a_exp e           => a_exp (sbst e n x)
       | a_eq e1 e2        => a_eq (sbst e1 n x)
                                  (sbst e2 n x)
       | a_class e C       => a_class (sbst e n x) C
       | a_set e Σ         => a_set (sbst e  n x) Σ
       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n x) (subst' A2 n x)
       | a_and A1 A2       => a_and (subst' A1 n x) (subst' A2 n x)
       | a_or A1 A2        => a_or (subst' A1 n x) (subst' A2 n x)
       | a_neg A'          => a_neg (subst' A' n x)
       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' (S n) x)
       | a_all_Σ A'      => a_all_Σ (subst' A' n x)
       | a_ex_x A'       => a_ex_x (subst' A' (S n) x)
       | a_ex_Σ A'       => a_ex_Σ (subst' A' n x)
       (*permission*)
       | a_acc v1 v2       => a_acc (sbst v1 n x) (sbst v2 n x)
       (*control*)
       | a_call v1 v2 m avMap => a_call ([x /s n] v1)
                                       ([x /s n] v2) m
                                       ([x /s n] avMap)
       (*time*)
       | a_next A'         => a_next (subst' A' n x)
       | a_will A'         => a_will (subst' A' n x)
       | a_prev A'         => a_prev (subst' A' n x)
       | a_was A'          => a_was (subst' A' n x)
       (*space*)
       | a_in A' Σ         => a_in (subst' A' n x) Σ
       (*viewpoint*)
       | a_extrn v          => a_extrn ([x /s n] v)
       | a_intrn v          => a_intrn ([x /s n] v)
       end
  }.

Instance varSetSubst : Subst varSet nat varSet :=
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
  }.

Inductive  closed_exp : exp -> nat -> Prop :=
| cl_val   : forall v n, closed_exp (e_val v) n
| cl_var   : forall x n, closed_exp (e_var x) n
| cl_hole  : forall m n, n <> m ->
                    closed_exp (e_hole m) n
| cl_eq    : forall e1 e2 n, closed_exp e1 n ->
                        closed_exp e2 n ->
                        closed_exp (e_eq e1 e2) n
| cl_if    : forall e1 e2 e3 n, closed_exp e1 n ->
                           closed_exp e2 n ->
                           closed_exp e3 n ->
                           closed_exp (e_if e1 e2 e3) n
| cl_acc_f : forall e f n, closed_exp e n ->
                      closed_exp (e_acc_f e f) n
| cl_acc_g : forall e f e' n, closed_exp e n ->
                         closed_exp e' n ->
                         closed_exp (e_acc_g e f e') n.

Definition notin_a_var (x : a_var)(y : var) : Prop :=
  match x with
  | a_bind z => z <> y
  | _ => True
  end.

Definition notin_av_map (avMap : partial_map var a_var)(x : var) : Prop :=
  forall y z, avMap y = Some z ->
         notin_a_var z x.

Inductive notin_Ax  : asrt -> var -> Prop :=

(** Simple *)
| ni_exp : forall e x, notin_exp e x ->
                  notin_Ax (a_exp e) x
| ni_aeq : forall e1 e2 x, notin_exp e1 x ->
                      notin_exp e2 x ->
                      notin_Ax (a_eq e1 e2) x
| ni_class : forall e C x, notin_exp e x ->
                      notin_Ax (a_class e C) x
| ni_set   : forall e Σ x, notin_exp e x ->
                      notin_Ax (a_set e Σ) x

(** Connectives *)
| ni_arr   : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_arr A1 A2) x
| ni_and   : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_and A1 A2) x
| ni_or    : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_or A1 A2) x
| ni_neg   : forall A x, notin_Ax A x ->
                    notin_Ax (a_neg A) x

(** Quantifiers *)
| ni_all_x : forall A x, notin_Ax A x ->
                    notin_Ax (a_all_x A) x
| ni_all_Σ : forall A x, notin_Ax A x ->
                    notin_Ax (a_all_Σ A) x
| ni_ex_x  : forall A x, notin_Ax A x ->
                    notin_Ax (a_ex_x A) x
| ni_ex_Σ  : forall A x, notin_Ax A x ->
                    notin_Ax (a_ex_Σ A) x

(** Permission: *)
| ni_acc   : forall x y x', notin_a_var x x' ->
                      notin_a_var y x' ->
                      notin_Ax (a_acc x y) x'

(** Control: *)
| ni_call  : forall x y z avMap m, notin_a_var y x ->
                              notin_a_var z x ->
                              notin_av_map avMap x ->
                              notin_Ax (a_call y z m avMap) x

(** Time: *)
| ni_next  : forall A x, notin_Ax A x ->
                    notin_Ax (a_next A) x
| ni_will  : forall A x, notin_Ax A x ->
                    notin_Ax (a_will A) x
| ni_prev  : forall A x, notin_Ax A x ->
                    notin_Ax (a_prev A) x
| ni_was   : forall A x, notin_Ax A x ->
                    notin_Ax (a_was A) x

(** Space: *)
| ni_in    : forall A Σ x, notin_Ax A x ->
                      notin_Ax (a_in A Σ) x

(** Viewpoint: *)
| ni_extrn : forall x y,  notin_a_var x y ->
                     notin_Ax (a_extrn x) y
| ni_intrn : forall x y, notin_a_var x y ->
                    notin_Ax (a_intrn x) y.

Hint Constructors notin_Ax notin_exp : chainmail_db.

Inductive fresh_x : var -> frame -> asrt -> Prop :=
| frsh : forall x ϕ A, (vMap ϕ) x = None ->
                  notin_Ax A x ->
                  fresh_x x ϕ A.
Hint Constructors fresh_x : chainmail_db.

Definition fresh_x_σ (x : var)(σ : config)(A : asrt) :=
  exists χ ϕ ψ, σ = (χ, ϕ::ψ) /\
           fresh_x x ϕ A.

Inductive notin_AΣ  : asrt -> varSet -> Prop :=

(** Simple *)
| niΣ_exp : forall e Σ, notin_AΣ (a_exp e) Σ
| niΣ_aeq : forall e1 e2 Σ, notin_AΣ (a_eq e1 e2) Σ
| niΣ_class : forall e C Σ, notin_AΣ (a_class e C) Σ
| niΣ_set   : forall e Σ Σ', notin_AΣ (a_set e Σ) Σ'

(** Connectives *)
| niΣ_arr   : forall A1 A2 Σ, notin_AΣ A1 Σ ->
                         notin_AΣ A2 Σ ->
                         notin_AΣ (a_arr A1 A2) Σ
| niΣ_and   : forall A1 A2 Σ, notin_AΣ A1 Σ ->
                         notin_AΣ A2 Σ ->
                         notin_AΣ (a_and A1 A2) Σ
| niΣ_or    : forall A1 A2 Σ, notin_AΣ A1 Σ ->
                         notin_AΣ A2 Σ ->
                         notin_AΣ (a_or A1 A2) Σ
| niΣ_neg   : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_neg A) Σ

(** Quantifiers *)
| niΣ_all_x : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_all_x A) Σ
| niΣ_all_Σ : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_all_Σ A) Σ
| niΣ_ex_x  : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_ex_x A) Σ
| niΣ_ex_Σ  : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_ex_Σ A) Σ

(** Permission: *)
| niΣ_acc   : forall x y Σ, notin_AΣ (a_acc x y) Σ

(** Control: *)
| niΣ_call  : forall y z avMap m Σ, notin_AΣ (a_call y z m avMap) Σ

(** Time: *)
| niΣ_next  : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_next A) Σ
| niΣ_will  : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_will A) Σ
| niΣ_prev  : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_prev A) Σ
| niΣ_was   : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_was A) Σ

(** Space: *)
| niΣ_in    : forall A Σ, notin_AΣ A Σ ->
                     notin_AΣ (a_in A Σ) Σ

(** Viewpoint: *)
| niΣ_extrn : forall x Σ,  notin_AΣ (a_extrn x) Σ
| niΣ_intrn : forall x Σ,  notin_AΣ (a_intrn x) Σ.

Hint Constructors notin_AΣ : chainmail_db.

Inductive fresh_Σ : varSet -> asrt -> Prop :=
| frshΣ : forall x A, notin_AΣ A x ->
                fresh_Σ x A.

Hint Constructors fresh_Σ : chainmail_db.

Fixpoint updates {B C : Type} `{Eq B}
         (bs : list (B * B))
         (map1 : partial_map B C)
         (map2 : partial_map B C) : partial_map B C :=
  match bs with
  | nil => map1
  | (b1, b2)::bs' => fun b => if eqb b b1
                          then map2 b2
                          else (updates bs' map1 map2) b
  end.

Definition fresh_in_map {A : Type} (x : var) (m : partial_map var A) : Prop :=
  m x = None.

Reserved Notation "σ1 '◁' σ2 '≜' σ3" (at level 40).

Inductive adaptation : config -> config -> config -> Prop :=
| a_adapt : forall σ χ ϕ ψ σ' χ' ϕ' ϕ'' c β β' ψ' s f f',
    σ = (χ, ϕ::ψ) ->
    σ' = (χ', ϕ' :: ψ') ->
    ϕ = frm β c ->
    ϕ' = frm β' (c_stmt s) ->
    one_to_one f ->
    onto f β' ->
    inv f f' ->
    disjoint_dom f β ->
    disjoint_dom f β' ->
    (forall z z', f z = Some z' -> ~ in_stmt z s) ->
    ϕ'' = frm ((f ∘ β') ∪ β) (c_stmt (❲f' ↦ s❳)) ->
    σ ◁ σ' ≜ (χ', ϕ'' :: ψ')

where "σ1 '◁' σ2 '≜' σ3" := (adaptation σ1 σ2 σ3).

Reserved Notation "M1 '⦂' M2 '◎' σ '⊨' A"(at level 40).
Reserved Notation "M1 '⦂' M2 '◎' σ '⊭' A"(at level 40).

(*
implication cannot be directly used due to strict positivity requirement of Coq
thus, satisfaction rules are in CNF

Similarly, (¬ A) ≡ (A -> False) which also violates the strict positivity 
requirement of Coq thus we define sat mutually with nsat, the negation of sat

For positivity discussion, see: http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html#lab30
 *)

Definition v_to_av : var -> option a_var := fun x => Some (a_bind x).

Lemma one_to_one_v_to_av :
  one_to_one v_to_av.
Proof.
  unfold one_to_one, v_to_av; intros; crush.
Qed.

Lemma into_v_to_av :
  forall {A : Type}`{Eq A}(m : partial_map A var),
    maps_into m v_to_av.
Proof.
  intros;
    unfold maps_into, v_to_av in *;
    intros;
    eexists;
    eauto.
Qed.

Hint Resolve into_v_to_av : chainmail_db.
Hint Resolve one_to_one_v_to_av : chainmail_db.

Lemma compose_v_to_av_equality :
  forall {A : Type} `{Eq A} (m1 m2 : partial_map A var),
    m1 ∘ v_to_av = m2 ∘ v_to_av ->
    m1 = m2.
Proof.
  intros.
  apply functional_extensionality;
    intros a.

  apply compose_one_to_one_eq in H0; auto; crush.
Qed.

Hint Resolve compose_v_to_av_equality : chainmail_db.

Definition initial (σ : config) : Prop :=
  exists α ϕ, σ = ((update α ObjectInstance empty), ϕ :: nil) /\
         (vMap ϕ) this = Some (v_addr α) /\
         (forall x, x <> this ->
               (vMap ϕ) x = None) /\
         finite_σ σ /\
         not_stuck_σ σ.

Inductive sat : mdl -> mdl -> config -> asrt -> Prop :=
(** Simple: *)
| sat_exp   : forall M1 M2 σ e, M1 ∙ σ ⊢ e ↪ v_true ->
                           M1 ⦂ M2 ◎ σ ⊨ a_exp e

| sat_eq   : forall M1 M2 σ e1 e2 v, M1 ∙ σ ⊢ e1 ↪ v ->
                                M1 ∙ σ ⊢ e2 ↪ v ->
                                M1 ⦂ M2 ◎ σ ⊨ a_eq e1 e2

| sat_class : forall M1 M2 σ e C α o, M1 ∙ σ ⊢ e ↪ (v_addr α) ->
                                 mapp σ α = Some o -> 
                                 o.(cname) = C ->
                                 M1 ⦂ M2 ◎ σ ⊨ (a_class e C)

| sat_set   : forall M1 M2 σ e Σ α As, M1 ∙ σ ⊢ e ↪ α ->
                                  ⌊ Σ ⌋ σ ≜′ As ->
                                  In α As ->
                                  M1 ⦂ M2 ◎ σ ⊨ (a_set e (s_bind Σ))

(** Connectives: *)
| sat_and   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (A1 ∧ A2)
                                  
| sat_or1   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)
                                  
| sat_or2   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)

| sat_arr1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2)

| sat_arr2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ (A1 ⇒ A2)
                                  
| sat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                           M1 ⦂ M2 ◎ σ ⊨ (¬ A)

(** Quantifiers: *)
| sat_all_x : forall M1 M2 σ A, (forall y v, mapp σ y = Some v ->
                                   forall z, fresh_x_σ z σ A ->
                                        M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊨ ([z /s 0]A)) ->
                           M1 ⦂ M2 ◎ σ ⊨ (∀x∙ A)

| sat_ex_x  : forall M1 M2 σ A z y v, mapp σ y = Some v ->
                                 fresh_x_σ z σ A ->
                                 M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊨ ([z /s 0] A) ->
                                 M1 ⦂ M2 ◎ σ ⊨ (∃x∙ A)

| sat_all_Σ : forall M1 M2 σ A, (forall Σ, (forall x, In x Σ ->
                                       exists v, ⌊x⌋ σ ≜ v) ->
                                 (M1 ⦂ M2 ◎ σ ⊨ ([(s_bind Σ) /s 0] A))) ->
                           M1 ⦂ M2 ◎ σ ⊨ (∀S∙ A)

| sat_ex_Σ  : forall M1 M2 σ A Σ, (forall x, In x Σ ->
                                   exists v, ⌊x⌋ σ ≜ v) ->
                             M1 ⦂ M2 ◎ σ ⊨ ([(s_bind Σ) /s 0] A) ->
                             M1 ⦂ M2 ◎ σ ⊨ (∃S∙ A)
                                
(** Permission: *)
| sat_access1 : forall M1 M2 σ x y α, ⌊x⌋ σ ≜ (v_addr α) ->
                                 ⌊y⌋ σ ≜ (v_addr α) ->
                                 M1 ⦂ M2 ◎ σ ⊨ ((a_bind x) access (a_bind y))

| sat_access2 : forall M1 M2 σ x y α α' o f, ⌊x⌋ σ ≜ (v_addr α') ->
                                        mapp σ α' = Some o ->
                                        (flds o) f = Some (v_addr α) ->
                                        ⌊y⌋ σ ≜ (v_addr α) ->
                                        M1 ⦂ M2 ◎ σ ⊨ ((a_bind x) access (a_bind y))

| sat_access3 : forall M1 M2 σ ψ ϕ χ x y z α1 α2 s, ⌊x⌋ σ ≜ (v_addr α1) ->
                                               ⌊this⌋ σ ≜ (v_addr α1) ->
                                               ⌊y⌋ σ ≜ (v_addr α2) ->
                                               ⌊z⌋ σ ≜ (v_addr α2) ->
                                               σ = (χ, ϕ :: ψ) ->
                                               (contn ϕ) = c_stmt s ->
                                               in_stmt z s ->
                                               M1 ⦂ M2 ◎ σ ⊨ ((a_bind x) access (a_bind y))

(** Control: *)
(** Julian: I should probably clean up the interpretation equivalence between parameter maps *)
| sat_call : forall M1 M2 σ χ ϕ ψ x x' y y' m vMap vMap' α s αy,
    ⌊ x ⌋ σ ≜ (v_addr α) ->
    ⌊ this ⌋ σ ≜ (v_addr α) ->
    σ = (χ, ϕ :: ψ) ->
    (contn ϕ) =
    (c_stmt (s_stmts (s_meth x' y' m vMap') s)) ->
    ⌊ y ⌋ σ ≜ (v_addr αy) ->
    ⌊ y'⌋ σ ≜ (v_addr αy) ->
    same_dom vMap vMap' ->
    (forall x' y1 y2, vMap x' = Some y1 ->
                 vMap' x' = Some y2 ->
                 (exists v, ⌊ y1 ⌋ σ ≜ v /\
                       ⌊ y2 ⌋ σ ≜ v)) ->
    M1 ⦂ M2 ◎ σ ⊨ ((a_bind x) calls (a_bind y) ∎ m ⟨ (vMap ∘ v_to_av) ⟩ )

(** Viewpoint: *)
| sat_extrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ (v_addr α) ->
                                 mapp σ α = Some o ->
                                 o.(cname) = C ->
                                 M1 C = None ->
                                 M1 ⦂ M2 ◎ σ ⊨ a_extrn (a_bind x)

| sat_intrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ (v_addr α) ->
                                 mapp σ α = Some o ->
                                 o.(cname) = C ->
                                 (exists CDef, M1 C = Some CDef) ->
                                 M1 ⦂ M2 ◎ σ ⊨ a_intrn (a_bind x)

(** Space: *)
| sat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                M1 ⦂ M2 ◎ σ' ⊨ A ->
                                M1 ⦂ M2 ◎ σ ⊨ (a_in A (s_bind Σ))

(** Time: *)

| sat_next : forall M1 M2 σ A ϕ ψ χ σ' σ'', σ = (χ, ϕ :: ψ) ->
                                       M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ' ->
                                       σ ◁ σ' ≜ σ'' ->
                                       M1 ⦂ M2 ◎ σ'' ⊨ A ->
                                       M1 ⦂ M2 ◎ σ ⊨ (a_next A)

| sat_will : forall M1 M2 σ A ϕ ψ χ σ' σ'', σ = (χ, ϕ :: ψ) ->
                                       M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ' ->
                                       σ ◁ σ' ≜ σ'' ->
                                       M1 ⦂ M2 ◎ σ'' ⊨ A ->
                                       M1 ⦂ M2 ◎ σ ⊨ (a_will A)

| sat_prev : forall M1 M2 σ A, (forall σ0 σ' σ'', initial σ0 ->
                                        M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                        M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                        σ ◁ σ' ≜ σ'' ->
                                        M1 ⦂ M2 ◎ σ'' ⊨ A) ->
                          M1 ⦂ M2 ◎ σ ⊨ (a_prev A)

| sat_was : forall M1 M2 σ A, (forall σ0, initial σ0 ->
                                M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                                exists σ' σ'', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' /\
                                          M1 ⦂ M2 ⦿ σ' ⤳⋆ σ /\
                                          σ ◁ σ' ≜ σ'' /\
                                          M1 ⦂ M2 ◎ σ'' ⊨ A) ->
                         M1 ⦂ M2 ◎ σ ⊨ (a_was A)

where "M1 '⦂' M2 '◎' σ '⊨' A" := (sat M1 M2 σ A)

with
nsat : mdl -> mdl -> config -> asrt -> Prop :=
(*simple*)
| nsat_exp : forall M1 M2 σ e, ~ M1 ∙ σ ⊢ e ↪ v_true ->
                          M1 ⦂ M2 ◎ σ ⊭ (a_exp e)

| nsat_eq1 : forall M1 M2 σ e1 e2 v1 v2, M1 ∙ σ ⊢ e1 ↪ v1 ->
                                    M1 ∙ σ ⊢ e2 ↪ v2 ->
                                    v1 <> v2 ->
                                    M1 ⦂ M2 ◎ σ ⊭ (a_eq e1 e2)

| nsat_eq2 : forall M1 M2 σ e1 e2, (forall v, ~M1 ∙ σ ⊢ e1 ↪ v) ->
                              M1 ⦂ M2 ◎ σ ⊭ (a_eq e1 e2)

| nsat_eq3 : forall M1 M2 σ e1 e2, (forall v, ~M1 ∙ σ ⊢ e2 ↪ v) ->
                              M1 ⦂ M2 ◎ σ ⊭ (a_eq e1 e2)

| nsat_class1 : forall M1 M2 σ e C C' α o, M1 ∙ σ ⊢ e ↪ (v_addr α) ->
                                      mapp σ α = Some o -> 
                                      o.(cname) = C' ->
                                      C <> C' ->
                                      M1 ⦂ M2 ◎ σ ⊭ (a_class e C)

| nsat_class2 : forall M1 M2 σ e C, (forall α, ~ M1 ∙ σ ⊢ e ↪ α) ->
                               M1 ⦂ M2 ◎ σ ⊭ (a_class e C)

| nsat_set1   : forall M1 M2 σ e Σ As, ⌊ Σ ⌋ σ ≜′ As ->
                                  (forall α, M1 ∙ σ ⊢ e ↪ α -> ~ In α As) ->
                                  M1 ⦂ M2 ◎ σ ⊭ (a_set e (s_bind Σ))

| nsat_set2   : forall M1 M2 σ e Σ, (forall α, ~ M1 ∙ σ ⊢ e ↪ α) ->
                               M1 ⦂ M2 ◎ σ ⊭ (a_set e (s_bind Σ))

(*connectives*)
| nsat_and1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ (A1 ∧ A2)
                                   
| nsat_and2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (A1 ∧ A2)
                                   
| nsat_or    : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (A1 ∨ A2)

| nsat_arr   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (A1 ⇒ A2)
                                   
| nsat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                            M1 ⦂ M2 ◎ σ ⊭ (¬ A)

(*quantifiers*)
| nsat_all_x : forall M1 M2 σ A y z v, mapp σ y = Some v ->
                                  fresh_x_σ z σ A ->
                                  M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊭ ([z /s 0]A) ->
                                  M1 ⦂ M2 ◎ σ ⊭ (∀x∙ A) 

| nsat_ex_x : forall M1 M2 σ A, (forall y v z, mapp σ y = Some v ->
                                     fresh_x_σ z σ A ->
                                     M1 ⦂ M2 ◎ (update_σ_map σ z v) ⊭ ([z /s 0]A)) ->
                           M1 ⦂ M2 ◎ σ ⊭ (∃x∙ A)

| nsat_ex_Σ  : forall M1 M2 σ A, (forall Σ, (forall x, In x Σ ->
                                        exists v, ⌊x⌋ σ ≜ v) ->
                                  (M1 ⦂ M2 ◎ σ ⊭ ([(s_bind Σ) /s 0] A))) ->
                            M1 ⦂ M2 ◎ σ ⊭ (∃S∙ A)

| nsat_all_Σ : forall M1 M2 σ A Σ, (forall x, In x Σ ->
                                    exists v, ⌊x⌋ σ ≜ v) ->
                              M1 ⦂ M2 ◎ σ ⊭ ([(s_bind Σ) /s 0] A) ->
                              M1 ⦂ M2 ◎ σ ⊭ (∀S∙ A)

(** Permission: *)
| nsat_access : forall M1 M2 σ x y, (forall α1 α2, ⌊x⌋ σ ≜ (v_addr α1) ->
                                         ⌊y⌋ σ ≜ (v_addr α2) ->
                                         α1 <> α2) ->
                               (forall α1 α2 α3 f o, ⌊x⌋ σ ≜ (v_addr α1) ->
                                                mapp σ α1 = Some o ->
                                                (flds o) f = Some (v_addr α2) ->
                                                ⌊y⌋ σ ≜ (v_addr α3) ->
                                                α2 <> α3) ->
                               ((forall α1 α2, ⌊x⌋ σ ≜ (v_addr α1) ->
                                          ⌊this⌋ σ ≜ (v_addr α2) ->
                                          α1 <> α2) \/
                                (forall z α, ⌊y⌋ σ ≜ (v_addr α) ->
                                        ⌊z⌋ σ ≜ (v_addr α) ->
                                        forall ψ ϕ χ s, σ = (χ, ϕ :: ψ) ->
                                                   (contn ϕ) = c_stmt s ->
                                                   ~ in_stmt z s))->
                               M1 ⦂ M2 ◎ σ ⊭ (a_acc (a_bind x) (a_bind y))

(** Control: *)
| nsat_call1 : forall M1 M2 σ x y m vMap α1 α2, ⌊ x ⌋ σ ≜ α1 ->
                                           ⌊ this ⌋ σ ≜ α2 ->
                                           α1 <> α2 ->
                                           M1 ⦂ M2 ◎ σ ⊭ (a_call (a_bind x)
                                                                 (a_bind y)
                                                                 m
                                                                 vMap)
                                              
| nsat_call2 : forall M1 M2 σ ϕ ψ x y m vMap vMap', snd σ = ϕ :: ψ ->
                                               (forall v u s,
                                                   ((contn ϕ) =
                                                    (c_stmt (s_stmts (s_meth v u m vMap') s))) /\
                                                   (forall v1 v2, ⌊ u ⌋ σ ≜ v1 ->
                                                             ⌊ y ⌋ σ ≜ v2 ->
                                                             v1 <> v2)) ->
                                               M1 ⦂ M2 ◎ σ ⊭ (a_call (a_bind x)
                                                                     (a_bind y)
                                                                     m
                                                                     vMap)
| nsat_call3 : forall M1 M2 σ ϕ ψ x y m vMap vMap', snd σ = ϕ :: ψ ->
                                               (forall v u s,
                                                   ((contn ϕ) =
                                                    (c_stmt (s_stmts (s_meth v u m vMap') s))) /\
                                                   (exists x' v1 v2, vMap x' = Some v1 /\
                                                                vMap' x' = Some v2 /\
                                                                (forall α1 α2, ⌊ v1 ⌋ σ ≜ α1 ->
                                                                          ⌊ v2 ⌋ σ ≜ α2 ->
                                                                          α1 <> α2))) ->
                                               M1 ⦂ M2 ◎ σ ⊭ (a_call (a_bind x)
                                                                     (a_bind y)
                                                                     m
                                                                     (vMap ∘ v_to_av))

(*viewpoint*) (* well-formeness? This is important!!!!*)
| nsat_extrn1 : forall M1 M2 σ x, (forall α, ~ ⌊ x ⌋ σ ≜ (v_addr α)) ->
                             M1 ⦂ M2 ◎ σ ⊭ a_extrn (a_bind x)

| nsat_extrn2 : forall M1 M2 σ x α, ⌊ x ⌋ σ ≜ (v_addr α) ->
                               mapp σ α = None ->
                               M1 ⦂ M2 ◎ σ ⊭ a_extrn (a_bind x)

| nsat_extrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ (v_addr α) ->
                                  mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  (exists CDef, M1 C = Some CDef) ->
                                  M1 ⦂ M2 ◎ σ ⊭ a_extrn (a_bind x)

| nsat_intrn1 : forall M1 M2 σ x, (forall α, ~ ⌊ x ⌋ σ ≜ (v_addr α)) ->
                             M1 ⦂ M2 ◎ σ ⊭ a_intrn (a_bind x)

| nsat_intrn2 : forall M1 M2 σ x α, ⌊ x ⌋ σ ≜ (v_addr α) ->
                               mapp σ α = None ->
                               M1 ⦂ M2 ◎ σ ⊭ a_intrn (a_bind x)

| nsat_intrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ (v_addr α) ->
                                  mapp σ α = Some o ->
                                  o.(cname) = C ->
                                  M1 C = None ->
                                  M1 ⦂ M2 ◎ σ ⊭ a_intrn (a_bind x)

(*space*)
| nsat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                 M1 ⦂ M2 ◎ σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_in A (s_bind Σ))

(*time*)

| nsat_next : forall M1 M2 σ A ϕ ψ χ σ' σ'', σ = (χ, ϕ :: ψ) ->
                                        (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ') ->
                                        (σ ◁ σ' ≜ σ'') ->
                                        M1 ⦂ M2 ◎ σ'' ⊭ A ->
                                        M1 ⦂ M2 ◎ σ ⊭ (a_next A)

| nsat_will : forall M1 M2 σ A ϕ ψ χ, σ = (χ, ϕ :: ψ) ->
                                 (forall σ' σ'', (M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ') ->
                                            (σ ◁ σ' ≜ σ'') ->
                                            M1 ⦂ M2 ◎ σ'' ⊭ A) ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_will A)

| nsat_prev : forall M1 M2 σ A σ0 σ' σ'', initial σ0 ->
                                     M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                     M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                     σ ◁ σ' ≜ σ'' ->
                                     M1 ⦂ M2 ◎ σ'' ⊭ A ->
                                     M1 ⦂ M2 ◎ σ ⊭ (a_prev A)

| nsat_was : forall M1 M2 σ A σ0, initial σ0 ->
                             (forall σ' σ'', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                        M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                                        σ ◁ σ' ≜ σ'' ->
                                        M1 ⦂ M2 ◎ σ'' ⊭ A) ->
                             M1 ⦂ M2 ◎ σ ⊭ (a_was A)

where "M1 '⦂' M2 '◎' σ '⊭' A" := (nsat M1 M2 σ A).

Scheme sat_mut_ind := Induction for sat Sort Prop
  with nsat_mut_ind := Induction for nsat Sort Prop.

Combined Scheme sat_mutind from sat_mut_ind, nsat_mut_ind.

Hint Constructors sat nsat : chainmail_db.

Inductive arising : mdl -> mdl -> config -> Prop :=
| arise : forall M1 M2 σ σ0, initial σ0 ->
                        M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                        arising M1 M2 σ.

Definition mdl_sat (M : mdl)(A : asrt) := forall M' σ, arising M M' σ ->
                                                  (exists ϕ ψ, snd σ = ϕ :: ψ) ->
                                                  M ⦂ M' ◎ σ ⊨ A.
  

Notation "M '⊨m' A" := (mdl_sat M A)(at level 40).

Inductive valid_avar : config -> a_var -> Prop :=
| valid_hole : forall σ n, valid_avar σ (a_hole n)
| valid_bind : forall σ x α, mapp σ x = Some α ->
                        valid_avar σ (a_bind x).

Hint Constructors valid_avar : chainmail_db.



Inductive entails : asrt -> asrt -> Prop :=
| ent : forall A1 A2, (forall χ ϕ ψ M1 M2, M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A1 ->
                                 M1 ⦂ M2 ◎ (χ, ϕ::ψ) ⊨ A2) ->
                 entails A1 A2.

Definition equiv_a (A1 A2 : asrt): Prop :=
  (entails A1 A2) /\ (entails A2 A1).
