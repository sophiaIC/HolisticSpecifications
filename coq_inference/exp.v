Require Export Arith.
Require Import List.

Require Import necessity.CpdtTactics.
Require Import necessity.common.
Require Import necessity.L_def.
Require Import necessity.defs.
Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Class Subst (A B C : Type) : Type :=
  {
    sbst : A -> B -> C -> A
  }.

Declare Scope exp_scope.

Open Scope exp_scope.

Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

#[global] Instance substExpVal : Subst exp nat value :=
  {
  sbst :=
    fix sbst' e n v :=
    match e with
    | e_hole m => if n =? m
                 then e_val v
                 else e
    | e_eq e1 e2     => e_eq (sbst' e1 n v) (sbst' e2 n v)
    | e_lt e1 e2     => e_lt (sbst' e1 n v) (sbst' e2 n v)
    | e_plus e1 e2   => e_plus (sbst' e1 n v) (sbst' e2 n v)
    | e_minus e1 e2  => e_minus (sbst' e1 n v) (sbst' e2 n v)
    | e_mult e1 e2   => e_mult (sbst' e1 n v) (sbst' e2 n v)
    | e_div e1 e2    => e_div (sbst' e1 n v) (sbst' e2 n v)
    | e_if e1 e2 e3  => e_if (sbst' e1 n v) (sbst' e2 n v) (sbst' e3 n v)
    | e_acc_f e' f   =>  e_acc_f (sbst' e' n v) f
    | e_acc_g e1 g e2 => e_acc_g (sbst' e1 n v) g (sbst' e2 n v)
    | e_val _ => e
    | e_var _ => e
    end
  }.

Reserved Notation "M '∙' σ '⊢' e1 '↪' e2" (at level 40).

Open Scope Z_scope.

Inductive evaluate : mdl -> config -> exp -> value -> Prop :=

(** M, σ true ↪ true     (True_Val) *)
(**| v_true     : forall M σ, M ∙ σ ⊢ e_true ↪ v_true*)

(** M, σ false ↪ false     (False_Val) *)
(**| v_false    : forall M σ, M ∙ σ ⊢ e_false ↪ v_false*)

(** M, σ null ↪ null     (Null_Val) *)
(**| v_null     : forall M σ, M ∙ σ ⊢ e_null ↪ v_null*)

(** This rule has been added to replace the original rules for values *)
(** i.e. Var_Value replaces Null_Val, False_Val, and True_Val, and *)
(** further extends the val to include evaluation of addresses *)
(** M, σ v ↪ v     (Var_Value) *)
| v_value     : forall M σ v, M ∙ σ ⊢ e_val v ↪ v

| v_local : forall M χ ϕ ψ x v, local ϕ x = Some v ->
                           M ∙ (χ, ϕ :: ψ) ⊢ e_var (x_ x) ↪ v

| v_this : forall M χ ϕ ψ, M ∙ (χ, ϕ :: ψ) ⊢ e_var (x_this) ↪ (v_addr (this ϕ))

(** M, σ e.f() ↪ α *)
(** σ(α, f) = v*)
(** ---------------- (Field_Heap_Val) *)
(** M, σ ⊢ e.f ↪ v      *)
| v_f_heap   : forall M χ ψ e f α o v, M ∙ (χ, ψ) ⊢ e ↪ (v_addr α) ->
                                  χ α = Some o ->
                                  flds o f = Some v ->
                                  M ∙ (χ, ψ) ⊢ e_acc_f e f ↪ v


(** M, σ e0 ↪ α *)
(** M, σ e ↪ v *)
(** σ(α) = o *)
(** o has class C in M *)
(** G(M, Class(α, σ), f) = f(x) { e' } (note: the x here corresponds with the 0 in the Coq) *)
(** M, σ e ↪ v*)
(** M, σ [v/x]e' ↪ v'*)
(** ------------------------ (Field_Ghost_Val) *)
(** M, σ ⊢ e0.f(e) ↪ v'      *)
| v_f_ghost  : forall M χ ψ e0 e g α o e' v v' C a,
    M ∙ (χ, ψ) ⊢ e0 ↪ (v_addr α) ->
    χ α = Some o ->
    M (cname o) = Some C ->
    C.(c_g_fields) g = Some (a, e') ->
    M ∙ (χ, ψ) ⊢ e ↪ v ->
    M ∙ (χ, ψ) ⊢ ([ v /s O ] [ (v_addr α) /s (S 0)] e') ↪ v' ->
    M ∙ (χ, ψ) ⊢ e_acc_g e0 g e ↪ v'

(** M, σ e ↪ true *)
(** M, σ e1 ↪ v *)
(** -------------------------------- (If_True_Val) *)
(** M, σ ⊢ if e then e1 else e2 ↪ v  *)
| v_if_true  : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ v_true ->
                                M ∙ σ ⊢ e1 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

(** M, σ e ↪ false *)
(** M, σ e2 ↪ v *)
(** -------------------------------- (If_False_Val) *)
(** M, σ ⊢ if e then e1 else e2 ↪ v  *)
| v_if_false : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ v_false -> 
                                M ∙ σ ⊢ e2 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

(** M, σ e1 ↪ v *)
(** M, σ e2 ↪ v *)
(** ------------------------- (Field_Heap_Val) *)
(** M, σ ⊢ e1 = e2 ↪ true *)
| v_equals   : forall M σ e1 e2 v, M ∙ σ ⊢ e1 ↪ v ->
                              M ∙ σ ⊢ e2 ↪ v ->
                              M ∙ σ ⊢ (e_eq e1 e2) ↪ v_true

(** M, σ e1 ↪ v1 *)
(** M, σ e2 ↪ v2 *)
(** v ≠ v' *)
(** ------------------------ (Field_Heap_Val) *)
(** M, σ ⊢ e1 = e2 ↪ false *)
| v_nequals  : forall M σ e1 e2 v1 v2, M ∙ σ ⊢ e1 ↪ v1 ->
                                  M ∙ σ ⊢ e2 ↪ v2 ->
                                  v1 <> v2 ->
                                  M ∙ σ ⊢ (e_eq e1 e2) ↪ v_false

| v_lt : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                            M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                            i1 < i2 ->
                            M ∙ σ ⊢ (e_lt e1 e2) ↪ v_true

| v_nlt : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                             M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                             ~ i1 < i2 ->
                             M ∙ σ ⊢ (e_lt e1 e2) ↪ v_false

| v_plus : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                              M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                              M ∙ σ ⊢ (e_plus e1 e2) ↪ (v_int (i1 + i2))

| v_minus : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                               M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                               M ∙ σ ⊢ (e_minus e1 e2) ↪ (v_int (i1 - i2))

| v_mult : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                              M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                              M ∙ σ ⊢ (e_mult e1 e2) ↪ (v_int (i1 * i2))

| v_div : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                             M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                             M ∙ σ ⊢ (e_div e1 e2) ↪ (v_int (i1 / i2))

where "M '∙' σ '⊢' e1 '↪' e2":= (evaluate M σ e1 e2) : exp_scope.

#[global] Hint Constructors evaluate : exp_db.

Close Scope Z_scope.

Lemma evaluation_unique :
  forall M σ e v, M ∙ σ ⊢ e ↪ v ->
             forall v', M ∙ σ ⊢ e ↪ v' ->
                   v' = v.
Proof.
  intros M σ e v Heval;
    induction Heval;
    intros;
    match goal with
    | [H : _ ∙ _ ⊢ _ ↪ ?v |- ?v = _] =>
      inversion H;
        subst;
        clear H
    end;
    auto;
    try solve [repeat match goal with
                      | [Ha : forall v', ?M ∙ ?σ ⊢ ?e ↪ v' -> _,
                           Hb : ?M ∙ ?σ ⊢ ?e ↪ ?v |- _] =>
                        specialize (Ha v);
                        repeat auto_specialize;
                        repeat simpl_crush;
                        subst
                      end;
               auto;
               crush].
Qed.

Ltac eval_unique_auto :=
  match goal with
  | [Ha : ?M ∙ ?σ ⊢ ?e ↪ ?v,
          Hb : ?M ∙ ?σ ⊢ ?e ↪ ?v' |- _] =>
    assert (v' = v);
    [apply (evaluation_unique M σ e v Ha v' Hb)
    |subst;
     repeat simpl_crush;
     cleanup]
  end.

Close Scope exp_scope.
