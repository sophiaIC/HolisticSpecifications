Require Import Arith.
Require Import List.
Require Import common.
Require Import CpdtTactics.

Module LanguageDefinition.

  Inductive addr :=
  | address : nat -> addr.

  Inductive val :=
  | v_addr : addr -> val
  | v_nat : nat -> val
  | v_bool : bool -> val
  | v_null : val.

  Inductive mth :=
  | mth_id : nat -> mth.

  Inductive fld :=
  | f_id : nat -> fld.

  Inductive ghost :=
  | g_id : nat -> ghost.

  Inductive cls :=
  | c_id : nat -> cls.

  Inductive var :=
  | v_id : nat -> var.

  Definition this := v_id 0.
  Definition result := v_id 1.

  Inductive mdl :=
  | mdl_id : nat -> mdl.

  Inductive exp :=
  | e_hole : nat -> exp
  | e_var : var -> exp
  | e_val : val -> exp
  | e_fld : exp -> fld -> exp
  | e_class : exp -> cls -> exp
  | e_ghost : exp -> ghost -> exp -> exp
  | e_if : exp -> exp -> exp -> exp
  | e_eq : exp -> exp -> exp.

  Definition v_true := (v_bool true).
  Definition v_false := (v_bool false).
  Definition e_true := (e_val v_true).
  Definition e_false := (e_val v_false).
  Definition e_null := (e_val v_null).

  Notation "'v_' v" := (e_var v)(at level 38).
  Notation "e ∙ f" := (e_fld e f)(at level 38).
  Notation "'e_' x" := (e_var x)(at level 38).
  Notation "e1 ⩵ e2" := (e_eq e1 e2)(at level 38).

  Inductive stmt :=
  | s_read : var -> var -> fld -> stmt
  | s_write : var -> fld -> var -> stmt
  | s_call : var -> var -> mth -> list var -> stmt
  | s_ret : var -> stmt
  | s_if : exp -> stmt -> stmt -> stmt
  | s_hole : var -> stmt
  | s_new : var -> cls -> stmt.

  Inductive stmts :=
  | s_stmt : stmt -> stmts
  | s_seq : stmt -> stmts -> stmts.

  #[global] Program Instance eqbFld : Eq fld :=
    {
      eqb := fun f1 f2 =>
               match f1, f2 with
               | f_id n1, f_id n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  #[global] Program Instance eqbVar : Eq var :=
    {
      eqb := fun x1 x2 =>
               match x1, x2 with
               | v_id n1, v_id n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply -> Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  #[global] Program Instance eqbMth : Eq mth :=
    {
      eqb := fun m1 m2 =>
               match m1, m2 with
               | mth_id n1, mth_id n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply -> Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  #[global] Program Instance eqbCls : Eq cls :=
    {
      eqb := fun C1 C2 =>
               match C1, C2 with
               | c_id n1, c_id n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply -> Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  #[global] Program Instance eqbMdl : Eq mdl :=
    {
      eqb := fun C1 C2 =>
               match C1, C2 with
               | mdl_id n1, mdl_id n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply -> Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  #[global] Program Instance eqbAddr : Eq addr :=
    {
      eqb := fun a1 a2 =>
               match a1, a2 with
               | address n1, address n2 => n1 =? n2
               end
    }.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      apply -> Nat.eqb_eq in H;
      subst; auto.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      rewrite Nat.eqb_neq;
      crush.
  Defined.
  Next Obligation.
    destruct a1 as [n];
      destruct a2 as [m];
      destruct (Nat.eq_dec n m) as [Heq|Hneq];
      subst;
      auto;
      right;
      crush.
  Defined.

  Inductive ty : Type :=
  | t_cls : cls -> ty
  | t_nat : ty
  | t_bool : ty.

  (**
     Assertions
   **)

  Inductive asrt :=
  | a_exp : exp -> asrt

  | a_and : asrt -> asrt -> asrt
  | a_or : asrt -> asrt -> asrt
  | a_neg : asrt -> asrt
  | a_all : asrt -> asrt
  | a_ex : asrt -> asrt

  | a_intl : exp -> asrt
  | a_extl : exp -> asrt

  | a_prt : exp -> asrt
  | a_prt_frm : exp -> exp -> asrt.

  Notation "'a_' e" := (a_exp e)(at level 38).
  Notation "A1 '∧' A2" := (a_and A1 A2)(at level 39).
  Notation "A1 '∨' A2" := (a_or A1 A2)(at level 39).
  Notation "'¬' A" := (a_neg A)(at level 39).
  Definition arr (A1 A2 : asrt) := ¬ A1 ∨ A2.
  Notation "A1 ⟶ A2" :=(arr A1 A2)(at level 40).
  Definition a_true := (a_ (e_true)).
  Definition a_false := (a_ (e_false)).

  Inductive path :=
  | p_fld : fld -> path
  | p_cons : fld -> path -> path.

  (***
      Core Language Definitions
  ***)

  Record methDef := meth{
                        pre : asrt;
                        post : asrt;
                        params : list (var * ty);
                        body : stmts
                      }.

  Record classDef := clazz{c_name : cls;
                            c_fields : partial_map fld ty;
                            c_meths : partial_map mth methDef}.

  Definition module := partial_map cls classDef.

  Record object := obj{o_cls : cls;
                        o_flds : partial_map fld val}.

  Definition heap := partial_map addr object.

  Record frame := frm{local : partial_map var val;
                       continuation : stmts}.

  Inductive stack :=
    | stack_cons : frame -> list frame -> stack.

  Notation "ϕ ';;' ψ" := (stack_cons ϕ ψ)(at level 41).

  Definition config := (heap * stack) % type.

  Definition interpret_x (σ : config)(x : var) : option val :=
    match σ with
    | (χ, frm lcl c ;; ψ) => lcl x
    end.

  Definition interpret_αf (σ : config)(α : addr)(f : fld) : option val :=
    match σ with
    | (χ, ϕ ;; ψ) =>
        match χ α with
        | Some o => o_flds o f
        | _ => None
        end
    end.

  Definition interpret_f (σ : config)(x : var)(f : fld) : option val :=
    match interpret_x σ x with
    | Some (v_addr α) => interpret_αf σ α f
    | _ => None
    end.

  (*
  Inductive interpret_x : config -> var -> val -> Prop :=
  | interpretation_x : forall χ lcl s x v ψ,
      lcl x = Some v ->
      interpret_x (χ, frm lcl s ;; ψ) x v.

  Inductive interpret_f : config -> var -> fld -> val -> Prop :=
  | interpretation_f : forall χ x f l o v ψ,
      interpret_x (χ, ψ) x (v_addr l) ->
      χ l = Some o ->
      o_flds o f = Some v ->
      interpret_f (χ, ψ) x f v.*)

  Definition classOf (σ : config)(x : var): option cls :=
    match interpret_x σ x with
    | Some (v_addr l) =>
        match fst σ l with
        | Some o => Some (o_cls o)
        | _ => None
        end
    | _ => None
    end.

  Definition typeOf_v (σ : config)(v : val)(t : ty) :=
    match v, t with
    | v_null, _ => True
    | v_nat _, t_nat => True
    | v_bool _, t_bool => True
    | v_addr α, t_cls C => match fst σ α with
                          | Some o => if eqb (o_cls o) C
                                     then True
                                     else False
                          | None => False
                          end
    | _, _ => False
    end.

  Definition typeOf (σ : config)(x : var)(t : ty) :=
    match interpret_x σ x with
    | Some v => typeOf_v σ v t
    | _ => False
    end.

  Fixpoint typeOf_l (σ : config)(lx : list var)(lt : list ty) :=
    match lx, lt with
    | nil, nil => True
    | x :: lx', t :: lt' => typeOf σ x t /\ typeOf_l σ lx' lt'
    | _, _ => False
    end.

End LanguageDefinition.