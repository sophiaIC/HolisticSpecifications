Require Import Arith.
Require Import Bool.
Require Export ZArith.ZArith.
Require Import List.
Require Import common.
Require Import CpdtTactics.

Module LanguageDefinition.

  Import ZArith.ZArith.

  Inductive addr :=
  | address : nat -> addr.

  Inductive val :=
  | v_addr : addr -> val
  | v_int : Z -> val
  | v_bool : bool -> val
  | v_str : String.string -> val
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
  | v_spec : nat -> var
  | v_prog : nat -> var.

  Definition this := v_prog 0.
  Definition result := v_prog 1.

  Inductive mdl :=
  | mdl_id : nat -> mdl.

  Inductive ty : Type :=
  | t_cls : cls -> ty
  | t_int : ty
  | t_bool : ty
  | t_str : ty
  | t_ext : ty.

  Inductive exp :=
  | e_hole : nat -> exp
  | e_var : var -> exp
  | e_val : val -> exp
  | e_fld : exp -> fld -> exp
  | e_typ : exp -> ty -> exp
  | e_ghost : exp -> ghost -> exp -> exp
  | e_if : exp -> exp -> exp -> exp
  | e_eq : exp -> exp -> exp
  | e_plus : exp -> exp -> exp
  | e_minus : exp -> exp -> exp
  | e_lt : exp -> exp -> exp.

  Notation "'v_true'" := (v_bool true)(at level 37).
  Notation "'v_false'" := (v_bool false)(at level 37).
  Notation "'e_true'" := (e_val (v_bool true))(at level 37).
  Notation "'e_false'" := (e_val (v_bool false)).
  Notation "'e_null'" := (e_val v_null).

  Notation "'v_' v" := (e_val v)(at level 38).
  Notation "e ∙ f" := (e_fld e f)(at level 38).
  Notation "'e_' x" := (e_var x)(at level 38).
  Notation "e1 ⩵ e2" := (e_eq e1 e2)(at level 38).

  Inductive stmt :=
  | s_read : var -> exp -> stmt
  | s_write : var -> fld -> exp -> stmt
  | s_call : var -> var -> mth -> list var -> stmt
(*  | s_ret : exp -> stmt*)
  | s_if : exp -> stmt -> stmt -> stmt
  | s_hole : var -> stmt
  | s_new : var -> cls -> stmt
  | s_empty : stmt
  | s_seq : stmt -> stmt -> stmt.

 (* Inductive stmt :=
  | s_read : var -> exp -> stmt
  | s_write : var -> fld -> exp -> stmt
  | s_call : var -> var -> mth -> list var -> stmt
  | s_ret : exp -> stmt
  | s_if : exp -> stmts -> stmts -> stmt
  | s_hole : var -> stmt
  | s_new : var -> cls -> stmt

  with stmts :=
  | s_stmt : stmt -> stmts
  | s_seq : stmts -> stmts -> stmts.*)

(*  Inductive stmt :=
  | s_read : var -> var -> fld -> stmt
  | s_write : var -> fld -> var -> stmt
  | s_call : var -> var -> mth -> list var -> stmt
  | s_ret : var -> stmt
  | s_if : exp -> stmt -> stmt -> stmt
  | s_hole : var -> stmt
  | s_new : var -> cls -> stmt.*)


  Definition ret x := (s_read result x).
  Notation "s ';;' ss" := (s_seq s ss)(at level 41).

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


  #[global] Program Instance eqbGhost : Eq ghost :=
    {
      eqb := fun g1 g2 =>
               match g1, g2 with
               | g_id n1, g_id n2 => n1 =? n2
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
               | v_spec n1, v_spec n2 => n1 =? n2
               | v_prog n1, v_prog n2 => n1 =? n2
               | _, _ => false
               end
    }.
  Next Obligation.
    intros;
    split;
      intros;
      crush.
  Defined.
  Next Obligation.
    intros;
    split;
      intros;
      crush.
  Defined.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    destruct a1, a2; try solve [apply Nat.eqb_sym];
      auto.
  Defined.
  Next Obligation.
    intros; destruct a1, a2;
      try solve [crush];
      try solve [apply Nat.eqb_eq in H;
                 subst;
                 auto].
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      try solve [crush];
      rewrite Nat.eqb_neq in H;
      crush.
  Defined.
  Next Obligation.
    intros; destruct a1; destruct a2;
      try solve [crush];
      apply Nat.eqb_neq;
        crush.
  Defined.
  Next Obligation.
    destruct a1 as [n|n];
      destruct a2 as [m|m];
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

  #[global] Program Instance eqbVal : Eq val :=
    {
      eqb := fun v1 v2 =>
               match v1, v2 with
               | v_addr a1, v_addr a2 => eqb a1 a2
               | v_int n1, v_int n2 => Z.eqb n1 n2
               | v_bool b1, v_bool b2 => Bool.eqb b1 b2
               | v_str s1, v_str s2 => String.eqb s1 s2
               | v_null, v_null => true
               | _, _ => false
               end
    }.
  Solve Obligations of eqbVal with crush.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
(*    destruct a1; destruct a2;
      try solve [crush].
    destruct a, a0;
      try solve [crush].*)
  Admitted.
  Next Obligation.
  Admitted.

  #[global] Program Instance eqbExp : Eq exp :=
    {
      eqb := fix eqb' e1 e2 :=
               match e1, e2 with
               | e_hole n1, e_hole n2 => eqb n1 n2
               | e_var x1, e_var x2 => eqb x1 x2
               | e_val v1, e_val v2 => eqb v1 v2
               | e_fld e1 f1, e_fld e2 f2 => eqb' e1 e2 && eqb f1 f2
               (*)| e_typ : exp -> ty -> exp
               | e_ghost : exp -> ghost -> exp -> exp
               | e_if : exp -> exp -> exp -> exp
               | e_eq : exp -> exp -> exp
               | e_plus : exp -> exp -> exp
               | e_minus : exp -> exp -> exp*)
               | _, _ => false
               end
    }.
  Solve Obligations of eqbExp with crush.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  (**
     Assertions
   **)

  Inductive asrt :=
  | a_exp : exp -> asrt

  | a_and : asrt -> asrt -> asrt
(*  | a_or : asrt -> asrt -> asrt*)
  | a_neg : asrt -> asrt
  | a_all : cls -> asrt -> asrt
(*  | a_ex : cls -> asrt -> asrt*)

(*)  | a_intl : exp -> asrt*)
  | a_extl : exp -> asrt

  | a_prt : exp -> asrt
  | a_prt_frm : exp -> exp -> asrt.

  Notation "'a_' e" := (a_exp e)(at level 38).
  Notation "A1 '∧' A2" := (a_and A1 A2)(at level 39).
  Notation "'¬' A" := (a_neg A)(at level 38).
  Definition a_or A1 A2 := ¬ (¬ A1 ∧ ¬ A2).
  Notation "A1 '∨' A2" := (a_or A1 A2)(at level 39).
  Definition arr A1 A2 := ¬ A1 ∨ A2.
  Notation "A1 ⟶ A2" :=(arr A1 A2)(at level 40).
  Notation "'a_true'" := (a_ (e_true))(at level 37).
  Notation "'a_false'" := (a_ (e_false))(at level 37).
  Notation "e1 ≠ e2" := (¬ a_ (e_eq e1 e2))(at level 37).

  #[global] Program Instance eqbAsrt : Eq asrt :=
    {
      eqb := fix eqb' a1 a2 :=
          match a1, a2 with
          | a_exp e1, a_exp e2 => eqb e1 e2
          | a_and A11 A12, a_and A21 A22 => eqb' A11 A21 && eqb' A12 A22
          | a_neg A1, a_neg A2 => eqb' A1 A2
          | a_all C1 A1, a_all C2 A2 => eqb C1 C2 && eqb' A1 A2
          | a_extl e1, a_extl e2 => eqb e1 e2
          | a_prt e1, a_prt e2 => eqb e1 e2
          | a_prt_frm e11 e12, a_prt_frm e21 e22 => eqb e11 e21 && eqb e12 e22
          | _, _ => false
          end
    }.
  Solve Obligations with crush.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Inductive path :=
  | p_fld : fld -> path
  | p_cons : fld -> path -> path.

  (***
      Core Language Definitions
   ***)

  Inductive l_spec :=
  | S_inv : list (var * ty) -> asrt -> l_spec
  | S_mth : cls -> mth -> list (var * ty) -> asrt -> asrt -> asrt -> l_spec
  | S_and : l_spec -> l_spec -> l_spec.

  Inductive visibility : Type :=
  | public
  | private.

  Record methDef := meth{
                        spec : list (asrt * asrt * asrt);
                        vis : visibility;
                        params : list (var * ty);
                        body : stmt;
                        rtrn : ty
                      }.

  Record classDef :=
    clazz{
        c_name : cls;
        c_fields : partial_map fld ty;
        c_ghosts : partial_map ghost (var * exp);
        c_meths : partial_map mth methDef
      }.

  Definition module := (l_spec * (partial_map cls classDef)) %type.

  Record object := obj{o_cls : cls;
                        o_flds : partial_map fld val}.

  Definition heap := partial_map addr object.

  Record frame := frm{local : partial_map var (val * ty);
                       continuation : stmt}.

  Inductive stack :=
    | stack_cons : frame -> list frame -> stack.

  (*notation for stack: \cdot *)
  Notation "ϕ '⋅' ψ" := (stack_cons ϕ ψ)(at level 41).

  Definition config := (stack * heap) % type.

  Definition top (σ : config) :=
    match σ with
    | (stack_cons ϕ ψ, _) => ϕ
    end.

  Definition interpret_x (σ : config)(x : var) : option val :=
    match σ with
    | (frm lcl c ⋅ ψ, _) => bind (lcl x) (fun x => Some (fst x))
    end.

  Definition interpret_αf (σ : config)(α : addr)(f : fld) : option val :=
    match σ with
    | (ϕ ⋅ ψ, χ) =>
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

  Definition ghostLookup (M : module)(σ : config)(α : addr)(g : ghost) : option (var * exp) :=
    match snd σ α with
    | Some o => match snd M (o_cls o) with
               | Some CDef => c_ghosts CDef g
               | None => None
               end
    | None => None
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
        match snd σ l with
        | Some o => Some (o_cls o)
        | _ => None
        end
    | _ => None
    end.

  Definition typeOf_v (σ : config)(v : val)(t : ty) :=
    match v, t with
    | v_null, _ => True
    | v_int _, t_int => True
    | v_bool _, t_bool => True
    | v_str _, t_str => True
    | v_addr α, t_cls C => match snd σ α with
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

  Definition typeOf_f (M : module) C f :=
    bind (snd M C) (fun def => (c_fields def) f).

End LanguageDefinition.
