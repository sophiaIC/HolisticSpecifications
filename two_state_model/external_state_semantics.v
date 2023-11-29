Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


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

  Record classDef := clazz{c_name : cls;
                            c_fields : partial_map fld ty;
                            c_meths : partial_map mth ((list (var * ty)) * stmts)}.

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

  Fixpoint list_to_map {A B : Type}`{Eq A}(l : list (A * B)) : partial_map A B :=
    match l with
    | nil => empty
    | (a, b) :: t => ⟦ a ↦ b ⟧ (list_to_map t)
    end.

  (* TODO: write expression evaluation *)
  Definition eval (M : module)(σ : config)(e : exp)(v : val) : Prop := True.

  Fixpoint zip_to_map {A B C : Type}`{Eq A}`{Eq B} (l1 : list A)(l2 : list B)(m : partial_map B C) : option (partial_map A C) :=
    match l1, l2 with
    | nil, nil => Some empty
    | a::l1', b::l2' => match m b, zip_to_map l1' l2' m with
                     | Some c, Some ac => Some (⟦a ↦ c⟧ ac)
                     | _, _ => None
                     end
    | _, _ => None
    end.

  Inductive reduction : module -> config -> config -> Prop :=
  | r_read : forall M σ χ x y v f lcl ψ C s,
      σ = (χ, frm lcl (s_seq (s_read x y f) s) ;; ψ) ->
      x <> this ->
      classOf σ this = Some C ->
      classOf σ y = Some C ->
      interpret_f σ y f = Some v ->
      reduction M σ (χ, frm (⟦ x ↦ v ⟧  lcl) s ;; ψ)

  | r_write : forall M σ χ x y v f lcl l ψ s C flds CDef Tf,
      σ = (χ, frm lcl (s_seq (s_write x f y) s) ;; ψ) ->
      classOf σ this = Some C ->
      classOf σ x = Some C ->
      M C = Some CDef ->
      c_fields CDef f = Some Tf ->
      typeOf σ y Tf ->
      interpret_x σ x = Some (v_addr l) ->
      χ l = Some (obj C flds) ->
      interpret_x σ y = Some v ->
      reduction M σ (⟦ l ↦ obj C (⟦ f ↦ v ⟧ flds)⟧ χ, frm lcl s ;; ψ)

  | r_call : forall M σ χ x y m ps lcl s ψ C CDef xs body lcl' l,
      σ = (χ, frm lcl (s_seq (s_call x y m ps) s) ;; ψ) ->
      interpret_x σ y = Some (v_addr l) ->
      classOf σ y = Some C ->
      M C = Some CDef ->
      c_meths CDef m = Some (xs, body) ->
      typeOf_l σ ps (map snd xs) ->
      zip_to_map (map fst xs) ps lcl = Some lcl' ->
      reduction M σ (χ, frm (⟦ this ↦ (v_addr l) ⟧ lcl') body ;; (frm lcl (s_seq (s_hole x) s) :: ψ))

  | r_new : forall M σ χ lcl s ψ x C α o CDef flds,
      σ = (χ, frm lcl (s_seq (s_new x C) s) ;; ψ) ->
      M C = Some CDef ->
      c_fields CDef = flds ->
      o = obj C ((fun _ => Some v_null) ∘ flds) ->
      reduction M σ (⟦ α ↦ o⟧ χ, frm (⟦ x ↦ v_addr α ⟧ lcl) s ;; ψ)

  | r_ret : forall M σ χ lcl x lcl' s1 s2 y v ψ,
      σ = (χ, frm lcl (s_seq (s_ret x)  s1) ;; (frm lcl' (s_seq (s_hole y) s2) :: ψ)) ->
      interpret_x σ x = Some v ->
      reduction M σ (χ, frm (⟦ y ↦ v ⟧ lcl') s2 ;; ψ)

  | r_if1 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (χ, frm lcl (s_seq (s_if e s1 s2) s) ;; ψ) ->
      eval M σ e v_true ->
      reduction M σ (χ, frm lcl (s_seq s1 s) ;; ψ)

  | r_if2 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (χ, frm lcl (s_seq (s_if e s1 s2) s) ;; ψ) ->
      eval M σ e v_false ->
      reduction M σ (χ, frm lcl (s_seq s1 s) ;; ψ).

End LanguageDefinition.
