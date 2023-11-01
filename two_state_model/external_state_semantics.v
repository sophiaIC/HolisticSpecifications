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
  | v_bool : bool -> val.

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
  | e_var : var -> exp
  | e_val : val -> exp
  | e_fld : exp -> fld -> exp
  | e_class : exp -> cls -> exp
  | e_ghost : exp -> ghost -> exp -> exp
  | e_cond : exp -> exp -> exp -> exp.

  Definition v_true := (v_bool true).
  Definition v_false := (v_bool false).
  Definition e_true := (e_val v_true).
  Definition e_false := (e_val v_false).

  Inductive stmt :=
  | s_read : var -> var -> fld -> stmt
  | s_write : var -> fld -> var -> stmt
  | s_call : var -> var -> mth -> list (var * var) -> stmt
  | s_ret : var -> stmt
  | s_if : exp -> stmt -> stmt -> stmt
  | s_seq : stmt -> stmt -> stmt.

  Inductive contn :=
  | c_stmt : stmt -> contn
  | c_hole : var -> stmt -> contn.

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
      symmetry in H;
      apply beq_nat_eq in H;
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
      symmetry in H;
      apply beq_nat_eq in H;
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
      symmetry in H;
      apply beq_nat_eq in H;
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
      symmetry in H;
      apply beq_nat_eq in H;
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
      symmetry in H;
      apply beq_nat_eq in H;
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
      symmetry in H;
      apply beq_nat_eq in H;
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

  Record classDef := clazz{c_name : cls;
                            c_fields : partial_map fld cls;
                            c_meths : partial_map mth stmt}.

  Definition module := partial_map cls classDef.

  Record object := obj{o_cls : cls;
                        o_flds : partial_map fld val}.

  Definition heap := partial_map addr object.

  Record frame := frm{local : partial_map var val;
                       continuation : contn}.

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

  Fixpoint list_to_map {A B : Type}`{Eq A}(l : list (A * B)) : partial_map A B :=
    match l with
    | nil => empty
    | (a, b) :: t => ⟦ a ↦ b ⟧ (list_to_map t)
    end.

  (* TODO: write expression evaluation *)
  Definition eval (M : module)(σ : config)(e : exp)(v : val) : Prop := True.

  Inductive reduction : module -> config -> config -> Prop :=
  | r_read : forall M σ χ x y v f s lcl ψ c,
      σ = (χ, frm lcl (c_stmt (s_seq (s_read x y f) s)) ;; ψ) ->
      x <> this ->
      classOf σ this = Some c ->
      classOf σ y = Some c ->
      interpret_f σ y f = Some v ->
      reduction M σ (χ, frm (⟦ x ↦ v ⟧  lcl) (c_stmt s) ;; ψ)

  | r_write : forall M σ χ x y v f s lcl l ψ c c' flds,
      σ = (χ, frm lcl (c_stmt (s_seq (s_write x f y) s)) ;; ψ) ->
      classOf σ this = Some c ->
      classOf σ x = Some c ->
      (exists v', interpret_f σ x f = Some v') ->
      interpret_x σ x = Some (v_addr l) ->
      χ l = Some (obj c' flds) ->
      interpret_x σ y = Some v ->
      reduction M σ (⟦ l ↦ obj c' (⟦ f ↦ v ⟧ flds)⟧ χ, frm lcl (c_stmt s) ;; ψ)

  | r_call : forall M σ χ x y m vs s lcl ψ c cDef body l,
      σ = (χ, frm lcl (c_stmt (s_seq (s_call x y m vs) s)) ;; ψ) ->
      interpret_x σ y = Some (v_addr l) ->
      classOf σ y = Some c ->
      M c = Some cDef ->
      c_meths cDef m = Some body ->
      reduction M σ (χ, frm (⟦ this ↦ (v_addr l) ⟧ (lcl ∘ list_to_map vs)) (c_stmt body) ;; (frm lcl (c_hole x s) :: ψ))

  | r_ret1 : forall M σ χ lcl x lcl' y s v ψ,
      σ = (χ, frm lcl (c_stmt (s_ret x)) ;; (frm lcl' (c_hole y s) :: ψ)) ->
      interpret_x σ x = Some v ->
      reduction M σ (χ, frm (⟦ y ↦ v ⟧ lcl') (c_stmt s) ;; ψ)

  | r_ret2 : forall M σ χ lcl x lcl' y s v ψ,
      σ = (χ, frm lcl (c_stmt (s_seq (s_ret x) s)) ;; ((frm lcl' (c_hole y s)) :: ψ)) ->
      interpret_x σ x = Some v ->
      reduction M σ (χ, frm (⟦ y ↦ v ⟧ lcl') (c_stmt s) ;; ψ)

  | r_if1 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (χ, frm lcl (c_stmt (s_seq (s_if e s1 s2) s)) ;; ψ) ->
      eval M σ e v_true ->
      reduction M σ (χ, frm lcl (c_stmt (s_seq s1 s)) ;; ψ)

  | r_if2 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (χ, frm lcl (c_stmt (s_seq (s_if e s1 s2) s)) ;; ψ) ->
      eval M σ e v_false ->
      reduction M σ (χ, frm lcl (c_stmt (s_seq s1 s)) ;; ψ).

End LanguageDefinition.
