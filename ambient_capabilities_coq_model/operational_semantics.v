Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.

Require Import language_def.
Require Import subst.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


Module OperationalSemantics.

  Import LanguageDefinition.
  Import SubstDefn.

  Fixpoint list_to_map {A B : Type}`{Eq A}(l : list (A * B)) : partial_map A B :=
    match l with
    | nil => empty
    | (a, b) :: t => ⟦ a ↦ b ⟧ (list_to_map t)
    end.


  Inductive eval : module -> config -> exp -> val -> Prop :=
  | eval_val : forall M σ v, eval M σ (v_ v) v

  | eval_var : forall M σ x v, local (top σ) x = Some v ->
                          eval M σ (e_ x) (fst v)

  | eval_fld : forall M σ e f α v, eval M σ e (v_addr α) ->
                              interpret_αf σ α f = Some v ->
                              eval M σ (e_fld e f) v
  | eval_ghost : forall M σ e0 g e1 α e x body v1 v,
      eval M σ e0 (v_addr α) ->
      ghostLookup M σ α g = Some (x, body) ->
      eval M σ e1 v1 -> (* eager or lazy eval? does it matter? *)
      eval M σ ([v_ v1 /s x] body) v ->
      eval M σ (e_ghost e0 g e) v

  | eval_class : forall M σ e T α,
      eval M σ e (v_addr α) ->
      typeOf_v σ (v_addr α) T ->
      eval M σ (e_typ e T) (v_true)

  | eval_eq : forall M σ e1 e2 v,
      eval M σ e1 v ->
      eval M σ e2 v ->
      eval M σ (e_eq e1 e2) (v_true)

  | eval_if_true : forall M σ e e1 e2 v1,
      eval M σ e (v_true) ->
      eval M σ e1 v1 ->
      eval M σ (e_if e e1 e2) v1

  | eval_if_false : forall M σ e e1 e2 v2,
      eval M σ e (v_false) ->
      eval M σ e2 v2 ->
      eval M σ (e_if e e1 e2) v2.


  Fixpoint zip_to_map {A B C : Type}`{Eq A}`{Eq B} (l1 : list A)(l2 : list B)(m : partial_map B C) : option (partial_map A C) :=
    match l1, l2 with
    | nil, nil => Some empty
    | a::l1', b::l2' => match m b, zip_to_map l1' l2' m with
                     | Some c, Some ac => Some (⟦a ↦ c⟧ ac)
                     | _, _ => None
                     end
    | _, _ => None
    end.

  (*
    seq handles removal of s_empty from terms during reduction of sequences
   *)

  Definition seq s1 s2 :=
    match s1 with
    | s_empty => s2
    | _ => (s_seq s1 s2)
    end.

  (*
    change encoding to only include continuation within the
    stack tail? This would allow for easier/cleaner induction
    on the reduction definition
   *)

  Inductive reduction : module -> config -> config -> Prop :=
  | r_read : forall M χ x e v lcl ψ T,
      x <> this ->
(*      classOf (frm lcl (s_read x e) ⋅ ψ, χ) this = Some C ->*)
      (* TODO: check e is constrained *)
      (* TODO: check e is the correct type *)
      typeOf (frm lcl (s_read x e) ⋅ ψ, χ) x T ->
      eval M (frm lcl (s_read x e) ⋅ ψ, χ) e v ->
      eval M (frm lcl (s_read x e) ⋅ ψ, χ) (e_typ e T) (v_true) ->
      reduction M (frm lcl (s_read x e) ⋅ ψ, χ) (frm (⟦ x ↦ (v, T) ⟧  lcl) s_empty ⋅ ψ, χ)

  | r_write : forall M χ x e v f lcl l ψ C flds CDef Tf,
      classOf (frm lcl (s_write x f e) ⋅ ψ, χ) this = Some C ->
      classOf (frm lcl (s_write x f e) ⋅ ψ, χ) x = Some C ->
      snd M C = Some CDef ->
      c_fields CDef f = Some Tf ->
      (* TODO: type of e is Tf *)
      interpret_x (frm lcl (s_write x f e) ⋅ ψ, χ) x = Some (v_addr l) ->
      χ l = Some (obj C flds) ->
      eval M (frm lcl (s_write x f e) ⋅ ψ, χ) e v ->
      reduction M
        (frm lcl (s_write x f e) ⋅ ψ, χ)
        (frm lcl s_empty ⋅ ψ, ⟦ l ↦ obj C (⟦ f ↦ v ⟧ flds)⟧ χ)

  | r_call : forall M χ x y m ps lcl ψ C CDef mDef lcl' l,
      interpret_x (frm lcl (s_call x y m ps) ⋅ ψ, χ) y = Some (v_addr l) ->
      classOf (frm lcl (s_call x y m ps) ⋅ ψ, χ) y = Some C ->
      snd M C = Some CDef ->
      c_meths CDef m = Some mDef ->
      typeOf_l (frm lcl (s_call x y m ps) ⋅ ψ, χ) ps (map snd (params mDef)) ->
      zip_to_map (map fst (params mDef)) ps lcl = Some lcl' ->
      reduction M
        (frm lcl (s_call x y m ps) ⋅ ψ, χ)
        (frm (⟦ this ↦ (v_addr l, rtrn mDef) ⟧ lcl') (body mDef) ⋅ (frm lcl (s_hole x) :: ψ), χ)

  | r_new : forall M χ lcl ψ x C α o CDef flds,
      snd M C = Some CDef ->
      c_fields CDef = flds ->
      o = obj C ((fun _ => Some v_null) ∘ flds) ->
      reduction M
        (frm lcl (s_new x C) ⋅ ψ, χ)
        (frm (⟦ x ↦ (v_addr α, t_cls C) ⟧ lcl) s_empty ⋅ ψ, ⟦ α ↦ o⟧ χ)

  | r_ret : forall M χ lcl lcl' x v ψ T,
      lcl result = Some (v, T) ->
      reduction M
        (frm lcl s_empty ⋅ (frm lcl' (s_hole x) :: ψ), χ)
        (frm (⟦ x ↦ (v, T) ⟧ lcl') s_empty ⋅ ψ, χ)

  | r_if1 : forall M χ lcl e s1 s2 ψ,
      eval M (frm lcl (s_if e s1 s2) ⋅ ψ, χ) e (v_true) ->
      reduction M
        (frm lcl (s_if e s1 s2) ⋅ ψ, χ)
        (frm lcl s1 ⋅ ψ, χ)

  | r_if2 : forall M χ lcl e s1 s2 ψ,
      eval M (frm lcl (s_if e s1 s2) ⋅ ψ, χ) e (v_false) ->
      reduction M
        (frm lcl (s_if e s1 s2) ⋅ ψ, χ)
        (frm lcl s2 ⋅ ψ, χ)

  | r_seq_call : forall M χ lcl s1 s2 s ϕ ψ,
      reduction M (frm lcl s1 ⋅ ψ, χ) (ϕ ⋅ (frm lcl s :: ψ), χ) ->
      reduction M
        (frm lcl (s_seq s1 s2) ⋅ ψ, χ)
        (ϕ ⋅ (frm lcl (seq s s2) :: ψ), χ)

  | r_seq_ret : forall M χ lcl lcl' s1 s2 s ϕ ψ,
      reduction M (ϕ ⋅ (frm lcl s1 :: ψ), χ) (frm lcl' s ⋅ ψ, χ) ->
      reduction M
        (ϕ ⋅ (frm lcl' (s_seq s1 s2) :: ψ), χ)
        (frm lcl' (seq s s2) ⋅ ψ, χ)

  | r_seq : forall M χ lcl s1 s2 s ψ,
      reduction M (frm lcl s1 ⋅ ψ, χ) (frm lcl s ⋅ ψ, χ) ->
      reduction M
        (frm lcl (s_seq s1 s2) ⋅ ψ, χ)
        (frm lcl (seq s s2) ⋅ ψ, χ).

  Inductive sublist `{A : Type} : list A -> list A -> Prop :=
  | sub_refl : forall l, sublist l l
  | sub_cons : forall l h t, sublist l t ->
                        sublist l (h :: t).

  Definition scoped_config (σsc σ : config) :=
    (exists ϕsc ψsc ϕ ψ, fst σsc = ϕsc ⋅ ψsc /\
                      fst σ = ϕ ⋅ ψ /\
                      sublist ψsc ψ).

  Definition scoped_execution (M : module)(σsc σ1 σ2 : config) :=
    reduction M σ1 σ2 /\
      scoped_config σsc σ1 /\
      scoped_config σsc σ2.

  Inductive scoped_executions : module -> config -> config -> config -> Prop :=
  | scx_refl : forall M σsc σ, scoped_config σsc σ ->
                          scoped_executions M σsc σ σ
  | scx_trans : forall M σsc σ1 σ2 σ3, scoped_execution M σsc σ1 σ2 ->
                                  scoped_executions M σsc σ2 σ3 ->
                                  scoped_executions M σsc σ1 σ3.

  Definition scoped_exec M σ := scoped_executions M σ σ.

  Definition scoped_final M σsc σ1 σ2 :=
    scoped_executions M σsc σ1 σ2 /\
      forall σ, ~ scoped_execution M σsc σ2 σ.

  Definition final M σ:= scoped_final M σ σ.

End OperationalSemantics.
