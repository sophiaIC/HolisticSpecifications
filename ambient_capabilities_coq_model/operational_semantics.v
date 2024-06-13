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
                          eval M σ (e_ x) v

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
      eval M σ (e_typ e T) v_true

  | eval_eq : forall M σ e1 e2 v,
      eval M σ e1 v ->
      eval M σ e2 v ->
      eval M σ (e_eq e1 e2) v_true

  | eval_if_true : forall M σ e e1 e2 v1,
      eval M σ e v_true ->
      eval M σ e1 v1 ->
      eval M σ (e_if e e1 e2) v1

  | eval_if_false : forall M σ e e1 e2 v2,
      eval M σ e v_false ->
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

  Inductive reduction : module -> config -> config -> Prop :=
  | r_read : forall M σ χ x y v f lcl ψ C s,
      σ = (frm lcl (s_seq (s_read x y f) s) ;; ψ, χ) ->
      x <> this ->
      classOf σ this = Some C ->
      classOf σ y = Some C ->
      interpret_f σ y f = Some v ->
      reduction M σ (frm (⟦ x ↦ v ⟧  lcl) s ;; ψ, χ)

  | r_write : forall M σ χ x y v f lcl l ψ s C flds CDef Tf,
      σ = (frm lcl (s_seq (s_write x f y) s) ;; ψ, χ) ->
      classOf σ this = Some C ->
      classOf σ x = Some C ->
      snd M C = Some CDef ->
      c_fields CDef f = Some Tf ->
      typeOf σ y Tf ->
      interpret_x σ x = Some (v_addr l) ->
      χ l = Some (obj C flds) ->
      interpret_x σ y = Some v ->
      reduction M σ (frm lcl s ;; ψ, ⟦ l ↦ obj C (⟦ f ↦ v ⟧ flds)⟧ χ)

  | r_call : forall M σ χ x y m ps lcl s ψ C CDef mDef lcl' l,
      σ = (frm lcl (s_seq (s_call x y m ps) s) ;; ψ, χ) ->
      interpret_x σ y = Some (v_addr l) ->
      classOf σ y = Some C ->
      snd M C = Some CDef ->
      c_meths CDef m = Some mDef ->
      typeOf_l σ ps (map snd (params mDef)) ->
      zip_to_map (map fst (params mDef)) ps lcl = Some lcl' ->
      reduction M σ (frm (⟦ this ↦ (v_addr l) ⟧ lcl') (body mDef) ;; (frm lcl (s_seq (s_hole x) s) :: ψ), χ)

  | r_new : forall M σ χ lcl s ψ x C α o CDef flds,
      σ = (frm lcl (s_seq (s_new x C) s) ;; ψ, χ) ->
      snd M C = Some CDef ->
      c_fields CDef = flds ->
      o = obj C ((fun _ => Some v_null) ∘ flds) ->
      reduction M σ (frm (⟦ x ↦ v_addr α ⟧ lcl) s ;; ψ, ⟦ α ↦ o⟧ χ)

  | r_ret : forall M σ χ lcl x lcl' s1 s2 y v ψ,
      σ = (frm lcl (s_seq (s_ret x)  s1) ;; (frm lcl' (s_seq (s_hole y) s2) :: ψ), χ) ->
      interpret_x σ x = Some v ->
      reduction M σ (frm (⟦ y ↦ v ⟧ lcl') s2 ;; ψ, χ)

  | r_if1 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (frm lcl (s_seq (s_if e s1 s2) s) ;; ψ, χ) ->
      eval M σ e v_true ->
      reduction M σ (frm lcl (s_seq s1 s) ;; ψ, χ)

  | r_if2 : forall M σ χ lcl e s1 s2 s ψ,
      σ = (frm lcl (s_seq (s_if e s1 s2) s) ;; ψ, χ) ->
      eval M σ e v_false ->
      reduction M σ (frm lcl (s_seq s1 s) ;; ψ, χ).

  Inductive sublist `{A : Type} : list A -> list A -> Prop :=
  | sub_refl : forall l, sublist l l
  | sub_cons : forall l h t, sublist l t ->
                        sublist l (h :: t).

  Definition scoped_config (σsc σ : config) :=
    (exists ϕsc ψsc ϕ ψ, fst σsc = ϕsc ;; ψsc /\
                      fst σ = ϕ ;; ψ /\
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
