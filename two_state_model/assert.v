Require Export Arith.
Require Import List.

Require Import CpdtTactics.
Require Import common.
Require Export external_state_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


Module Assert.

  Module LDef := LanguageDefinition.
  Export LDef.

  Inductive asrt :=
  | a_exp : exp -> asrt

  | a_and : asrt -> asrt -> asrt
  | a_or : asrt -> asrt -> asrt
  | a_neg : asrt -> asrt
  | a_arr : asrt -> asrt -> asrt
  | a_all : var -> asrt -> asrt
  | a_ex : var -> asrt -> asrt

  | a_prt : exp -> asrt
  | a_prt_frm : exp -> exp -> asrt.

  Notation "A1 '∧' A2" := (a_and A1 A2)(at level 39).
  Notation "A1 '∨' A2" := (a_or A1 A2)(at level 39).
  Notation "A1 '⟶' A2" := (a_arr A1 A2)(at level 39).
  Notation "'¬' A" := (a_neg A)(at level 39).

  Inductive path :=
  | p_fld : fld -> path
  | p_cons : fld -> path -> path.

  Fixpoint interpret_αp (p : path)(σ : config)(α : addr) : option val :=
    match p with
    | p_fld f => interpret_αf σ α f
    | p_cons f p' =>
        match interpret_αf σ α f with
        | Some (v_addr α') => interpret_αp p' σ α'
        | _ => None
        end
    end.

  Definition interpret_p (p : path)(σ : config)(x : var) : option val :=
    match interpret_x σ x with
    | Some (v_addr α) => interpret_αp p σ α
    | _ => None
    end.

  Inductive path_to : config -> var -> addr -> Prop :=
  | path_fld : forall σ x f α, interpret_f σ x f = Some (v_addr α) ->
                          path_to σ x α
  | path_trans : forall σ χ ψ x α' o f α, path_to σ x α' ->
                                      σ = (χ, ψ) ->
                                      χ α' = Some o ->
                                      o_flds o f = Some (v_addr α) ->
                                      path_to σ x α.

  (* TODO: relevant definition *)
  Definition relevant (α : addr)(ϕ : frame)(σ : config) : Prop :=
    exists x p, x ∈ (local ϕ) /\ interpret_p p σ x = Some (v_addr α).

  Definition loc_relevant (α : addr)(σ : config) : Prop :=
    exists ϕ ψ, snd σ = ϕ ;; ψ /\ relevant α ϕ σ.

  Definition glob_relevant (α : addr)(σ : config) : Prop :=
    exists ϕ ϕ' ψ, snd σ = ϕ ;; ψ /\ (ϕ' = ϕ \/ In ϕ' ψ) /\ relevant α ϕ' σ.

  Inductive is_protected_path : module -> config -> addr -> path -> Prop :=
  | is_prot1 : forall M σ α_orig f1 f2 α1 o, interpret_αf σ α_orig f1 = Some (v_addr α1) ->
                                        fst σ α1 = Some o ->
                                        (o_cls o) ∈ M ->
                                        is_protected_path M σ α_orig (p_cons f1 (p_fld f2))

  | is_protn : forall M σ α_orig f p α, interpret_αf σ α_orig f = Some (v_addr α) ->
                                   is_protected_path M σ α p ->
                                   is_protected_path M σ α_orig (p_cons f p).

  Definition protected_from (M : module)(σ : config)(α_orig α : addr) :=
    forall p, interpret_αp p σ α_orig = Some (v_addr α) -> is_protected_path M σ α_orig p.

  Inductive sat : module -> config -> asrt -> Prop :=
  | sat_exp : forall M σ e, eval M σ e v_true ->
                       sat M σ (a_exp e)

  | sat_and : forall M σ A1 A2, sat M σ A1 ->
                           sat M σ A2 ->
                           sat M σ (A1 ∧ A2)

  | sat_or1 : forall M σ A1 A2, sat M σ A1 ->
                           sat M σ (A1 ∨ A2)

  | sat_or2 : forall M σ A1 A2, sat M σ A2 ->
                           sat M σ (A1 ∨ A2)

  | sat_arr1 : forall M σ A1 A2, nsat M σ A1 ->
                            sat M σ (A1 ⟶ A2)

  | sat_arr2 : forall M σ A1 A2, sat M σ A2 ->
                            sat M σ (A1 ⟶ A2)

  | sat_neg : forall M σ A, nsat M σ A ->
                       sat M σ (¬ A)

  | sat_all : forall M σ x A, (forall α, glob_relevant α σ ->
                               sat M σ A) ->
                         sat M σ (a_all x A)

  | sat_ex : forall M σ x α A, glob_relevant α σ ->
                          sat M σ (a_ex x A)

  | sat_prt_from : forall M σ e e_orig α α_orig, eval M σ e (v_addr α) ->
                                            eval M σ e_orig (v_addr α_orig) ->
                                            (forall p, interpret_αp p σ α_orig = Some (v_addr α) ->
                                                  is_protected_path M σ α_orig p) ->
                                            sat M σ (a_prt_frm e e_orig)


  with  nsat : module -> config -> asrt -> Prop :=
  | nsat_exp : forall M σ e, (forall v, eval M σ e v ->
                              v <> v_true) ->
                        nsat M σ (a_exp e).

End Assert.

