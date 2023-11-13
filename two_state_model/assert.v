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
  | a_all : var -> asrt -> asrt
  | a_ex : var -> asrt -> asrt

  | a_intl : exp -> asrt
  | a_extl : exp -> asrt

  | a_prt : exp -> asrt
  | a_prt_frm : exp -> exp -> asrt.

  Notation "A1 '∧' A2" := (a_and A1 A2)(at level 39).
  Notation "A1 '∨' A2" := (a_or A1 A2)(at level 39).
(*)  Notation "A1 '⟶' A2" := (a_arr A1 A2)(at level 39).*)
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

  Class Subst (A B C : Type) : Type :=
    {
      sbst : A -> B -> C -> A
    }.

  Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

  #[global] Instance exp_subst : Subst exp nat addr:=
    {
    sbst :=
      fix sbst' e n α :=
          match e with
          | e_hole m  => if beq_nat n m
                        then e_val (v_addr α)
                        else e_hole m
          | e_fld e' f => e_fld (sbst' e' n α) f
          | e_class e' C => e_class (sbst' e' n α) C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 n α) g (sbst' e1 n α)
          | e_if e0 e1 e2 => e_if (sbst' e0 n α) (sbst' e1 n α) (sbst' e2 n α)
          | _ => e
          end
    }.

  #[global] Instance asrtSubst : Subst asrt nat addr:=
    {
    sbst :=
      fix sbst' A n α :=
        match A with
        | a_exp e     => a_exp ([ α /s n ] e)
        | A1 ∧ A2     => (sbst' A1 n α) ∧ (sbst' A2 n α)
        | A1 ∨ A2     => (sbst' A1 n α) ∨ (sbst' A2 n α)
        | ¬ A         => ¬ (sbst' A n α)
(*)        | A1 ⟶ A2   => (sbst' A1 n α) ⟶ (sbst' A2 n α)*)

        | a_all x A    => a_all x (sbst' A (S n) α)
        | a_ex x A   => a_ex x (sbst' A (S n) α)

        | a_intl e => a_intl ([α /s n] e)
        | a_extl e => a_extl ([α /s n] e)

        | a_prt_frm e1 e2 => a_prt_frm ([α /s n] e1) ([α /s n] e2)
        | a_prt e => a_prt ([α /s n] e)
        end
    }.

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

  | sat_neg : forall M σ A, nsat M σ A ->
                       sat M σ (¬ A)

  | sat_all : forall M σ x A, (forall α, glob_relevant α σ ->
                               sat M σ ([α /s 0] A)) ->
                         sat M σ (a_all x A)

  | sat_ex : forall M σ x α A, glob_relevant α σ ->
                          sat M σ ([α /s 0] A) ->
                          sat M σ (a_ex x A)

  | sat_intl : forall M σ e C, sat M σ (a_exp (e_class e C)) ->
                          C ∈ M ->
                          sat M σ (a_intl e)

  | sat_extl : forall M σ e C, sat M σ (a_exp (e_class e C)) ->
                          ~ C ∈ M ->
                          sat M σ (a_extl e)

  | sat_prt_from : forall M σ e e_orig α α_orig, eval M σ e (v_addr α) ->
                                            eval M σ e_orig (v_addr α_orig) ->
                                            (forall p, interpret_αp p σ α_orig = Some (v_addr α) ->
                                                  is_protected_path M σ α_orig p) ->
                                            sat M σ (a_prt_frm e e_orig)

  | sat_prt : forall M σ e, (forall α, loc_relevant α σ ->
                             sat M σ (a_prt_frm e (e_val (v_addr α)))) ->
                       sat M σ (a_prt e)


  with  nsat : module -> config -> asrt -> Prop :=

  | nsat_exp : forall M σ e, (forall v, eval M σ e v ->
                              v <> v_true) ->
                        nsat M σ (a_exp e)

  | nsat_and1 : forall M σ A1 A2, nsat M σ A1 ->
                             nsat M σ (A1 ∧ A2)

  | nsat_and2 : forall M σ A1 A2, nsat M σ A2 ->
                             nsat M σ (A1 ∧ A2)

  | nsat_or : forall M σ A1 A2, nsat M σ A1 ->
                           nsat M σ A2 ->
                           nsat M σ (A1 ∨ A2)

  | nsat_neg : forall M σ A, sat M σ A ->
                        nsat M σ (¬ A)

  | nsat_all : forall M σ x α A, glob_relevant α σ ->
                            nsat M σ ([α /s 0] A) ->
                            nsat M σ (a_all x A)

  | nsat_ex : forall M σ x A, (forall α, glob_relevant α σ ->
                                nsat M σ ([α /s 0] A)) ->
                         nsat M σ (a_ex x A)

  | nsat_intl : forall M σ e C, sat M σ (a_exp (e_class e C)) ->
                           ~C ∈ M ->
                           nsat M σ (a_intl e)

  | nsat_extl : forall M σ e C, sat M σ (a_exp (e_class e C)) ->
                           C ∈ M ->
                           nsat M σ (a_extl e)

  | nsat_prt_from1 : forall M σ e e_orig, (forall v α, eval M σ e v ->
                                             v <> v_addr α) ->
                                     nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from2 : forall M σ e e_orig, (forall v_orig α, eval M σ e_orig v_orig ->
                                                  v_orig <> v_addr α) ->
                                     nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from3 : forall M σ e e_orig v v_orig, eval M σ e v ->
                                              eval M σ e_orig v_orig ->
                                              v = v_orig ->
                                              nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from4 : forall M σ e e_orig α α_orig p, eval M σ e (v_addr α) ->
                                                eval M σ e_orig (v_addr α_orig) ->
                                                interpret_αp p σ α_orig = Some (v_addr α) ->
                                                ~ is_protected_path M σ α_orig p ->
                                                nsat M σ (a_prt_frm e e_orig).

End Assert.

