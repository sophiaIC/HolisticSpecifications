Require Export Arith.
Require Import List.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Export operational_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

(** Note: this file is included for the purposes of future extensions to Chainmail, but is not required for the
 compilation of the proofs core to this artifact. *)

Module Assert.

  Import LanguageDefinition.
  Import SubstDefn.
  Import OperationalSemantics.


  Declare Scope assert_scope.


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

  Definition reachable (α : addr)(ϕ : frame)(σ : config) : Prop :=
    exists x p, x ∈ (local ϕ) /\ interpret_p p σ x = Some (v_addr α).

  Definition loc_reachable (α : addr)(σ : config) : Prop :=
    exists ϕ ψ, fst σ = ϕ ⋅ ψ /\ reachable α ϕ σ.

  Definition glob_reachable (α : addr)(σ : config) : Prop :=
    exists ϕ ϕ' ψ, fst σ = ϕ ⋅ ψ /\ (ϕ' = ϕ \/ In ϕ' ψ) /\ reachable α ϕ' σ.

  Definition intl (M : module)(σ : config)(α : addr) :=
    exists o, snd σ α = Some o /\
           (o_cls o) ∈ snd M.

  Definition extl (M : module)(σ : config)(α : addr) :=
    forall o, snd σ α = Some o -> ~ (o_cls o) ∈ snd M.

  Inductive is_protected_path : module -> config -> addr -> path -> Prop :=
  | is_prot1 : forall M σ α_orig f1 f2 α1, interpret_αf σ α_orig f1 = Some (v_addr α1) ->
                                      intl M σ α1 ->
                                      is_protected_path M σ α_orig (p_cons f1 (p_fld f2))

  | is_protn : forall M σ α_orig f p α, interpret_αf σ α_orig f = Some (v_addr α) ->
                                   is_protected_path M σ α p ->
                                   is_protected_path M σ α_orig (p_cons f p).

  Definition protected_from (M : module)(σ : config)(α_orig α : addr) :=
    forall p, interpret_αp p σ α_orig = Some (v_addr α) -> is_protected_path M σ α_orig p.

  (** * Assertion Semantics - Sections 4.1 & 4.2 *)

  Inductive sat : module -> config -> asrt -> Prop :=
  | sat_exp : forall M σ e, eval M σ e (v_true) ->
                       sat M σ (a_exp e)

  | sat_and : forall M σ A1 A2, sat M σ A1 ->
                           sat M σ A2 ->
                           sat M σ (A1 ∧ A2)

  | sat_neg : forall M σ A, nsat M σ A ->
                       sat M σ (¬ A)

  | sat_all : forall M σ C A, (forall α, glob_reachable α σ ->
                               eval M σ (e_typ (e_val (v_addr α)) (t_cls C)) (v_true) ->
                               sat M σ ([α /s 0] A)) ->
                         sat M σ (a_all C A)

  | sat_extl1 : forall M σ e C, sat M σ (a_exp (e_typ e (t_cls C))) ->
                          ~ C ∈ snd M ->
                          sat M σ (a_extl e)

  | sat_extl2 : forall M σ e, sat M σ (a_exp (e_typ e (t_ext))) ->
                         sat M σ (a_extl e)

  | sat_prt_frm : forall M σ e e_orig α α_orig, eval M σ e (v_addr α) ->
                                           eval M σ e_orig (v_addr α_orig) ->
                                           α <> α_orig ->
                                           (forall p, interpret_αp p σ α_orig = Some (v_addr α) ->
                                                 is_protected_path M σ α_orig p) ->
                                           sat M σ (a_prt_frm e e_orig)

  | sat_prt_frm_scalar : forall M σ e e_orig T α, eval M σ e (v_addr α) ->
                                             sat M σ (a_ e_typ e_orig T) ->
                                             (T = t_int \/ T = t_str \/ T = t_bool) ->
                                             sat M σ (a_prt_frm e e_orig)

  | sat_prt_frm_intl : forall M σ e e_orig α α_orig, eval M σ e (v_addr α) ->
                                                eval M σ e_orig (v_addr α_orig) ->
                                                α <> α_orig ->
                                                sat M σ (¬ a_extl e) ->
                                                sat M σ (a_prt_frm e e_orig)

  | sat_prt : forall M σ e, (exists α, eval M σ e (v_addr α)) ->
                       (forall α, loc_reachable α σ ->
                             extl M σ α ->
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

  | nsat_neg : forall M σ A, sat M σ A ->
                        nsat M σ (¬ A)

  | nsat_all : forall M σ α C A, glob_reachable α σ ->
                            sat M σ (a_exp (e_typ (e_val (v_addr α)) (t_cls C))) ->
                            nsat M σ ([α /s 0] A) ->
                            nsat M σ (a_all C A)

  | nsat_extl : forall M σ e C, sat M σ (a_exp (e_typ e (t_cls C))) ->
                           C ∈ snd M ->
                           nsat M σ (a_extl e)

  | nsat_prt_from1 : forall M σ e e_orig, (forall α, ~ eval M σ e (v_addr α)) ->
                                     nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from2 : forall M σ e e_orig, (forall α_orig, ~ eval M σ e_orig (v_addr α_orig)) ->
                                     nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from3 : forall M σ e e_orig v v_orig, eval M σ e v ->
                                              eval M σ e_orig v_orig ->
                                              v = v_orig ->
                                              nsat M σ (a_prt_frm e e_orig)

  | nsat_prt_from4 : forall M σ e e_orig α α_orig p, eval M σ e (v_addr α) ->
                                                eval M σ e_orig (v_addr α_orig) ->
                                                interpret_αp p σ α_orig = Some (v_addr α) ->
                                                ~ is_protected_path M σ α_orig p ->
                                                nsat M σ (a_prt_frm e e_orig)

  | nsat_prt1 : forall M σ e, (forall α, ~ eval M σ e (v_addr α)) ->
                         nsat M σ (a_prt e)

  | nsat_prt2 : forall M σ e α, loc_reachable α σ ->
                           sat M σ (a_extl (v_ (v_addr α))) ->
                           nsat M σ (a_prt_frm (v_ (v_addr α)) e) ->
                           nsat M σ (a_prt e).


  Scheme sat_mut_ind := Induction for sat Sort Prop
      with nsat_mut_ind := Induction for nsat Sort Prop.

  Combined Scheme sat_mutind from sat_mut_ind, nsat_mut_ind.

  #[global] Hint Constructors sat : assert_db.

  Close Scope assert_scope.

End Assert.
