Require Export Arith.
Require Import List.

Require Import necessity.CpdtTactics.
Require Import necessity.common.
Require Import necessity.defs.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Type LanguageDef.

  Parameter L_config : Type.

  Parameter config_translation : L_config -> config.

  Declare Scope L_scope.

  Notation "'⟦' σ '⟧'" := (config_translation σ)(at level 40) : L_scope.

  (* read visibility *)
  Parameter visible_r : mdl -> config -> addr -> value -> Prop.
  (* field read visibility *)
  Inductive visible_rf : mdl -> config -> addr -> addr -> fld -> Prop :=
  | vis_rf : forall M χ ψ a1 a2 o1 o2 f, χ a1 = Some o1 ->
                                    χ a2 = Some o2 ->
                                    (cname o1) = (cname o2) ->
                                    (cname o1) ∈ M ->
                                    visible_rf M (χ, ψ) a1 a2 f.

  (* write visibility *)
  Inductive visible_w : mdl -> config -> addr -> addr -> fld -> Prop :=
  | vis_w : forall M χ ψ a1 a2 o1 o2 f, χ a1 = Some o1 ->
                                    χ a2 = Some o2 ->
                                    (cname o1) = (cname o2) ->
                                    (cname o1) ∈ M ->
                                    visible_w M (χ, ψ) a1 a2 f.
  (* method visibility *)
  Parameter visible_m : mdl -> config -> addr -> addr -> mth -> Prop.
  (* constructor visibility *)
  Parameter visible_c : mdl -> config -> addr -> cls -> Prop.

  Parameter visible_r_stack_append :
    forall M σ α v, visible_r M σ α v ->
               forall ψ, visible_r M (σ ◁ ψ) α v.

  Parameter visible_w_stack_append :
    forall M σ α1 α2 f, visible_w M σ α1 α2 f ->
                   forall ψ, visible_w M (σ ◁ ψ) α1 α2 f.

  Parameter visible_m_stack_append :
    forall M σ α1 α2 m, visible_m M σ α1 α2 m ->
                   forall ψ, visible_m M (σ ◁ ψ) α1 α2 m.

  Parameter visible_c_stack_append :
    forall M σ α C, visible_c M σ α C ->
               forall ψ, visible_c M (σ ◁ ψ) α C.

  (* access *)
  Parameter has_access : mdl -> mdl -> config -> addr -> addr -> Prop.

  Parameter access_implies_read_visibility :
    forall M1 M2 σ α1 α2, has_access M1 M2 σ α1 α2 ->
                     forall M, M1 ⋄ M2 ≜ M ->
                     visible_r M σ α1 (v_addr α2).

  Ltac visible_stack_append_auto :=
    match goal with
    | [H : visible_r ?M (?χ, ?ϕ :: nil) ?α ?v
       |- visible_r ?M (?χ, ?ϕ :: ?ψ') ?α ?v] =>
      apply visible_r_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_w ?M (?χ, ?ϕ :: nil) ?α1 ?α2 ?f
       |- visible_w ?M (?χ, ?ϕ :: ?ψ') ?α1 ?α2 ?f] =>
      apply visible_w_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_m ?M (?χ, ?ϕ :: nil) ?α1 ?α2 ?m
       |- visible_m ?M (?χ, ?ϕ :: ?ψ') ?α1 ?α2 ?m] =>
      apply visible_m_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_c ?M (?χ, ?ϕ :: nil) ?α ?C
       |- visible_c ?M (?χ, ?ϕ :: ?ψ') ?α ?C] =>
      apply visible_c_stack_append with (ψ:=ψ') in H;
      auto

    | [H : visible_r ?M (?χ, ?ψ) ?α ?v
       |- visible_r ?M (?χ, ?ψ ++ ?ψ') ?α ?v] =>
      apply visible_r_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_w ?M (?χ, ?ψ) ?α1 ?α2 ?f
       |- visible_w ?M (?χ, ?ψ ++ ?ψ') ?α1 ?α2 ?f] =>
      apply visible_w_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_m ?M (?χ, ?ψ) ?α1 ?α2 ?m
       |- visible_m ?M (?χ, ?ψ ++ ?ψ') ?α1 ?α2 ?m] =>
      apply visible_m_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_c ?M (?χ, ?ψ) ?α ?C
       |- visible_c ?M (?χ, ?ψ ++ ?ψ') ?α ?C] =>
      apply visible_c_stack_append with (ψ:=ψ') in H;
      auto

    | [H : visible_r ?M (?χ, ?ϕ :: ?ψ) ?α ?v
       |- visible_r ?M (?χ, ?ϕ :: ?ψ ++ ?ψ') ?α ?v] =>
      apply visible_r_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_w ?M (?χ, ?ϕ :: ?ψ) ?α1 ?α2 ?f
       |- visible_w ?M (?χ, ?ϕ :: ?ψ ++ ?ψ') ?α1 ?α2 ?f] =>
      apply visible_w_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_m ?M (?χ, ?ϕ :: ?ψ) ?α1 ?α2 ?m
       |- visible_m ?M (?χ, ?ϕ :: ?ψ ++ ?ψ') ?α1 ?α2 ?m] =>
      apply visible_m_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_c ?M (?χ, ?ϕ :: ?ψ) ?α ?C
       |- visible_c ?M (?χ, ?ϕ :: ?ψ ++ ?ψ') ?α ?C] =>
      apply visible_c_stack_append with (ψ:=ψ') in H;
      auto

    | [H : visible_r ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ) ?α ?v
       |- visible_r ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ ++ ?ψ') ?α ?v] =>
      apply visible_r_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_w ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ) ?α1 ?α2 ?f
       |- visible_w ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ ++ ?ψ') ?α1 ?α2 ?f] =>
      apply visible_w_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_m ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ) ?α1 ?α2 ?m
       |- visible_m ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ ++ ?ψ') ?α1 ?α2 ?m] =>
      apply visible_m_stack_append with (ψ:=ψ') in H;
      auto
    | [H : visible_c ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ) ?α ?C
       |- visible_c ?M (?χ, ?ϕ1 :: ?ϕ2 :: ?ψ ++ ?ψ') ?α ?C] =>
      apply visible_c_stack_append with (ψ:=ψ') in H;
      auto
    end.

  (*operational semantics*)
  Parameter L_red : mdl -> mdl -> L_config -> L_config -> Prop.

End LanguageDef.
