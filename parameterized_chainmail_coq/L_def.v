Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Import chainmail.defs.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Type LanguageDef.

  Parameter L_config : Type.

  Parameter config_translation : L_config -> config.

  Declare Scope L_scope.

  Notation "'⟦' σ '⟧'" := (config_translation σ)(at level 40) : L_scope.

  (* read visibility *)
  Parameter visible_r : config -> addr -> value -> Prop.
  (* write visibility *)
  Parameter visible_w : config -> addr -> addr -> fld -> Prop.
  (* method visibility *)
  Parameter visible_m : config -> addr -> addr -> mth -> Prop.
  (* constructor visibility *)
  Parameter visible_c : config -> addr -> cls -> Prop.

  (* access *)
  Parameter has_access : mdl -> mdl -> config -> addr -> addr -> Prop.

  Parameter access_implies_read_visibility :
    forall M1 M2 σ α1 α2, has_access M1 M2 σ α1 α2 ->
                     visible_r σ α1 (v_addr α2).

  (*operational semantics*)
  Parameter L_red : mdl -> mdl -> L_config -> L_config -> Prop.

End LanguageDef.
