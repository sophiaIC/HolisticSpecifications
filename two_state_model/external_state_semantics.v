Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


Module ExternalStateSemantics.

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

  Inductive cls :=
  | c_id : nat -> cls.

  Inductive var :=
  | v_id : nat -> var.

  Inductive mdl :=
  | mdl_id : nat -> mdl.

  Inductive program :=
  | prog :  mdl-> program
  | call : var -> mth -> list var -> program
  | ret : var -> program.

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
                            c_meths : partial_map mth program}.

  Definition module := partial_map cls classDef.

  Record object := obj{o_cls : cls;
                        o_flds : partial_map fld val}.

  Definition heap := partial_map addr object.

  Definition config := (pair (pair heap (list var))).

  Inductive reduction : config -> program -> Prop :
  | 

End ExternalStateSemantics.
