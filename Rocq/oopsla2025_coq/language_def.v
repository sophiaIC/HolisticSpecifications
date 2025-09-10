Require Import Arith.
Require Import Bool.
Require Export ZArith.ZArith.
Require Import List.
Require Import common.
Require Import CpdtTactics.

Module LanguageDefinition.

  Import ZArith.ZArith.

  (** * Lul Syntax - Section 3.1 *)

  Inductive addr :=
  | address : nat -> addr.

  Inductive val :=
  | v_addr : addr -> val
  | v_int : Z -> val
  | v_bool : bool -> val
  | v_str : String.string -> val
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
  | v_spec : nat -> var
  | v_prog : nat -> var.

  Definition this := v_prog 0.
  Definition result := v_prog 1.

  Inductive mdl :=
  | mdl_id : nat -> mdl.

  Inductive ty : Type :=
  | t_cls : cls -> ty
  | t_int : ty
  | t_bool : ty
  | t_str : ty
  | t_ext : ty.

  Inductive exp :=
  | e_hole : nat -> exp
  | e_var : var -> exp
  | e_val : val -> exp
  | e_fld : exp -> fld -> exp
  | e_typ : exp -> ty -> exp
  | e_ghost : exp -> ghost -> exp -> exp
  | e_if : exp -> exp -> exp -> exp
  | e_eq : exp -> exp -> exp
  | e_plus : exp -> exp -> exp
  | e_minus : exp -> exp -> exp
  | e_lt : exp -> exp -> exp.

  Notation "'v_true'" := (v_bool true)(at level 37).
  Notation "'v_false'" := (v_bool false)(at level 37).
  Notation "'e_true'" := (e_val (v_bool true))(at level 37).
  Notation "'e_false'" := (e_val (v_bool false)).
  Notation "'e_null'" := (e_val v_null).

  Notation "'v_' v" := (e_val v)(at level 38).
  Notation "e ∙ f" := (e_fld e f)(at level 38).
  Notation "'e_' x" := (e_var x)(at level 38).
  Notation "e1 ⩵ e2" := (e_eq e1 e2)(at level 38).

  Inductive stmt :=
  | s_read : var -> exp -> stmt
  | s_write : var -> fld -> exp -> stmt
  | s_call : var -> var -> mth -> list var -> stmt
  | s_if : exp -> stmt -> stmt -> stmt
  | s_hole : var -> stmt
  | s_new : var -> cls -> stmt
  | s_empty : stmt
  | s_seq : stmt -> stmt -> stmt.

  Definition ret x := (s_read result x).
  Notation "s ';;' ss" := (s_seq s ss)(at level 41).

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

  #[global] Program Instance eqbGhost : Eq ghost :=
    {
      eqb := fun g1 g2 =>
               match g1, g2 with
               | g_id n1, g_id n2 => n1 =? n2
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

  #[global] Program Instance eqbVar : Eq var :=
    {
      eqb := fun x1 x2 =>
               match x1, x2 with
               | v_spec n1, v_spec n2 => n1 =? n2
               | v_prog n1, v_prog n2 => n1 =? n2
               | _, _ => false
               end
    }.
  Next Obligation.
    intros;
    split;
      intros;
      crush.
  Defined.
  Next Obligation.
    intros;
    split;
      intros;
      crush.
  Defined.
  Next Obligation.
    intros; destruct a; apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    destruct a1, a2; try solve [apply Nat.eqb_sym];
      auto.
  Defined.
  Next Obligation.
    intros; destruct a1, a2;
      try solve [crush];
      try solve [apply Nat.eqb_eq in H;
                 subst;
                 auto].
  Defined.
  Next Obligation.
    intros;
      destruct a1;
      destruct a2;
      try solve [crush];
      rewrite Nat.eqb_neq in H;
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

  #[global] Program Instance eqbTy : Eq ty :=
    {
      eqb := fun T1 T2 =>
               match T1, T2 with
               | t_cls C1, t_cls C2 => eqb C1 C2
               | t_int, t_int => true
               | t_bool, t_bool => true
               | t_str, t_str => true
               | t_ext, t_ext => true
               | _, _ => false
               end
    }.
  Solve Obligations of eqbTy with crush.
  Next Obligation.
    match goal with
    | [a : ?T |- _] =>
        destruct a
    end;
    auto.
    match goal with
    | [c : ?T |- _] =>
        rewrite <- (eqb_refl c)
    end;
    simpl;
    auto.
  Defined.
  Next Obligation.
    match goal with
    | [a1 : ?T, a2 : ?T |- _] =>
        destruct a1, a2
    end;
    auto.
    match goal with
    | [c1 : ?T, c2 : ?T |- _] =>
        destruct c1, c2;
        apply Nat.eqb_sym
    end.
  Defined.
  Next Obligation.
    match goal with
    | [a1 : ?T, a2 : ?T |- _] =>
        destruct a1, a2
    end;
    try solve [match goal with
               | [H : false = true |- _] =>
                   inversion H
               end];
    auto.
    match goal with
    | [a1 : ?T, a2 : ?T |- _] =>
        destruct a1, a2
    end.
    apply Nat.eqb_eq in H;
      subst;
      auto.
  Defined.
  Next Obligation.
    match goal with
    | [a1 : ?T, a2 : ?T |- _] =>
        destruct a1, a2
    end;
    try solve [crush].
    intro Hcontra;
      inversion Hcontra;
      subst.
    destruct c0.
    apply Nat.eqb_neq in H.
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

  #[global] Program Instance eqbVal : Eq val :=
    {
      eqb := fun v1 v2 =>
               match v1, v2 with
               | v_addr a1, v_addr a2 => eqb a1 a2
               | v_int n1, v_int n2 => Z.eqb n1 n2
               | v_bool b1, v_bool b2 => Bool.eqb b1 b2
               | v_str s1, v_str s2 => String.eqb s1 s2
               | v_null, v_null => true
               | _, _ => false
               end
    }.
  Solve Obligations of eqbVal with crush.
  Next Obligation.
    destruct a;
      auto;
      try solve [crush].
    destruct a.
    apply Nat.eqb_refl.
    apply eqb_reflx.
    apply String.eqb_refl.
  Defined.
  Next Obligation.
    destruct a1, a2;
      auto;
      try solve [crush].
    destruct a, a0.
    apply Nat.eqb_sym.
    destruct b, b0; auto.
    apply String.eqb_sym.
  Defined.
  Next Obligation.
    destruct a1, a2;
      crush.
    destruct a, a0; auto.
    apply Nat.eqb_eq in H;
      subst;
      auto.
    apply Z.eqb_eq in H;
      subst;
      auto.
    destruct b, b0;
      crush.
    apply String.eqb_eq in H;
      subst;
      auto.
  Defined.
  Next Obligation.
    destruct a1, a2;
      crush.
    destruct a0.
    rewrite Nat.eqb_refl in H;
      crush.
    rewrite Bool.eqb_reflx in H;
      crush.
    rewrite String.eqb_refl in H;
      crush.
  Defined.

  Fixpoint eqbExpHelper e1 e2 :=
    match e1, e2 with
    | e_hole n1, e_hole n2 => eqb n1 n2
    | e_var x1, e_var x2 => eqb x1 x2
    | e_val v1, e_val v2 => eqb v1 v2
    | e_fld e1 f1, e_fld e2 f2 => eqbExpHelper e1 e2 && eqb f1 f2
    | e_typ e1 T1, e_typ e2 T2 => eqbExpHelper e1 e2 && eqb T1 T2
    | e_ghost e1 g1 e1', e_ghost e2 g2 e2' => eqbExpHelper e1 e2 &&
                                               eqb g1 g2 &&
                                               eqbExpHelper e1' e2'
    | e_if e0 e1 e2, e_if e0' e1' e2' => eqbExpHelper e0 e0' &&
                                          eqbExpHelper e1 e1' &&
                                          eqbExpHelper e2 e2'
    | e_eq e1 e2, e_eq e1' e2' => eqbExpHelper e1 e1' &&
                                   eqbExpHelper e2 e2'
    | e_plus e1 e2, e_plus e1' e2' => eqbExpHelper e1 e1' &&
                                       eqbExpHelper e2 e2'
    | e_minus e1 e2, e_minus e1' e2' => eqbExpHelper e1 e1' &&
                                         eqbExpHelper e2 e2'
    | e_lt e1 e2, e_lt e1' e2' => eqbExpHelper e1 e1' &&
                                   eqbExpHelper e2 e2'
    | _, _ => false
    end.

  #[global] Program Instance eqbExp : Eq exp :=
    {
      eqb := fix eqb' e1 e2 :=
               match e1, e2 with
               | e_hole n1, e_hole n2 => eqb n1 n2
               | e_var x1, e_var x2 => eqb x1 x2
               | e_val v1, e_val v2 => eqb v1 v2
               | e_fld e1 f1, e_fld e2 f2 => eqb' e1 e2 && eqb f1 f2
               | e_typ e1 T1, e_typ e2 T2 => eqb' e1 e2 && eqb T1 T2
               | e_ghost e1 g1 e1', e_ghost e2 g2 e2' => eqb' e1 e2 &&
                                                          eqb g1 g2 &&
                                                          eqb' e1' e2'
               | e_if e0 e1 e2, e_if e0' e1' e2' => eqb' e0 e0' &&
                                                     eqb' e1 e1' &&
                                                     eqb' e2 e2'
               | e_eq e1 e2, e_eq e1' e2' => eqb' e1 e1' &&
                                              eqb' e2 e2'
               | e_plus e1 e2, e_plus e1' e2' => eqb' e1 e1' &&
                                                  eqb' e2 e2'
               | e_minus e1 e2, e_minus e1' e2' => eqb' e1 e1' &&
                                                    eqb' e2 e2'
               | e_lt e1 e2, e_lt e1' e2' => eqb' e1 e1' &&
                                              eqb' e2 e2'
               | _, _ => false
               end
    }.
  Solve Obligations of eqbExp with crush.
  Next Obligation.
    induction a;
      try solve [apply Nat.eqb_refl];
      try solve [destruct v;
                 try solve [apply Nat.eqb_refl]];
      try solve [
          match goal with
          | [v : ?T |- _] =>
              rewrite <- (eqb_refl v);
              destruct v;
              auto
          end
        ];
    try (repeat (match goal with
                 | [IHa : ?f1 ?a ?a = true |- _] =>
                     rewrite IHa;
                     simpl;
                     clear IHa
                 end; simpl);
         auto);
      try solve[simpl;
                match goal with
                | [_ : exp,
                      f : ?T |- _] =>
                    rewrite <- (eqb_refl f)
                end;
                simpl;
                auto];
    auto.
    destruct t;
      auto;
      rewrite <- (eqb_refl c);
      simpl;
      auto.

    rewrite <- (eqb_refl g);
      destruct g;
      simpl;
      auto.
    rewrite Nat.eqb_refl;
      auto.
  Defined.
  Next Obligation.
    generalize a2; clear a2.
    induction a1;
      intros a2;
      destruct a2;
      auto;
      try (repeat (match goal with
                   | [IHa : forall a2, ?f1 ?a1 a2 = ?f a2 ?a1 |- _] =>
                       rewrite IHa;
                       simpl;
                       clear IHa
                   end; simpl);
           auto);

      try solve [match goal with
                 | [v1 : ?T,
                       v2 : ?T |- _] =>
                     assert (Hsym : eqb v1 v2 = eqb v2 v1);
                     [apply eqb_sym|simpl in Hsym; auto; rewrite Hsym; auto]
                 end
        ].
  Defined.
  Next Obligation.
    generalize H; clear H.
    generalize a2; clear a2.
    induction a1;
      intros;
      destruct a2;
      try solve [crush];
      try solve [
          match goal with
          | [x : ?T, y : ?T |- _ ] =>
              rewrite (eqb_eq x y);
              auto
          end
        ];
      try (
          repeat match goal with
            | [H : _ && _ = true |- _] =>
                apply andb_true_iff in H;
                destruct H
            end
        );
      try (rewrite (IHa1_1 a2_1);
           auto;
           rewrite (IHa1_2 a2_2);
           auto).

    rewrite (eqb_eq f f0);
      auto.
    rewrite (IHa1 a2);
      auto.

    rewrite (eqb_eq t t0);
      auto.
    rewrite (IHa1 a2);
      auto.

    rewrite (eqb_eq g g0);
      auto.

    rewrite (IHa1_3 a2_3);
      auto.
  Defined.
  Next Obligation.
    generalize H;
      generalize a2;
      clear H; clear a2.
    induction a1;
      intros;
      destruct a2;
      try solve [crush];
      try (intro Hcontra;
           inversion Hcontra;
           subst);

      try (repeat match goal with
             | [H : _ && _ = false |- _ ] =>
                 apply andb_false_iff in H;
                 destruct H
             end;

           [specialize (IHa1_1 a2_1);
            apply IHa1_1 in H;
            crush|
             specialize (IHa1_2 a2_2);
             apply IHa1_2 in H;
             crush]).

    apply Nat.eqb_neq in H.
    crush.

    assert (Heqb : eqb v0 v0 = true);
      [apply eqb_refl| simpl in Heqb; rewrite Heqb in H];
      crush.

    assert (Heqb : eqb v0 v0 = true);
      [apply eqb_refl| simpl in Heqb; rewrite Heqb in H];
      crush.

    repeat match goal with
           | [H : _ && _ = false |- _ ] =>
               apply andb_false_iff in H;
               destruct H
           end.
    specialize (IHa1 a2);
      apply IHa1 in H.
    crush.

    destruct f0; rewrite Nat.eqb_refl in H; crush.

    repeat match goal with
           | [H : _ && _ = false |- _ ] =>
               apply andb_false_iff in H;
               destruct H
           end.
    specialize (IHa1 a2);
      apply IHa1 in H.
    crush.

    destruct t0; crush.
    destruct c; rewrite Nat.eqb_refl in H; crush.

    repeat match goal with
           | [H : _ && _ = false |- _ ] =>
               apply andb_false_iff in H;
               destruct H
           end.
    specialize (IHa1_1 a2_1);
      apply IHa1_1 in H;
      crush.
    destruct g0; rewrite Nat.eqb_refl in H; crush.
    specialize (IHa1_2 a2_2);
      apply IHa1_2 in H;
      crush.

    repeat match goal with
           | [H : _ && _ = false |- _ ] =>
               apply andb_false_iff in H;
               destruct H
           end.
    specialize (IHa1_1 a2_1);
      apply IHa1_1 in H;
      crush.
    specialize (IHa1_2 a2_2);
      apply IHa1_2 in H;
      crush.
    specialize (IHa1_3 a2_3);
      apply IHa1_3 in H;
      crush.
  Defined.

  (** * Assertion Syntax - Section 4*)

  Inductive asrt :=
  | a_exp : exp -> asrt

  | a_and : asrt -> asrt -> asrt
  | a_neg : asrt -> asrt
  | a_all : cls -> asrt -> asrt

  | a_extl : exp -> asrt

  | a_prt : exp -> asrt
  | a_prt_frm : exp -> exp -> asrt.

  Notation "'a_' e" := (a_exp e)(at level 38).
  Notation "A1 '∧' A2" := (a_and A1 A2)(at level 39).
  Notation "'¬' A" := (a_neg A)(at level 38).
  Definition a_or A1 A2 := ¬ (¬ A1 ∧ ¬ A2).
  Notation "A1 '∨' A2" := (a_or A1 A2)(at level 39).
  Definition arr A1 A2 := ¬ A1 ∨ A2.
  Notation "A1 ⟶ A2" :=(arr A1 A2)(at level 40).
  Notation "'a_true'" := (a_ (e_true))(at level 37).
  Notation "'a_false'" := (a_ (e_false))(at level 37).
  Notation "e1 ≠ e2" := (¬ a_ (e_eq e1 e2))(at level 37).

  #[global] Program Instance eqbAsrt : Eq asrt :=
    {
      eqb := fix eqb' a1 a2 :=
          match a1, a2 with
          | a_exp e1, a_exp e2 => eqb e1 e2
          | a_and A11 A12, a_and A21 A22 => eqb' A11 A21 && eqb' A12 A22
          | a_neg A1, a_neg A2 => eqb' A1 A2
          | a_all C1 A1, a_all C2 A2 => eqb C1 C2 && eqb' A1 A2
          | a_extl e1, a_extl e2 => eqb e1 e2
          | a_prt e1, a_prt e2 => eqb e1 e2
          | a_prt_frm e11 e12, a_prt_frm e21 e22 => eqb e11 e21 && eqb e12 e22
          | _, _ => false
          end
    }.
  Solve Obligations of eqbAsrt with crush.
  Next Obligation.
    induction a; crush;
    try solve [assert (Heq : eqb e e = true);
               [apply eqb_refl|simpl in Heq; auto]].

    destruct c; rewrite Nat.eqb_refl; auto.

    assert (Heq : eqb e e = true);
      [apply eqb_refl|simpl in Heq; rewrite Heq].

    assert (Heq0 : eqb e0 e0 = true);
      [apply eqb_refl|simpl in Heq0; crush].
  Defined.

  Next Obligation.
    generalize a2; clear a2.
    induction a1;
      intros a2;
      destruct a2;
      try solve [crush];

    try solve [assert (Hsym : eqb e e0 = eqb e0 e);
               [apply eqb_sym|simpl in Hsym; crush]].


    assert (Hsym : eqb c c0 = eqb c0 c);
      [apply eqb_sym|simpl in Hsym; rewrite Hsym].
    specialize (IHa1 a2).
    rewrite IHa1.
    auto.

    assert (HsymA : eqb e e1 = eqb e1 e);
      [apply eqb_sym|simpl in HsymA; rewrite HsymA].

    assert (HsymB : eqb e0 e2 = eqb e2 e0);
      [apply eqb_sym|simpl in HsymB; crush].
  Defined.

  Next Obligation.
    generalize H; clear H.
    generalize a2; clear a2.
    induction a1;
      intros;
      destruct a2;
      try solve [crush];
      try solve [
          match goal with
          | [x : ?T, y : ?T |- _ ] =>
              rewrite (eqb_eq x y);
              auto
          end
        ];
      try (
          repeat match goal with
            | [H : _ && _ = true |- _] =>
                apply andb_true_iff in H;
                destruct H
            end
        );
      try (rewrite (IHa1_1 a2_1);
           auto;
           rewrite (IHa1_2 a2_2);
           auto);
      try (rewrite (IHa1 a2); auto).

    rewrite (eqb_eq c c0); auto.

    rewrite (eqb_eq e e1), (eqb_eq e0 e2); auto.

  Defined.

  Next Obligation.
    generalize H;
      generalize a2;
      clear H; clear a2.
    induction a1;
      intros;
      destruct a2;
      try solve [crush];
      try (intro Hcontra;
           inversion Hcontra;
           subst);

      try (repeat match goal with
             | [H : _ && _ = false |- _ ] =>
                 apply andb_false_iff in H;
                 destruct H
             end;

           [specialize (IHa1_1 a2_1);
            apply IHa1_1 in H;
            crush|
             specialize (IHa1_2 a2_2);
             apply IHa1_2 in H;
             crush]);

      try solve [assert (Heqb : eqb e0 e0 = true);
                 [apply eqb_refl| simpl in Heqb; rewrite Heqb in H];
                 crush].

    specialize (IHa1 a2).
    contradiction IHa1;
      auto.

    repeat match goal with
           | [H : _ && _ = false |- _ ] =>
               apply andb_false_iff in H;
               destruct H
           end.

    assert (Heqb : eqb c0 c0 = true);
      [apply eqb_refl| simpl in Heqb; rewrite Heqb in H];
      crush.

    specialize (IHa1 a2).
    contradiction IHa1;
      auto.

    assert (HeqbA : eqb e1 e1 = true);
      [apply eqb_refl| simpl in HeqbA; rewrite HeqbA in H];
      crush.

    assert (HeqbB : eqb e2 e2 = true);
      [apply eqb_refl| simpl in HeqbB; rewrite HeqbB in H];
      crush.
  Defined.

  Inductive path :=
  | p_fld : fld -> path
  | p_cons : fld -> path -> path.

  (** * Core Language Definitions **)

  Inductive l_spec :=
  | S_inv : list (var * ty) -> asrt -> l_spec
  | S_mth : cls -> mth -> list (var * ty) -> asrt -> asrt -> asrt -> l_spec
  | S_and : l_spec -> l_spec -> l_spec.

  Inductive visibility : Type :=
  | public
  | private.

  Record methDef := meth{
                        spec : list (asrt * asrt * asrt);
                        vis : visibility;
                        params : list (var * ty);
                        body : stmt;
                        rtrn : ty
                      }.

  Record classDef :=
    clazz{
        c_name : cls;
        c_fields : partial_map fld ty;
        c_ghosts : partial_map ghost (var * exp);
        c_meths : partial_map mth methDef
      }.

  Definition module := (l_spec * (partial_map cls classDef)) %type.

  Record object := obj{o_cls : cls;
                        o_flds : partial_map fld val}.

  Definition heap := partial_map addr object.

  Record frame := frm{local : partial_map var (val * ty);
                       continuation : stmt}.

  Inductive stack :=
    | stack_cons : frame -> list frame -> stack.

  Notation "ϕ '⋅' ψ" := (stack_cons ϕ ψ)(at level 41).

  Definition config := (stack * heap) % type.

  Definition top (σ : config) :=
    match σ with
    | (stack_cons ϕ ψ, _) => ϕ
    end.

  Definition interpret_x (σ : config)(x : var) : option val :=
    match σ with
    | (frm lcl c ⋅ ψ, _) => bind (lcl x) (fun x => Some (fst x))
    end.

  Definition interpret_αf (σ : config)(α : addr)(f : fld) : option val :=
    match σ with
    | (ϕ ⋅ ψ, χ) =>
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

  Definition ghostLookup (M : module)(σ : config)(α : addr)(g : ghost) : option (var * exp) :=
    match snd σ α with
    | Some o => match snd M (o_cls o) with
               | Some CDef => c_ghosts CDef g
               | None => None
               end
    | None => None
    end.

  Definition classOf (σ : config)(x : var): option cls :=
    match interpret_x σ x with
    | Some (v_addr l) =>
        match snd σ l with
        | Some o => Some (o_cls o)
        | _ => None
        end
    | _ => None
    end.

  Definition typeOf_v (σ : config)(v : val)(t : ty) :=
    match v, t with
    | v_null, _ => True
    | v_int _, t_int => True
    | v_bool _, t_bool => True
    | v_str _, t_str => True
    | v_addr α, t_cls C => match snd σ α with
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

  Definition typeOf_f (M : module) C f :=
    bind (snd M C) (fun def => (c_fields def) f).

End LanguageDefinition.
