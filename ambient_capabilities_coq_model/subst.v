Require Export Arith.
Require Import List.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module SubstDefn.

  Import LanguageDefinition.

  Class Subst (A B C : Type) : Type :=
    {
      sbst : A -> B -> C -> A
    }.

  Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

  #[global] Instance exp_addr_subst : Subst exp nat addr:=
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

          | a_all C A  => a_all C (sbst' A (S n) α)
          | a_ex C A   => a_ex C (sbst' A (S n) α)

          | a_intl e => a_intl ([α /s n] e)
          | a_extl e => a_extl ([α /s n] e)

          | a_prt_frm e1 e2 => a_prt_frm ([α /s n] e1) ([α /s n] e2)
          | a_prt e => a_prt ([α /s n] e)
          end
    }.

  #[global] Instance exp_subst : Subst exp var exp:=
    {
      sbst :=
        fix sbst' e x e' :=
          match e with
          | e_var y => if eqb x y
                      then e'
                      else e_var y
          | e_fld e0 f => e_fld (sbst' e0 x e') f
          | e_class e0 C => e_class (sbst' e0 x e') C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 x e') g (sbst' e1 x e')
          | e_if e0 e1 e2 => e_if (sbst' e0 x e') (sbst' e1 x e') (sbst' e2 x e')
          | _ => e
          end
    }.

  #[global] Instance asrt_subst : Subst asrt var exp:=
    {
      sbst :=
        fix sbst' A x e :=
          match A with
          | a_exp e' => a_exp ([e /s x] e')

          | A1 ∧ A2 => (sbst' A1 x e) ∧ (sbst' A2 x e)
          | A1 ∨ A2 => (sbst' A1 x e) ∨ (sbst' A2 x e)
          | ¬ A' => ¬ (sbst' A' x e)
          | a_all C A' => a_all C (sbst' A' x e)
          | a_ex C A' => a_ex C (sbst' A' x e)

          | a_intl e' => a_intl ([e /s x] e')
          | a_extl e' => a_extl ([e /s x] e')

          | a_prt e' => a_prt ([e /s x] e')
          | a_prt_frm e1 e2 => a_prt_frm ([e /s x] e1) ([e /s x] e2)
          end
    }.

  (*#[global] Instance exp_acc_subst : Subst exp (var * fld) var :=
    {
      sbst :=
        fix sbst' e acc x :=
          match e with
          | e_fld e0 f0 => match e0, acc with
                          | e_ y, (z, f) => if (eqb y z && eqb f0 f)
                                           then e_ x
                                           else e
                          | _, _ => e_fld (sbst' e0 acc x) f0
                          end
          | e_class e0 C => e_class (sbst' e0 acc x) C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 acc x) g (sbst' e1 acc x)
          | e_if e0 e1 e2 => e_if (sbst' e0 acc x) (sbst' e1 acc x) (sbst' e2 acc x)
          | _ => e
          end
    }.*)

  (*#[global] Instance asrt_acc_subst : Subst asrt (var * fld) var:=
    {
      sbst :=
        fix sbst' A acc x :=
          match A with
          | a_exp e => a_exp ([x /s acc] e)

          | A1 ∧ A2 => (sbst' A1 acc x) ∧ (sbst' A2 acc x)
          | A1 ∨ A2 => (sbst' A1 acc x) ∨ (sbst' A2 acc x)
          | ¬ A' => ¬ (sbst' A' acc x)
          | a_all C A' => a_all C (sbst' A' acc x)
          | a_ex C A' => a_ex C (sbst' A' acc x)

          | a_intl e => a_intl ([x /s acc] e)
          | a_extl e => a_extl ([x /s acc] e)

          | a_prt e => a_prt ([x /s acc] e)
          | a_prt_frm e1 e2 => a_prt_frm ([x /s acc] e1) ([x /s acc] e2)
          end
    }.*)

End SubstDefn.
