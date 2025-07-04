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
          | e_hole m  => if Nat.eqb n m
                        then e_val (v_addr α)
                        else e_hole m
          | e_fld e' f => e_fld (sbst' e' n α) f
          | e_typ e' C => e_typ (sbst' e' n α) C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 n α) g (sbst' e1 n α)
          | e_if e0 e1 e2 => e_if (sbst' e0 n α) (sbst' e1 n α) (sbst' e2 n α)
          | e_plus e1 e2 => e_plus (sbst' e1 n α) (sbst' e2 n α)
          | e_minus e1 e2 => e_minus (sbst' e1 n α) (sbst' e2 n α)
          | e_lt e1 e2 => e_lt (sbst' e1 n α) (sbst' e2 n α)
          | _ => e
          end
    }.

  #[global] Instance list_subst {A B C : Type}`{Subst A B C} : Subst (list A) B C :=
    {
      sbst :=
        fix sbst' l b c :=
          match l with
          | nil => nil
          | a :: t => ([c /s b] a) :: (sbst' t b c)
          end
    }.

  #[global] Instance asrtSubst : Subst asrt nat addr:=
    {
      sbst :=
        fix sbst' A n α :=
          match A with
          | a_exp e     => a_exp ([ α /s n ] e)
          | A1 ∧ A2     => (sbst' A1 n α) ∧ (sbst' A2 n α)
          | ¬ A         => ¬ (sbst' A n α)

          | a_all C A  => a_all C (sbst' A (S n) α)

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
          | e_typ e0 C => e_typ (sbst' e0 x e') C
          | e_ghost e0 g e1 => e_ghost (sbst' e0 x e') g (sbst' e1 x e')
          | e_if e0 e1 e2 => e_if (sbst' e0 x e') (sbst' e1 x e') (sbst' e2 x e')
          | e_plus e1 e2 => e_plus (sbst' e1 x e') (sbst' e2 x e')
          | e_minus e1 e2 => e_minus (sbst' e1 x e') (sbst' e2 x e')
          | e_lt e1 e2 => e_lt (sbst' e1 x e') (sbst' e2 x e')
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
          | ¬ A' => ¬ (sbst' A' x e)
          | a_all C A' => a_all C (sbst' A' x e)

          | a_extl e' => a_extl ([e /s x] e')

          | a_prt e' => a_prt ([e /s x] e')
          | a_prt_frm e1 e2 => a_prt_frm ([e /s x] e1) ([e /s x] e2)
          end
    }.



  Fixpoint listSubst {A B C : Type}`{Subst A B C} (a : A)(cb : list (C * B)) : A :=
    match cb with
    | nil => a
    | (c, b) :: t => listSubst ([c /s b] a) t
    end.


End SubstDefn.
