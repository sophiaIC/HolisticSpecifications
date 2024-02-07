Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import assert.
Require Export operational_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Hoare.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.

  Inductive big_step : module -> config -> config -> Prop :=
  | bsr_single : forall M σ1 σ2, reduction M σ1 σ2 ->
                            big_step M σ1 σ2

  | bsr_trans : forall M σ1 σ2 σ3, reduction M σ1 σ2 ->
                              big_step M σ2 σ3 ->
                              big_step M σ1 σ2.

  Definition hoare_semantics (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    forall χ lcl s' ψ χ' lcl', big_step M (χ, frm lcl (s_seq s s') ;; nil) (χ', frm lcl' s' ;; nil) ->
                          sat M (χ, frm lcl (s_seq s s') ;; ψ) P ->
                          sat M (χ', frm lcl' s' ;; ψ) Q.

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare_semantics M P s Q)(at level 40).

  Definition entails (M : module)(A1 A2 : asrt) : Prop := forall σ, sat M σ (A2 ⟶ A2).

  Notation "M ⊢ A1 ⊆ A2" := (entails M A1 A2)(at level 40).

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

  #[global] Instance exp_acc_subst : Subst exp (var * fld) var :=
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
    }.

  #[global] Instance asrt_acc_subst : Subst asrt (var * fld) var:=
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
    }.

  Fixpoint zip {A B : Type} (l1 : list A)(l2 : list B) : option (list (A * B)) :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => match zip t1 t2 with
                         | Some l => Some ((h1, h2) :: l)
                         | None => None
                         end
    | nil, nil => Some nil
    | _, _ => None
    end.

  Fixpoint listSubst {A B C : Type}`{Subst A B C} (a : A)(cb : list (C * B)) : A :=
    match cb with
    | nil => a
    | (c, b) :: t => listSubst ([c /s b] a) t
    end.

  (* Proof Rules *)

  Class HoareTriple (A : Type) := triple : module -> asrt -> A -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" := (triple M P s Q) (at level 40, s at level 59).

  (* Is there a purpose to splitting the internal and external method arguments? *)

  Fixpoint prt_free (A : asrt) :=
    match A with
    | a_prt_frm x y => false
    | a_prt x => false
    | A1 ∧ A2 => prt_free A1 && prt_free A2
    | A1 ∨ A2 => prt_free A1 && prt_free A2
    | a_all C A => prt_free A
    | a_ex C A => prt_free A
    | ¬ A => prt_free A
    | _ => true
    end.

  Inductive lift : asrt -> list var -> list var -> asrt -> Prop :=
  | lift_eq : forall v v' zs ys, lift (a_ v_ v ⩵ v_ v') zs ys (a_ v_ v ⩵ v_ v')
  | lift_fld : forall x f v zs ys, lift (a_ e_ x∙f ⩵ v_ v) zs ys (a_ e_ x∙f ⩵ v_ v)
  | lift_prt : forall x zs ys, lift (a_prt (e_ x)) zs ys (a_prt (e_ x)) (* Discuss: does this make sense? Should we not require that x not be in z or y? *)
  | lift_prt_frm1 : forall A x zs ys, (forall M z, In z zs -> M ⊢ A ⊆ a_prt_frm (e_ x) (e_ z)) -> (* <- discuss *)
                                 ~ In x ys ->
                                 lift A zs ys (a_prt (e_ x))
  | lift_prt_frm2 : forall A x zs ys, (exists M z, In z zs -> ~ M ⊢ A ⊆ a_prt_frm (e_ x) (e_ z)) ->
                                 lift A zs ys (a_prt (e_ x))
  | lift_prt_frm3 : forall A x zs ys, In x ys ->
                                 lift A zs ys (a_prt (e_ x))
  | lift_and : forall A1 A2 zs ys A1' A2', lift A1 zs ys A1' ->
                                      lift A2 zs ys A2' ->
                                      lift (A1 ∧ A2) zs ys (A1' ∧ A2')
  | lift_all : forall A zs ys C A', lift A zs ys A' ->
                               lift (a_all C A) zs ys (a_all C A')
  | lift_ex : forall A zs ys C A', lift A zs ys A' ->
                              lift (a_ex C A) zs ys (a_ex C A')
  | lift_neg : forall A zs ys A', prt_free A = true ->
                             lift A zs ys A' ->
                             lift (¬ A) zs ys (¬ A').

  Fixpoint lower (A : asrt) : asrt :=
    match A with
    | a_ ((v_ v) ⩵ (v_ v')) => a_ ((v_ v) ⩵ (v_ v'))
    | a_ (e_ x∙f ⩵ v_ v) => a_ (e_ x∙f ⩵ v_ v)
    | a_prt (e_ x) => a_prt (e_ x) (* is this correct? paper says true *)
    | a_prt_frm (e_ x) (e_ y) => a_prt_frm (e_ x) (e_ y)
    | A1 ∧ A2 => lower A1 ∧ lower A2
    | ¬ A => if prt_free A
            then ¬ (lower A)
            else a_true
    | a_all C A => a_all C (lower A)
    | a_ex C A => a_ex C (lower A)
    | _ => a_true
    end.

  Parameter hoare_base : HoareTriple stmt.

  Parameter hoare_read : forall M x y f e, hoare_base M ([e_ y∙f /s x] (a_ e)) (s_read x y f) (a_ e).

  Inductive hoare_extension : HoareTriple stmt :=
  | h_base : forall M P s Q, hoare_base M P s Q ->
                        M ⊢ ⦃ P ⦄ s ⦃ Q ⦄


  (*

because our HL only considers internal code, and field access is module protected,
we know that any field access we do will not expose anything to external code.
(the above is also true of field writes)

Because of this, we can preserve the usual assignment rule from HL.

   *)

  | h_read : forall M x y f P, M ⊢ ⦃ [e_ y∙f /s x] P ⦄ s_read x y f ⦃ P ⦄

(*  | h_read_extl : forall M x y f e, M ⊢ ⦃ [e_ y∙f /s x] (a_extl e) ⦄ s_read x y f ⦃ a_extl e ⦄

  | h_read_intl : forall M x y f e, M ⊢ ⦃ [e_ y∙f /s x] (a_intl e) ⦄ s_read x y f ⦃ a_intl e ⦄

  | h_read_prt_frm : forall M x y f z z', M ⊢ ⦃ [e_ y∙f /s x] a_prt_frm (e_ z) (e_ z')⦄
                                       s_read x y f
                                       ⦃ a_prt_frm (e_ z) (e_ z') ⦄

  | h_read_prt : forall M x y f z, M ⊢ ⦃ [e_ y∙f /s x] a_prt z ⦄ s_read x y f ⦃ a_prt z ⦄*)

  | h_strengthen : forall M s P1 P2 Q, M ⊢ ⦃ P1 ⦄ s ⦃ Q ⦄ ->
                                  M ⊢ P2 ⊆ P1 ->
                                  M ⊢ ⦃ P2 ⦄ s ⦃ Q ⦄

  | h_weaken : forall M s P Q1 Q2, M ⊢ ⦃ P ⦄ s ⦃ Q1 ⦄ ->
                              M ⊢ Q1 ⊆  Q2 ->
                              M ⊢ ⦃ P ⦄ s ⦃ Q2 ⦄

  | h_if : forall M e s1 s2 P Q, M ⊢ ⦃ P ∧ a_ e ⦄ s1 ⦃ Q ⦄ ->
                            M ⊢ ⦃ P ∧ ¬ a_ e ⦄ s2 ⦃ Q ⦄ ->
                            M ⊢ ⦃ P ⦄ s_if e s1 s2 ⦃ Q ⦄

  | h_call : forall M P x y m ps C CDef mDef pSubst, M ⊢ P ⊆ (a_ e_class (e_ y) C) ->
                                                M C = Some CDef ->
                                                c_meths CDef m = Some mDef ->
                                                zip (map (fun p => e_ (fst p)) (params mDef)) ps = Some pSubst ->
                                                M ⊢ ⦃ P ∧ ([e_ y /s this] (listSubst (pre mDef) pSubst)) ⦄
                                                  (s_call x y m ps)
                                                  ⦃ [e_ x /s result] post mDef ⦄

  | h_new_prt_frm1 : forall M x C y z, M ⊢ ⦃ a_prt_frm y z ⦄ (s_new x C) ⦃ a_prt_frm y z ⦄

  | h_new_prt_frm2 : forall M x C y,  M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt_frm (e_ x) (e_ y) ⦄

  | h_new_prt1 : forall M x C y, M ⊢ ⦃ a_prt y ⦄ (s_new x C) ⦃ a_prt y ⦄

  | h_new_prt2 : forall M x C, M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄.

  Print HoareTriple.
  Print Subst.

  #[global] Instance hoare_triple_stmt : HoareTriple stmt :=
    {
      triple := hoare_extension
    }.

  Inductive hoare_stmts : HoareTriple stmts :=
  | h_stmt : forall M s P Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                        M ⊢ ⦃ P ⦄ s_stmt s ⦃ Q ⦄
  | h_seq : forall M s s' P Q R, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                            M ⊢ ⦃ Q ⦄ s' ⦃ R ⦄ ->
                            M ⊢ ⦃ P ⦄ s_seq s s' ⦃ R ⦄.

  #[global] Instance hoare_triple_stmts : HoareTriple stmts :=
    {
      triple := hoare_stmts
    }.

End Hoare.
