Require Export Arith.
Require Import List.
Require Import Bool.

Require Import common.
Require Import language_def.
Require Import subst.
Require Export operational_semantics.
Require Import assert_theory.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

(** * Hoare Logic *)

Module Hoare.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import SubstDefn.
  Import AssertTheory.

  Declare Scope hoare_scope.

  (** ** Helper Functions *)

  Fixpoint zip {A B : Type} (l1 : list A)(l2 : list B) : option (list (A * B)) :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => match zip t1 t2 with
                         | Some l => Some ((h1, h2) :: l)
                         | None => None
                         end
    | nil, nil => Some nil
    | _, _ => None
    end.

  Inductive has_m_spec : module -> asrt -> cls -> mth ->
                         list (var * ty) -> ty -> asrt -> asrt -> Prop :=
  | mspec : forall M P C ps Q A m mDef CDef pSubst
              pre post inv ret,
      snd M C = Some CDef ->
      c_meths CDef m = Some mDef ->
      map snd ps = map snd (params mDef) ->
      zip (map (fun xC => e_var (fst xC)) ps)
        (map fst (params mDef)) = Some pSubst ->
      In (P, Q, A) (spec mDef) ->
      pre = listSubst P pSubst ->
      ret = rtrn mDef ->
      post = listSubst Q pSubst ->
      inv = listSubst A pSubst ->
      has_m_spec M pre C m ps ret post inv.

  Inductive has_l_spec : module -> l_spec -> Prop :=
  | lspec_base : forall S Cdefs, has_l_spec (S, Cdefs) S
  | lspec_and1 : forall S S1 S2 Cdefs, has_l_spec (S1, Cdefs) S ->
                                  has_l_spec (S_and S1 S2, Cdefs) S
  | lspec_and2 : forall S S1 S2 Cdefs, has_l_spec (S2, Cdefs) S ->
                                  has_l_spec (S_and S1 S2, Cdefs) S.

  Definition asrt_frm_list {A : Type} (f : A -> asrt)(ys : list A) :=
    fold_left a_and (map f ys) (a_true).


  Definition prt_frms (e : exp)(ys : list var) :=
    asrt_frm_list (a_prt_frm e) (map e_var ys).

  Definition a_typs (xCs : list (var * ty)) :=
    asrt_frm_list (fun eC => a_ (e_typ (e_ (fst eC)) (snd eC))) xCs.

  (** * Adaptation. See Section 6.2.2 in the related paper *)

  Fixpoint adapt (A : asrt)(ys : list var) : asrt :=
    match A with
    | a_prt e => prt_frms e ys
    | a_prt_frm e x => a_prt_frm e x
    | a_extl e => a_extl e
    | a_ e => a_ e
    | A1 ∧ A2 => (adapt A1 ys) ∧ (adapt A2 ys)
    | a_all C A => a_all C (adapt A ys)
    | ¬ A => ¬ (adapt A ys)
    end.

  (** * Stability. See Section 4.3.1 in the related paper *)

  Fixpoint Stbl (A : asrt) :=
    match A with
    | a_prt x => False
    | A1 ∧ A2 => Stbl A1 /\ Stbl A2
    | a_all C A => Stbl A
    | ¬ A => Stbl A
    | _ => True
    end.

  (** Stbl_plus is defined here, but not used in the proofs of satisfaction*)

  Fixpoint Stbl_plus (A : asrt) :=
    match A with
    | A1 ∧ A2 => Stbl_plus A1 /\ Stbl_plus A2
    | a_all C A => Stbl_plus A
    | ¬ A => Stbl_neg A
    | _ => True
    end

  with Stbl_neg (A : asrt) :=
         match A with
         | a_prt x => False
         | A1 ∧ A2 => Stbl_neg A1 /\ Stbl_neg A2
         | a_all C A => Stbl_neg A
         | ¬ A => Stbl_plus A
         | _ => True
         end.

  Inductive lift : list var -> asrt -> asrt -> Prop :=
  | lift_exp : forall e ys, lift ys (a_ e) (a_ e)
  | lift_prt : forall x ys A, (forall M y, In y ys ->
                                  M ⊢ A ⊆ (a_prt_frm (e_ x) (e_ y))) ->
                          lift ys A (a_prt (e_ x)).

  Fixpoint call_free s :=
    match s with
    | s_call _ _ _ _ => False
    | s1 ;; s2 => call_free s1 /\ call_free s2
    | _ => True
    end.

  Fixpoint prt_free A :=
    match A with
    | a_prt_frm x y => False
    | a_prt x => False
    | A1 ∧ A2 => prt_free A1 /\ prt_free A2
    | a_all C A => prt_free A
    | ¬ A => prt_free A
    | _ => True
    end.

  (** * Hoare Triples - Section 6.1 *)

  Class HoareTriple (A : Type) := triple : module -> asrt -> A -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

  (** Assumed definitiong for the the underlying hoare logic. *)

  Parameter hoare_base : HoareTriple stmt.

  Parameter hoare_base_stbl :
    forall M P s Q, hoare_base M P s Q ->
               Stbl P /\ Stbl Q /\ call_free s /\ prt_free P /\ prt_free Q.

  Fixpoint exp_not_in e x :=
    match e with
    | e_ y => x <> y
    | e_typ e0 _ => exp_not_in e0 x
    | e_fld e0 _ => exp_not_in e0 x
    | e_ghost e0 _ e1 => exp_not_in e0 x /\ exp_not_in e1 x
    | e_if e0 e1 e2 => exp_not_in e0 x /\ exp_not_in e1 x /\ exp_not_in e2 x
    | e_eq e1 e2 => exp_not_in e1 x /\ exp_not_in e2 x
    | e_plus e1 e2 => exp_not_in e1 x /\ exp_not_in e2 x
    | e_minus e1 e2 => exp_not_in e1 x /\ exp_not_in e2 x
    | e_lt e1 e2 => exp_not_in e1 x /\ exp_not_in e2 x
    | _ => True
    end.

  Fixpoint does_not_assign_to_var s x :=
    match s with
    | s_read y _ => x <> y
    | s1 ;; s2 => does_not_assign_to_var s1 x /\
                   does_not_assign_to_var s2 x
    | s_call y _ _ _ => x <> y
    | s_if _ s1 s2 => does_not_assign_to_var s1 x /\
                       does_not_assign_to_var s2 x
    | s_hole y => x <> y
    | s_new y _ => x <> y
    | _  => True
    end.

  Fixpoint simple_exp e :=
    match e with
    | e_if _ _ _ => False
    | e_ghost _ _ _ => False
    | e_eq e1 e2 => simple_exp e1 /\ simple_exp e2
    | e_fld e' _ => simple_exp e'
    | e_typ e' _ => simple_exp e'
    | e_plus e1 e2 => simple_exp e1 /\ simple_exp e2
    | e_minus e1 e2 => simple_exp e1 /\ simple_exp e2
    | e_lt e1 e2 => simple_exp e1 /\ simple_exp e2
    | _ => True
    end.

  Inductive hoare_extension : HoareTriple stmt :=

  (** 
      Note: there is no explicit use of Stbl P, Stbl Q, prt_free, or call_free s in h_base because
      it is implicitly handled by the hoare_base_stbl assumption.
   *)

  (** M ⊢_base ⦃ P ⦄ s ⦃ Q ⦄ *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P ⦄ s ⦃ Q ⦄  *)

  | h_embed_UL : forall M P s Q,
      hoare_base M P s Q ->
      M ⊢ ⦃ P ⦄ s ⦃ Q ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ true ⦄ x := new C ⦃ ⟪ x ⟫ ⦄ *)

  | h_prot_new : forall M x C,
      M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄

  (** M ⊢ ⦃ P1 ⦄ s ⦃ Q ⦄ *)
  (** M ⊢ P2 ⊆ P1 *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P2 ⦄ s ⦃ Q ⦄  *)

  | h_strengthen : forall M s P1 P2 Q,
      M ⊢ ⦃ P1 ⦄ s ⦃ Q ⦄ ->
      M ⊢ P2 ⊆ P1 ->
      M ⊢ ⦃ P2 ⦄ s ⦃ Q ⦄

  (** M ⊢ ⦃ P ⦄ s ⦃ Q1 ⦄ *)
  (** M ⊢ Q1 ⊆ Q2 *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P ⦄ s ⦃ Q2 ⦄  *)

  | h_weaken : forall M s P Q1 Q2,
      M ⊢ ⦃ P ⦄ s ⦃ Q1 ⦄ ->
      M ⊢ Q1 ⊆  Q2 ->
      M ⊢ ⦃ P ⦄ s ⦃ Q2 ⦄

  (** M ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ *)
  (** M ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ *)
  (** ----------------- *)
  (** M ⊢ ⦃ P1 ∧ P2 ⦄ s ⦃ Q1 ∧ Q2 ⦄  *)

  | h_and : forall M P1 P2 s Q1 Q2,
      M ⊢ ⦃ P1 ⦄ s ⦃ Q1 ⦄ ->
      M ⊢ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
      M ⊢ ⦃ P1 ∧ P2 ⦄ s ⦃ Q1 ∧ Q2 ⦄

  (** M ⊢ ⦃ P ∧ e ⦄ s1 ⦃ Q ⦄ *)
  (** M ⊢ ⦃ P ∧ ¬ e ⦄ s2 ⦃ Q ⦄ *)
  (** ----------------- *)
  (** M ⊢ ⦃ P ⦄ if e then s1 else s2 ⦃ Q ⦄  *)

  | h_if : forall M e s1 s2 P Q,
      M ⊢ ⦃ P ∧ a_ e ⦄ s1 ⦃ Q ⦄ ->
      M ⊢ ⦃ P ∧ ¬ a_ e ⦄ s2 ⦃ Q ⦄ ->
      M ⊢ ⦃ P ⦄ s_if e s1 s2 ⦃ Q ⦄


  (** call_free s *)
  (** ∀ z, s does not assign to z → M ⊢ ⦃ A ∧ e = z ⦄ s ⦃ e = z ⦄ *)
  (** -----------------------------*)
  (** M ⊢ ⦃ A ∧ prt e ⦄ y := z.f ⦃ prt e ⦄ *)

  | h_prot1 : forall M e s A,
      call_free s ->
      (forall z, does_not_assign_to_var s z ->
            M ⊢ ⦃ (A ∧ a_ (e_eq e (e_ z))) ⦄ s ⦃ (a_ (e_eq e (e_ z))) ⦄) ->
      M ⊢ ⦃ A ∧ a_prt e ⦄ s ⦃ a_prt e ⦄


  (**  *)
  (** -----------------------------*)
  (** M ⊢ ⦃ prt x ⦄ y := z.f ⦃ prt x ⦄ *)

  | h_prot2 : forall M x e e' s,
      (forall z z', z <> x -> z' <> x ->
               M ⊢ ⦃ a_ ((e_ z) ⩵ e) ∧ a_ ((e_ z') ⩵ e') ⦄
                 s
                 ⦃ a_ ((e_ z) ⩵ e) ∧ a_ ((e_ z') ⩵ e') ⦄) ->
      M ⊢ ⦃ a_prt_frm e e' ⦄ s ⦃ a_prt_frm e e' ⦄

  | h_prot3 : forall M x z y f,
      x <> z ->
      M ⊢ ⦃ a_prt_frm (e_fld (e_ y) f) (e_ z) ⦄
        s_read x (e_fld (e_ y)  f)
        ⦃ a_prt_frm (e_ x) (e_ z) ⦄

  | h_prot4 : forall M x y y' f z,
      M ⊢ ⦃ a_prt_frm (e_ x) (e_ z) ∧ a_prt_frm (e_ x) (e_ y') ⦄
        (s_write y f (e_ y'))
        ⦃ a_prt_frm (e_ x) (e_ z) ⦄

  | h_seq : forall M A1 A2 A3 s1 s2,
      M ⊢ ⦃ A1 ⦄ s1 ⦃ A2 ⦄ ->
      M ⊢ ⦃ A2 ⦄ s2 ⦃ A3 ⦄ ->
      M ⊢ ⦃ A1 ⦄ s1 ;; s2 ⦃ A3 ⦄

  | h_read_type : forall M e T x,
      M ⊢ ⦃ a_ (e_typ e T) ⦄
        (s_read x e)
        ⦃ a_ (e_typ (e_ x) T) ⦄

  | h_types1 : forall M e T s,
      M ⊢ ⦃ a_ (e_typ e T) ⦄
        s
        ⦃ a_ (e_typ e T) ⦄

  | h_or : forall M A1 A2 A3 s, M ⊢ ⦃ A1 ⦄ s ⦃ A3 ⦄ ->
                           M ⊢ ⦃ A2 ⦄ s ⦃ A3 ⦄ ->
                           M ⊢ ⦃ A1 ∨ A2 ⦄ s ⦃ A3 ⦄.

  #[global] Instance hoare_triple_stmt : HoareTriple stmt :=
    {
      triple := hoare_extension
    }.

  (** * Hoare Quadruples *)

  Class HoareQuadruple A := quad : module -> asrt -> A -> asrt -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄' '||' '⦃' A '⦄'" :=
    (quad M P s Q A) (at level 40, s at level 59).

  Inductive hoare_quad : HoareQuadruple stmt :=
  | hq_mid : forall M A1 s A2 A,
      M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ ->
      M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄

  | hq_types2 : forall M s e T A,
      M ⊢ ⦃ a_ (e_typ e T) ⦄ s ⦃ a_ (e_typ e T) ⦄ || ⦃ A ⦄

  | hq_combine : forall M A1 s A2 A3 A4 A,
      M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄ ->
      M ⊢ ⦃ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
      M ⊢ ⦃ A1 ∧ A3 ⦄ s ⦃ A2 ∧ A4 ⦄ || ⦃ A ⦄

  | hq_sequ : forall M A1 A2 A3 A s1 s2,
      M ⊢ ⦃ A1 ⦄ s1 ⦃ A2 ⦄ || ⦃ A ⦄ ->
      M ⊢ ⦃ A2 ⦄ s2 ⦃ A3 ⦄ || ⦃ A ⦄ ->
      M ⊢ ⦃ A1 ⦄ s1 ;; s2 ⦃ A3 ⦄ || ⦃ A ⦄

  | hq_if : forall M A1 A2 A3 e s1 s2,
      M ⊢ ⦃ (a_ e) ∧ A1 ⦄ s1 ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
      M ⊢ ⦃ ¬ (a_ e) ∧ A1 ⦄ s2 ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
      M ⊢ ⦃ A1 ⦄ s_if e s1 s2 ⦃ A2 ⦄ || ⦃ A3 ⦄

  | hq_conseq : forall M s A1 A2 A3 A4 A5 A6,
      M ⊢ ⦃ A4 ⦄ s ⦃ A5 ⦄ || ⦃ A6 ⦄ ->
      M ⊢ A1 ⊆ A4 ->
      M ⊢ A5 ⊆ A2 ->
      M ⊢ A3 ⊆ A6 ->
      M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄

  | hq_call_int : forall M A1 C m ys T A2 A3 y0 u xs xCs yCs yxs,
      has_m_spec M A1 C m xCs T A2 A3 ->
      xs = map fst xCs ->
      zip ys (map snd xCs) = Some yCs ->
      zip (map e_var ys) xs = Some yxs ->
      M ⊢ ⦃ (a_typs ((result, T)::(y0, t_cls C)::xCs)) ∧
              [e_ y0 /s this](listSubst A1 yxs) ⦄
        s_call u y0 m ys
        ⦃ [e_ u /s result][e_ y0 /s this] (listSubst A2 yxs) ⦄ || ⦃ A3 ⦄

  | hq_call_int_adapt : forall M A1 C m ys T A2 A3 y0 u xs xCs yCs yxs,
      has_m_spec M A1 C m xCs T A2 A3 ->
      xs = map fst xCs ->
      zip ys (map snd xCs) = Some yCs ->
      zip (map e_var ys) xs = Some yxs ->
      M ⊢ ⦃ (a_typs ((result, T)::(y0, t_cls C)::xCs)) ∧
              adapt ([e_ y0 /s this](listSubst A1 yxs)) (y0 :: ys) ⦄
        s_call u y0 m ys
        ⦃ adapt ([e_ u /s result][e_ y0 /s this] (listSubst A2 yxs)) (y0 :: ys) ⦄ || ⦃ A3 ⦄

  | hq_call_ext_adapt : forall M xCs A u y0 m ys,
      has_l_spec M (S_inv xCs A) ->
      M ⊢
        ⦃ a_extl (e_ y0) ∧
            a_typs xCs ∧
            (adapt A (y0::ys)) ⦄
        s_call u y0 m ys
        ⦃ (adapt A (y0::ys)) ⦄ || ⦃ A ⦄

  | hq_call_ext_adapt_strong : forall M xCs A u y0 m ys,
      has_l_spec M (S_inv xCs A) ->
      M ⊢
        ⦃ a_extl (e_ y0) ∧
            a_typs xCs ∧
            A ∧
            (adapt A (y0::ys)) ⦄
        s_call u y0 m ys
        ⦃ A ∧ (adapt A (y0::ys)) ⦄ || ⦃ A ⦄.

  #[global] Instance hoare_quadruple_stmt : HoareQuadruple stmt :=
    {
      quad := hoare_quad
    }.

    Ltac induction_hoare :=
    match goal with
    | [ |- forall M P s Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> _ ] =>
        intros M P s Q Hhoare; induction Hhoare
    | [ |- forall M P s Q A, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ || ⦃ A ⦄ -> _ ] =>
        intros M P s Q A Hhoare; induction Hhoare
    end.

    #[export] Hint Constructors hoare_quad : hoare_db.

  Close Scope hoare_scope.

End Hoare.
