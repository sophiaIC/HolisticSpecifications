Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert.
Require Export operational_semantics.
Require Import assert_theory.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Hoare.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.

  Declare Scope hoare_scope.
  Open Scope assert_scope.

  (*Question: replace entails with a general assertion satisfaction form?
   i.e. something like M ⊢ A instead of M ⊢ A1 ⊆ A2
   I don't know what that would give us. Are there non-consequence assertions
   that we want to prove are always satisfied?
   *)

  (** Helper Functions *)

  Fixpoint zip {A B : Type} (l1 : list A)(l2 : list B) : option (list (A * B)) :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => match zip t1 t2 with
                         | Some l => Some ((h1, h2) :: l)
                         | None => None
                         end
    | nil, nil => Some nil
    | _, _ => None
    end.

  (*
TODO: Need to discuss below. Clarification. Do the variables in the spec refer to the objects or the variables?
i.e. if we overwrite the variable in the method body, but don't modify the original object, is the overwrite reflected in the post?
   *)

  Inductive has_m_spec : module -> asrt -> cls -> mth ->
                         list (var * ty) -> ty -> asrt -> asrt -> Prop :=
  | mspec : forall M P C ps Q A m mDef CDef pSubst,
      snd M C = Some CDef ->
      c_meths CDef m = Some mDef ->
      map snd ps = map snd (params mDef) ->
      zip (map (fun xC => e_var (fst xC)) ps) (map fst (params mDef)) = Some pSubst ->
      In (P, Q, A) (spec mDef) ->
      has_m_spec
        M (listSubst P pSubst) C m ps (rtrn mDef)
        (listSubst Q pSubst) (listSubst A pSubst).

  Inductive has_l_spec : module -> l_spec -> Prop :=
  | lspec_base : forall S Cdefs, has_l_spec (S, Cdefs) S
  | lspec_and1 : forall S S1 S2 Cdefs, has_l_spec (S1, Cdefs) S ->
                                  has_l_spec (S_and S1 S2, Cdefs) S
  | lspec_and2 : forall S S1 S2 Cdefs, has_l_spec (S2, Cdefs) S ->
                                  has_l_spec (S_and S1 S2, Cdefs) S.

  (** * Hoare Semantics *)
  Inductive reductions : module -> config -> config -> Prop :=
  | r_single : forall M σ1 σ2, reduction M σ1 σ2 ->
                          reductions M σ1 σ2

  | r_trans : forall M σ1 σ2 σ3, reduction M σ1 σ2 ->
                            reductions M σ2 σ3 ->
                            reductions M σ1 σ2.

  Definition final s := s = s_empty.

  (* traditional hoare triple semantics *)
  Definition hoare_triple_semantics (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    forall χ lcl s' ψ χ' lcl',
      reductions M (frm lcl s ⋅ ψ, χ) (frm lcl' s' ⋅ ψ, χ') ->
      final s ->
      sat M (frm lcl s ⋅ ψ, χ) P ->
      sat M (frm lcl' s' ⋅ ψ, χ) Q.

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare_triple_semantics M P s Q)(at level 40).

  Definition hoare_quad_semantics (M : module)(P : asrt)(s : stmt)(Q A : asrt) :=
    forall σ1 σ2, (forall χ ψ ϕ, σ1 = (ϕ ⋅ ψ, χ) -> continuation ϕ = s) ->
             forall αs zs zSubst , zip αs zs = Some zSubst ->
                              sat M σ1 (listSubst P zSubst) ->
                              final (continuation (top σ2)) ->
                              (forall σ, scoped_exec M σ1 σ ->
                                    sat M σ (a_extl(e_ this) ⟶ (listSubst A zSubst))) ->
                              sat M σ2 (listSubst Q zSubst).

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄ || ⦃ A ⦄" := (hoare_quad_semantics M P s Q A)(at level 40).


  (* remove? *)
  Definition push (σ : config)(αs : list addr) : config -> Prop :=
    match σ with
    | (ϕ ⋅ ψ, χ) =>
        fun σ' =>
          match σ' with
          | (ϕ' ⋅ ψ', χ') =>
              ψ' = ϕ :: ψ /\
                χ' = χ /\
                (forall x α T, local ϕ x = Some (v_addr α, T) ->
                          In (α) αs) (* this is weaker than the paper, but I think sufficient*)
          end
    end.

  Definition asrt_frm_list {A : Type} (f : A -> asrt)(ys : list A) :=
    fold_left a_and (map f ys) a_true.


  Definition prt_frms (e : exp)(ys : list var) :=
    asrt_frm_list (a_prt_frm e) (map e_var ys).

  Definition a_typs (xCs : list (var * ty)) :=
    asrt_frm_list (fun eC => a_ (e_typ (e_ (fst eC)) (snd eC))) xCs.

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

  (* Proof Rules *)

  (* Is there a purpose to splitting the internal and external method arguments? *)

  Fixpoint Stbl (A : asrt) :=
    match A with
    | a_prt_frm x y => False
    | a_prt x => False
    | A1 ∧ A2 => Stbl A1 /\ Stbl A2
    | a_all C A => Stbl A
    | ¬ A => Stbl A
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

(*)(*  | lift_eq : forall v v' z ys, lift (a_ v_ v ⩵ v_ v') z ys (a_ v_ v ⩵ v_ v') *)
  | lift_fld : forall x f v z ys, lift (a_ e_ x∙f ⩵ v_ v) z ys (a_ e_ x∙f ⩵ v_ v)
  | lift_prt : forall x z ys, lift (a_prt (e_ x)) z ys (a_prt (e_ x)) (* Discuss: does this make sense? Should we not require that x not be in z or y? *)
  | lift_prt_frm1 : forall A x z ys, (forall M z, In z z -> M ⊢ A ⊆ a_prt_frm (e_ x) (e_ z)) -> (* <- discuss *)
                                 ~ In x ys ->
                                 lift A z ys (a_prt (e_ x))
  | lift_prt_frm2 : forall A x z ys, (exists M z, In z zs -> ~ M ⊢ A ⊆ a_prt_frm (e_ x) (e_ z)) ->
                                 lift A zs ys (a_prt (e_ x))
  | lift_prt_frm3 : forall A x z ys, In x ys ->
                                lift A z ys (a_prt (e_ x))
  | lift_and : forall A1 A2 z ys A1' A2', lift A1 z ys A1' ->
                 lift A2 z ys A2' ->
                 lift (A1 ∧ A2) zs ys (A1' ∧ A2')
  | lift_all : forall A z ys C A', lift A z ys A' ->
                 lift (a_all C A) z ys (a_all C A')
  | lift_ex : forall A z ys C A', lift A z ys A' ->
                lift (a_ex C A) z ys (a_ex C A')
  | lift_neg : forall A z ys A', prt_free A = true ->
                 lift A z ys A' ->
                 lift (¬ A) zs ys (¬ A').*)

  (*Fixpoint lower (A : asrt) : asrt :=
    match A with
    | a_ ((v_ v) ⩵ (v_ v')) => a_ ((v_ v) ⩵ (v_ v'))
    | a_ (e_ x∙f ⩵ v_ v) => a_ (e_ x∙f ⩵ v_ v)
    | a_prt (e_ x) => a_prt (e_ x) (* is this correct? paper says true *)
    | a_prt_frm (e_ x) (e_ y) => a_prt_frm (e_ x) (e_ y)
    | A1 ∧ A2 => lower A1 ∧ lower A2
    | ¬ A => if Stbl A
            then ¬ (lower A)
            else a_true
    | a_all C A => a_all C (lower A)
    | a_ex C A => a_ex C (lower A)
    | _ => a_true
    end.*)

  (** * Hoare Logic *)

(*  Class BaseHoareTriple (A : Type) :=
    prt_free_triple
      (M : module)
      (P : asrt)(s : stmt)(Q : asrt): (Prop * (prt_free P = true /\ prt_free Q = true)).

 *)

  Class HoareTriple (A : Type) := triple : module -> asrt -> A -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

  Parameter hoare_base : HoareTriple stmt.

  Parameter hoare_base_stbl :
    forall M P s Q, hoare_base M P s Q ->
               Stbl P /\ Stbl Q /\ call_free s.

(*  Definition base_hoare_triple (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    fst(hoare_base M P s Q).
*)

  (* Parameter hoare_read : forall M x y f e,
      hoare_base M ([e_ y∙f /s x] (a_ e)) (s_read x y f) (a_ e). *)

  Parameter hoare_base_soundness : forall M P s Q,
      hoare_base M P s Q -> M ⊨ ⦃ P ⦄ s ⦃ Q ⦄.

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
    | _ => True
    end.

  Inductive hoare_extension : HoareTriple stmt :=

    (*
      Note: there is no explicit use of Stbl P, Stbl Q, or call_free s in h_base because
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

  | h_prot_new1 : forall M x C,
      M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄


  (** x ≠ y *)
  (** -----------------------------*)
  (** M ⊢ ⦃ true ⦄ x := new C ⦃ ⟪ x ⟫ <-\- y ⦄ *)

  | h_prot_new2 : forall M x y C,
      x <> y ->
      M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt_frm (e_ x) (e_ y)⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ prt e ⦄ x := new C ⦃ prt e ⦄ *)

  | h_prot_new3 : forall M x C e,
      M ⊢ ⦃ a_prt e ⦄ (s_new x C) ⦃ a_prt e ⦄


  (* add to appendix & fix markup *)
  (** -----------------------------*)
  (** M ⊢ ⦃ true ⦄ x := new C ⦃ prt x ⦄ *)

  | h_new_prt2 : forall M x e1 e2 C,
      exp_not_in e1 x ->
      exp_not_in e2 x ->
      M ⊢ ⦃ a_prt_frm e1 e2 ⦄ (s_new x C) ⦃ a_prt_frm e1 e2 ⦄


  (*

because our HL only considers internal code, and field access is module protected,
we know that any field access we do will not expose anything to external code.
(the above is also true of field writes)

Because of this, we can preserve the usual assignment rule from HL.

   *)

  (*  | h_read_extl : forall M x y f e, M ⊢ ⦃ [e_ y∙f /s x] (a_extl e) ⦄ s_read x y f ⦃ a_extl e ⦄

  | h_read_intl : forall M x y f e, M ⊢ ⦃ [e_ y∙f /s x] (a_intl e) ⦄ s_read x y f ⦃ a_intl e ⦄

  | h_read_prt_frm : forall M x y f z z', M ⊢ ⦃ [e_ y∙f /s x] a_prt_frm (e_ z) (e_ z')⦄
                                       s_read x y f
                                       ⦃ a_prt_frm (e_ z) (e_ z') ⦄

  | h_read_prt : forall M x y f z, M ⊢ ⦃ [e_ y∙f /s x] a_prt z ⦄ s_read x y f ⦃ a_prt z ⦄*)

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
  (** *)
  (** ----------------- *)
  (** M ⊢ ⦃ [y.f / x] P ⦄  ⦃ P ⦄  *)

  | h_read : forall M x y f P,
      M ⊢ ⦃ [e_ y∙f /s x] P ⦄ s_read x (e_fld (e_ y) f) ⦃ P ⦄

  (** M ⊢ ⦃ P ∧ e ⦄ s1 ⦃ Q ⦄ *)
  (** M ⊢ ⦃ P ∧ ¬ e ⦄ s2 ⦃ Q ⦄ *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P ⦄ if e then s1 else s2 ⦃ Q ⦄  *)

  | h_if : forall M e s1 s2 P Q,
      M ⊢ ⦃ P ∧ a_ e ⦄ s1 ⦃ Q ⦄ ->
      M ⊢ ⦃ P ∧ ¬ a_ e ⦄ s2 ⦃ Q ⦄ ->
      M ⊢ ⦃ P ⦄ s_if e s1 s2 ⦃ Q ⦄

  (** -----------------------------*)
  (** M ⊢ ⦃ w prt-frm x ⦄ y := z.f ⦃ w prt-frm x ⦄  *)

  | h_write_prt_frm : forall M w x y z f,
      M ⊢ ⦃ a_prt_frm (e_ w) (e_ x) ∧ a_prt_frm (e_ w) (e_ z) ⦄ s_write y f (e_ z) ⦃ a_prt_frm (e_ w) (e_ x) ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ prt x ⦄ y := z.f ⦃ prt x ⦄ *)

  | h_write_prt : forall M x y f z,
      M ⊢ ⦃ a_prt (e_ x) ⦄ (s_write y f z) ⦃ a_prt (e_ x) ⦄

  | h_seq : forall M A1 A2 A3 s1 s2,
      M ⊢ ⦃ A1 ⦄ s1 ⦃ A2 ⦄ ->
      M ⊢ ⦃ A2 ⦄ s2 ⦃ A3 ⦄ ->
      M ⊢ ⦃ A1 ⦄ s1 ;; s2 ⦃ A3 ⦄

  | h_read_type : forall M e T x, M ⊢ ⦃ a_ (e_typ e T) ⦄ (s_read x e) ⦃ a_ (e_typ (e_ x) T) ⦄

  | h_read_prt1 : forall M e1 x e2, exp_not_in e1 x ->
                               M ⊢ ⦃ a_prt e1 ⦄ (s_read x e2) ⦃ a_prt e1 ⦄

  | h_read_prt2 : forall M e1 x e2 A, M ⊢ A ⊆ a_prt e1  ->
                                 M ⊢ A ⊆ a_prt e2 ->
                                 M ⊢ ⦃ A ⦄ (s_read x e2) ⦃ a_prt e1 ⦄.

  #[global] Instance hoare_triple_stmt : HoareTriple stmt :=
    {
      triple := hoare_extension
    }.

  (*Inductive hoare_stmts : HoareTriple stmts :=
  | h_stmt : forall M s P Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                        M ⊢ ⦃ P ⦄ s_stmt s ⦃ Q ⦄
  | h_seq : forall M s s' P Q R, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
                            M ⊢ ⦃ Q ⦄ s' ⦃ R ⦄ ->
                            M ⊢ ⦃ P ⦄ s_seq s s' ⦃ R ⦄.

  #[export] Hint Constructors hoare_extension : hoare_db.

  #[global] Instance hoare_triple_stmts : HoareTriple stmts :=
    {
      triple := hoare_stmts
    }.*)

  Class HoareQuadruple A := quad : module -> asrt -> A -> asrt -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄' '||' '⦃' A '⦄'" :=
    (quad M P s Q A) (at level 40, s at level 59).

  Inductive hoare_quad : HoareQuadruple stmt :=
  | hq_mid : forall M A1 s A2 A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ ->
                            M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄

  (* I'm pretty sure hq_types2 is derivable from hq_types1, hq_conseq, and hq_mid
     remove?
   *)
  | hq_types2 : forall M s e T A,
      M ⊢ ⦃ a_ (e_typ e T) ⦄ s ⦃ a_ (e_typ e T) ⦄ || ⦃ A ⦄

  (*)| hq_types2 : forall M A1 s A2 A x T,
      M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄ ->
      M ⊢ ⦃ A1 ∧ (a_ (e_typ (e_ x) T)) ⦄ s ⦃ A2 ∧ (a_ (e_typ (e_ x) T)) ⦄ || ⦃ A ⦄*)

  | hq_combine : forall M A1 s A2 A3 A4 A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄ ->
                                      M ⊢ ⦃ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                                      M ⊢ ⦃ A1 ∧ A3 ⦄ s ⦃ A2 ∧ A4 ⦄ || ⦃ A ⦄

  | hq_sequ : forall M A1 A2 A3 A s1 s2, M ⊢ ⦃ A1 ⦄ s1 ⦃ A2 ⦄ || ⦃ A ⦄ ->
                                    M ⊢ ⦃ A2 ⦄ s2 ⦃ A3 ⦄ || ⦃ A ⦄ ->
                                    M ⊢ ⦃ A1 ⦄ s1 ;; s2 ⦃ A3 ⦄ || ⦃ A ⦄

  | hq_if : forall M A1 A2 A3 e s1 s2, M ⊢ ⦃ (a_ e) ∧ A1 ⦄ s1 ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
                                  M ⊢ ⦃ ¬ (a_ e) ∧ A1 ⦄ s2 ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
                                  M ⊢ ⦃ A1 ⦄ s_if e s1 s2 ⦃ A2 ⦄ || ⦃ A3 ⦄

  (*
    I think the invariant portion of the quadruple is in a negative position, not positive.
    weakening the invariant makes the quadruple a stronger proof obligation
    The easy example for this is
    M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄ does not imply that
    M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ true ⦄ is satisfied
    The inverse is true however:
    M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ true ⦄ does imply that
    M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄ is satisfied

    This has not come up yet because our examples so far do not vary the
    invariant at all.
   *)

  | hq_conseq : forall M s A1 A2 A3 A4 A5 A6, M ⊢ ⦃ A4 ⦄ s ⦃ A5 ⦄ || ⦃ A6 ⦄ ->
                                         M ⊢ A1 ⊆ A4 ->
                                         M ⊢ A5 ⊆ A2 ->
                                         M ⊢ A6 ⊆ A3 ->
                                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄

  (* change list subst to be subst of 2 lists, and a proof they are the same length, instead of zip?
     this would allow use of the normal subst notation. Might have to make the proof an implicit
     argument. Does that mean that all substitutions need this proof???? Can we make the subst for
     single variables implicit?
   *)

  (*
    substitute into invariant????
    realistitcally the invariant should not contain arguments to the method calls???
   *)

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
            a_typs (map (fun xC => (fst xC, t_cls (snd xC))) xCs) ∧
            (adapt A (y0::ys)) ⦄
        s_call u y0 m ys
        ⦃ (adapt A (y0::ys)) ⦄ || ⦃ A ⦄

  | hq_call_ext_adapt_strong : forall M xCs A u y0 m ys,
      has_l_spec M (S_inv xCs A) ->
      M ⊢
        ⦃ a_extl (e_ y0) ∧
            a_typs (map (fun xC => (fst xC, t_cls (snd xC))) xCs) ∧
            A ∧
            (adapt A (y0::ys)) ⦄
        s_call u y0 m ys
        ⦃ A ∧ (adapt A (y0::ys)) ⦄ || ⦃ A ⦄.

  #[global] Instance hoare_quadruple_stmt : HoareQuadruple stmt :=
    {
      quad := hoare_quad
    }.

  (*Inductive hoare_quad_stmts : HoareQuadruple stmts :=
  | hq_stmt : forall M A1 s A2 A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A ⦄ ->
                             M ⊢ ⦃ A1 ⦄ s_stmt s ⦃ A2 ⦄ || ⦃ A ⦄
  | hq_seq : forall M A1 s1 A2 s2 A3 A, M ⊢ ⦃ A1 ⦄ s1 ⦃ A2 ⦄ || ⦃ A ⦄ ->
                                   M ⊢ ⦃ A2 ⦄ s2 ⦃ A3 ⦄ || ⦃ A ⦄ ->
                                   M ⊢ ⦃ A1 ⦄ s_seq s1 s2 ⦃ A3 ⦄ || ⦃ A3 ⦄.*)

    Ltac induction_hoare :=
    match goal with
    | [ |- forall M P s Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> _ ] =>
        intros M P s Q Hhoare; induction Hhoare
    | [ |- forall M P s Q A, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ || ⦃ A ⦄ -> _ ] =>
        intros M P s Q A Hhoare; induction Hhoare
    end.

    #[export] Hint Constructors hoare_quad : hoare_db.

  Close Scope assert_scope.
  Close Scope hoare_scope.

End Hoare.
