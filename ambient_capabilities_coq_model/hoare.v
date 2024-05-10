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

  (** * Hoare Semantics *)
  Inductive big_step : module -> config -> config -> Prop :=
  | bsr_single : forall M σ1 σ2, reduction M σ1 σ2 ->
                            big_step M σ1 σ2

  | bsr_trans : forall M σ1 σ2 σ3, reduction M σ1 σ2 ->
                              big_step M σ2 σ3 ->
                              big_step M σ1 σ2.

  Definition final (M : module)(σ : config) := forall σ', ~ reduction M σ σ'.

  Definition hoare_semantics (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    forall χ lcl s' ψ χ' lcl',
      big_step M (frm lcl (s_seq s s') ;; ψ, χ) (frm lcl' s' ;; ψ, χ') ->
      sat M (frm lcl (s_seq s s') ;; ψ, χ) P ->
      sat M (frm lcl' s' ;; ψ, χ) Q.

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare_semantics M P s Q)(at level 40).

  Definition push (σ : config)(αs : list addr) : config -> Prop :=
    match σ with
    | (ϕ ;; ψ, χ) => fun σ' =>
                      match σ' with
                      | (ϕ' ;; ψ', χ') =>
                          ψ' = ϕ :: ψ /\
                            χ' = χ /\
                            (forall x α, local ϕ x = Some (v_addr α) ->
                                    In (α) αs) (* this is weaker than the paper, but I think sufficient*)
                      end
    end.

  Fixpoint prt_frms (e : exp)(ys : list var) :=
    match ys with
    | y :: ys' => (a_prt_frm e (e_ y)) ∧ (prt_frms e ys')
    | nil => a_true
    end.

  Fixpoint adapt (A : asrt)(ys : list var) : asrt :=
    match A with
    | a_prt e => prt_frms e ys
    | a_prt_frm e x => a_prt_frm e x
    | a_extl e => a_extl e
    | a_ e => a_ e
    | A1 ∧ A2 => (adapt A1 ys) ∧ (adapt A2 ys)
    | a_all C A => a_all C (adapt A ys)
    | ¬ A => ¬ (adapt A ys)
    | _ => a_true (* partial ......*)
    end.

  Fixpoint zip {A B : Type} (l1 : list A)(l2 : list B) : option (list (A * B)) :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 => match zip t1 t2 with
                         | Some l => Some ((h1, h2) :: l)
                         | None => None
                         end
    | nil, nil => Some nil
    | _, _ => None
    end.

  (* Proof Rules *)

  Class HoareTriple (A : Type) := triple : module -> asrt -> A -> asrt -> Prop.
  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

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

  Inductive lift : list var -> asrt -> asrt -> Prop :=
  | lift_exp : forall e ys, lift ys (a_ e) (a_ e)
  | lift_prt : forall x ys A, (forall M y, In y ys ->
                                  M ⊢ A ⊆ (a_prt_frm (e_ x) (e_ y))) ->
                          lift ys A (a_prt (e_ x)).

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

  (** * Hoare Logic *)

(*  Class BaseHoareTriple (A : Type) :=
    prt_free_triple
      (M : module)
      (P : asrt)(s : stmt)(Q : asrt): (Prop * (prt_free P = true /\ prt_free Q = true)).

 *)

  Notation "M '⊢' '⦃' P '⦄' s '⦃' Q '⦄'" :=
    (triple M P s Q) (at level 40, s at level 59).

  Parameter hoare_base : HoareTriple stmt.

  Parameter hoare_base_prt_free :
    forall M P s Q, hoare_base M P s Q ->
               prt_free P = true /\ prt_free Q = true.

(*  Definition base_hoare_triple (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    fst(hoare_base M P s Q).
*)

  (* Parameter hoare_read : forall M x y f e,
      hoare_base M ([e_ y∙f /s x] (a_ e)) (s_read x y f) (a_ e). *)

  Parameter hoare_base_soundness : forall M P s Q,
      hoare_base M P s Q -> M ⊨ ⦃ P ⦄ s ⦃ Q ⦄.

  Inductive hoare_extension : HoareTriple stmt :=

  (** M ⊢_base ⦃ P ⦄ s ⦃ Q ⦄ *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P ⦄ s ⦃ Q ⦄  *)

  | h_base : forall M P s Q,
      hoare_base M P s Q ->
      M ⊢ ⦃ P ⦄ s ⦃ Q ⦄


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
      M ⊢ ⦃ [e_ y∙f /s x] P ⦄ s_read x y f ⦃ P ⦄

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
      M ⊢ ⦃ a_prt_frm (e_ w) (e_ x) ⦄ s_write y f z ⦃ a_prt_frm (e_ w) (e_ x) ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ prt x ⦄ y := z.f ⦃ prt x ⦄ *)

  | h_write_prt : forall M x y f z,
      M ⊢ ⦃ a_prt (e_ x) ⦄ (s_write y f z) ⦃ a_prt (e_ x) ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ e1 prt-frm e2 ⦄ x := new C ⦃ e1 prt-frm e2 ⦄ *)

  | h_new_prt_frm1 : forall M x C e1 e2,
      M ⊢ ⦃ a_prt_frm e1 e2 ⦄ (s_new x C) ⦃ a_prt_frm e1 e2 ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ true ⦄ x := new C ⦃ e1 prt-frm e2 ⦄ *)

  | h_new_prt_frm2 : forall M x C e,
      M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt_frm (e_ x) e ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ prt e ⦄ x := new C ⦃ prt e ⦄ *)

  | h_new_prt1 : forall M x C e,
      M ⊢ ⦃ a_prt e ⦄ (s_new x C) ⦃ a_prt e ⦄


  (** -----------------------------*)
  (** M ⊢ ⦃ true ⦄ x := new C ⦃ prt x ⦄ *)

  | h_new_prt2 : forall M x C,
      M ⊢ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄

  (** M ⊢ P ⟶ y : C *)
  (** C ∈ M *)
  (** C.m.pre = P *)
  (** C.m.post = Q *)
  (** -----------------------------*)
  (** M ⊢ ⦃ [y / this][args / ys] P ⦄ x := y.m(args) ⦃ [y / this][args / ys] Q ⦄ *)

  | h_int_call : forall M P x y m ps C CDef mDef pre post pSubst,
      M ⊢ P ⊆ (a_ e_class (e_ y) C) ->
      snd M C = Some CDef ->
      c_meths CDef m = Some mDef ->
      zip (map (fun p => e_ (fst p)) (params mDef)) ps = Some pSubst ->
      In (pre, post) (spec mDef) ->
      M ⊢ ⦃ P ∧ ([e_ y /s this] (listSubst pre pSubst)) ⦄
        (s_call x y m ps)
        ⦃ [e_ x /s result] [e_ y /s this] (listSubst post pSubst) ⦄

  (** M ⊢ P ⟶ extl y *)
  (** lift (y,ys) p = A1 *)
  (** lower A2 = Q *)
  (** -----------------------------*)
  (** M ⊢ ⦃ P ⦄ x := y.m(args) ⦃ Q ⦄*)

  (*| h_ext_call : forall M P x y m zs Q xCs A1 A2,
      M ⊢ P ⊆ (a_extl (e_ y)) ->
      lift (y::zs) P A1 ->
      lower A2 = Q ->
      defined_spec M (S_inv xCs A1 A2) ->
      M ⊢ ⦃ P ⦄ (s_call x y m zs) ⦃ Q ⦄*).

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

  #[export] Hint Constructors hoare_extension : hoare_db.

  #[global] Instance hoare_triple_stmts : HoareTriple stmts :=
    {
      triple := hoare_stmts
    }.

  Ltac induction_hoare :=
    match goal with
    | [ |- forall M P s Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ -> _ ] =>
        intros M P s Q Hhoare; induction Hhoare
    end.

  Lemma strengthening_sound :
    forall M s P1 P2 Q,
      M ⊨ ⦃ P1 ⦄ s ⦃ Q ⦄ ->
      M ⊢ P2 ⊆ P1 ->
      M ⊨ ⦃ P2 ⦄ s ⦃ Q ⦄.
  Proof.
    unfold hoare_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    apply H.
    apply entails_strengthening with (A1:=P2); auto.
  Qed.

  Lemma weakening_sound :
    forall M s P Q1 Q2,
      M ⊨ ⦃ P ⦄ s ⦃ Q1 ⦄ ->
      M ⊢ Q1 ⊆ Q2 ->
      M ⊨ ⦃ P ⦄ s ⦃ Q2 ⦄.
  Proof.
    unfold hoare_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    apply entails_strengthening with (A1:=Q1); auto.
  Qed.

  Lemma h_and_sound :
    forall M P1 P2 s Q1 Q2,
      M ⊨ ⦃ P1 ⦄ s ⦃ Q1 ⦄ ->
      M ⊨ ⦃ P2 ⦄ s ⦃ Q2 ⦄ ->
      M ⊨ ⦃ P1 ∧ P2 ⦄ s ⦃ Q1 ∧ Q2 ⦄.
  Proof.
    unfold hoare_semantics in *; intros.
    specialize (H χ lcl s' ψ χ' lcl' H1).
    specialize (H0 χ lcl s' ψ χ' lcl' H1).
    inversion H2; subst; eauto with assert_db.
  Qed.

  Lemma read_sound :
    forall M P x y f,
      M ⊨ ⦃ [e_ y ∙ f /s x] P ⦄ s_read x y f ⦃ P ⦄.
  Proof.
    intros.
    unfold hoare_semantics.
    intros.

    inversion H; subst.

    * 
  Admitted.

  Lemma if_sound :
    forall M e s1 s2 P Q,
      M ⊨ ⦃ P ∧ a_ e ⦄ s1 ⦃ Q ⦄ ->
      M ⊨ ⦃ P ∧ ¬ a_ e ⦄ s2 ⦃ Q ⦄ ->
      M ⊨ ⦃ P ⦄ s_if e s1 s2 ⦃ Q ⦄.
  Proof.
  Admitted.

  Lemma write_prt_frm_sound :
    forall M w x y z f,
      M ⊨ ⦃ a_prt_frm (e_ w) (e_ x) ⦄
        s_write y f z
        ⦃ a_prt_frm (e_ w) (e_ x) ⦄.
  Proof.
  Admitted.

  Lemma write_prt_sound :
    forall M x y f z,
      M ⊨ ⦃ a_prt (e_ x) ⦄
        (s_write y f z)
        ⦃ a_prt (e_ x) ⦄.
  Proof.
  Admitted.

  Lemma new_prt_frm1_sound :
    forall M x C e1 e2,
      M ⊨ ⦃ a_prt_frm e1 e2 ⦄
        (s_new x C)
        ⦃ a_prt_frm e1 e2 ⦄.
  Proof.
  Admitted.

  Lemma new_prt_frm2_sound :
    forall M x C e,
      M ⊨ ⦃ a_true ⦄
        (s_new x C)
        ⦃ a_prt_frm (e_ x) e ⦄.
  Proof.
  Admitted.


  Lemma new_prt1_sound :
    forall M x C e,
      M ⊨ ⦃ a_prt e ⦄ (s_new x C) ⦃ a_prt e ⦄.
  Proof.
  Admitted.

  Lemma new_prt2_sound :
    forall M x C,
      M ⊨ ⦃ a_true ⦄ (s_new x C) ⦃ a_prt (e_ x) ⦄.
  Proof.
  Admitted.

  #[export]
    Hint Resolve
    strengthening_sound weakening_sound h_and_sound read_sound if_sound write_prt_frm_sound write_prt_sound new_prt1_sound new_prt2_sound new_prt_frm1_sound new_prt_frm2_sound : hoare_db.

  Theorem hoare_extension_sound :
    forall M P s Q, M ⊢ ⦃ P ⦄ s ⦃ Q ⦄ ->
               M ⊨ ⦃ P ⦄ s ⦃ Q ⦄.
  Proof.
    induction_hoare; eauto with hoare_db.

    * (* hoare base *)
      apply hoare_base_soundness; auto.

    * (* internal call *)
      admit.

    * (* external call *)
      admit.

  Admitted.


  Close Scope assert_scope.
  Close Scope hoare_scope.

End Hoare.
