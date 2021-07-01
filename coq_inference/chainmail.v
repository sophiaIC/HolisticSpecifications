Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import List.
Require Export Coq.Lists.ListSet.

Module Chainmail(L : LanguageDef).

  Import L.
  Module L_Semantics := AbstractOperationalSemantics(L).
  Export L_Semantics.

  Declare Scope chainmail_scope.

  Open Scope reduce_scope.

  Inductive a_val : Type :=
  | av_hole : nat -> a_val
  | av_bnd  : value -> a_val.

  Notation "'a♢' n" := (av_hole n)(at level 25) : chainmail_scope.
  Open Scope chainmail_scope.
  Notation "'av_' v" := (av_bnd v)(at level 25) : chainmail_scope.
  Notation "'v_' α" := (v_addr α)(at level 25) : chainmail_scope.
  Notation "'a_' α" := (av_bnd (v_ α))(at level 25) : chainmail_scope.

  Program Instance eq_a_val : Eq a_val :=
    {
    eqb x y := match x, y with
               | av_hole n, av_hole m => n =? m
               | av_bnd α1, av_bnd α2 => eqb α1 α2
               | _, _ => false
               end
    }.
  Next Obligation.
    split;
      intros;
      intro Hcontra;
      andDestruct;
      crush.
  Defined.
  Next Obligation.
    split;
      intros;
      intro Hcontra;
      andDestruct;
      crush.
  Defined.
  Next Obligation.
    destruct a.
    apply Nat.eqb_refl.
    destruct v;
      auto;
      [|apply Z.eqb_refl].
    destruct a;
      apply Nat.eqb_refl.
  Defined.
  Next Obligation.
    destruct a1, a2;
      try solve [rewrite Nat.eqb_sym;
                 auto];
      auto.
    destruct v, v0;
      auto;
      try solve [rewrite Z.eqb_sym;
                 auto].
    destruct a, a0.
    rewrite Nat.eqb_sym;
      auto.
  Defined.
  Next Obligation.
    destruct a1, a2;
      try match goal with
          | [H : (_ =? _) = true |- _] =>
            apply Nat.eqb_eq in H;
              subst
          end;
      auto;
      try solve [crush].
    destruct v, v0;
      try solve [simpl_crush];
      auto.
    destruct a, a0;
      try match goal with
          | [H : (_ =? _) = true |- _] =>
            apply Nat.eqb_eq in H;
              subst
          end;
      auto.
    apply Z.eqb_eq in H;
      subst;
      auto.
  Defined.
  Next Obligation.
    destruct a1, a2;
      try match goal with
          | [H : (_ =? _) = false |- _] =>
            apply Nat.eqb_neq in H;
              subst
          end;
      auto;
      try solve [simpl_crush];
      try solve [crush].
    intro Hcontra;
      inversion Hcontra;
      subst.
    destruct v0;
      crush.
    - destruct a.
      apply Nat.eqb_neq in H.
      crush.
    - apply Z.eqb_neq in H;
        crush.
  Defined.
  Next Obligation.
    destruct a1, a2;
      try match goal with
          | [H : (_ =? _) = false |- _] =>
            apply Nat.eqb_neq in H;
              subst
          end;
      auto.
    - apply <- Nat.eqb_neq.
      crush.

    - destruct v, v0;
        auto;
        try solve [apply Z.eqb_neq;
                   crush];
        try solve [crush].
      destruct a, a0.
      apply Nat.eqb_neq;
        crush.
  Defined.
  Next Obligation.
    destruct a1, a2;
      [|right; crush|right; crush|].
    - destruct (eq_dec n n0);
        subst;
        auto;
        right;
        crush.
    - destruct (eq_dec v v0);
        subst;
        auto;
        right;
        crush.
  Defined.

  Inductive a_mth : Type :=
  | am_hole : nat -> a_mth
  | am_bnd : mth -> a_mth.

  Notation "'am_' m" := (am_bnd m)(at level 40) : chainmail_scope.
  Notation "'am♢' m" := (am_hole m)(at level 40) : chainmail_scope.

  (** Assertion syntax  *)

  Inductive asrt : Type :=
  (** Simple: *)
  | a_exp : exp -> asrt
  | a_class : exp -> cls -> asrt

  (** Connectives: *)
  | a_arr   : asrt -> asrt -> asrt
  | a_and   : asrt -> asrt -> asrt
  | a_or    : asrt -> asrt -> asrt
  | a_neg   : asrt -> asrt

  (** Quantifiers: *)
  | a_all : asrt -> asrt
  | a_ex  : asrt -> asrt

  (** Permission: *)
  | a_acc   : a_val -> a_val -> asrt

  (** Control: *)
  | a_call  : a_val -> a_val -> mth -> partial_map name a_val  -> asrt

  (** Viewpoint: *)
  | a_extrn : a_val -> asrt
  | a_intrn : a_val -> asrt.

  Notation "A1 '⟶' A2" := (a_arr A1 A2)(at level 30) : chainmail_scope.
  Notation "A1 '∧' A2" :=(a_and A1 A2)(at level 28) : chainmail_scope.
  Notation "A1 '∨' A2" :=(a_or A1 A2)(at level 29) : chainmail_scope.
  Notation "'¬' A" :=(a_neg A)(at level 27) : chainmail_scope.
  Notation "'∀x.[' A ']'" :=(a_all A)(at level 31) : chainmail_scope.
  Notation "'∃x.[' A ']'" :=(a_ex A)(at level 31) : chainmail_scope.
  Notation "x 'internal'" :=(a_intrn x)(at level 26) : chainmail_scope.
  Notation "x 'external'" :=(a_extrn x)(at level 26) : chainmail_scope.
  Notation "x 'access' y" :=(a_acc x y)(at level 26) : chainmail_scope.
  Notation "x 'calls' y '◌' m '⟨' vMap '⟩'" :=(a_call x y m vMap)(at level 26) : chainmail_scope.

  Reserved Notation "M1 '⦂' M2 '◎' σ '⊨' A"(at level 40).
  Reserved Notation "M1 '⦂' M2 '◎' σ '⊭' A"(at level 40).

  Instance a_valSubst : Subst a_val nat value :=
    {
    sbst x n v :=
      match x with
      | av_hole m => if (beq_nat n m)
                    then av_bnd v
                    else x
      | _ => x
      end
    }.

  Instance optionSubst{A : Type}`{Subst A nat value} : Subst (option A) nat value :=
    {
    sbst o n v := match o with
                  | Some a => Some ([v /s n] a)
                  | None => None
                  end
    }.

  Instance vMap : Subst (partial_map name a_val) nat value :=
    {
    sbst β n v :=
      fun x => [v /s n] (β x)
    }.

  Instance asrtSubst : Subst asrt nat value :=
    {
    sbst :=
      fix sbst' A n v :=
        match A with
        | a_exp e     => a_exp ([ v /s n ] e)
        | a_class x C => a_class ([ v /s n ] x) C
        | A1 ∧ A2     => (sbst' A1 n v) ∧ (sbst' A2 n v)
        | A1 ∨ A2     => (sbst' A1 n v) ∨ (sbst' A2 n v)
        | ¬ A         => ¬ (sbst' A n v)
        | A1 ⟶ A2   => (sbst' A1 n v) ⟶ (sbst' A2 n v)

        | ∀x.[ A ]    => ∀x.[(sbst' A (S n) v)]
        | ∃x.[ A ]    => ∃x.[ (sbst' A (S n) v)]

        | x access y  => ([ v /s n] x) access ([ v /s n ] y)
        | x calls y ◌  m ⟨ vMap ⟩ => ([ v /s n ] x) calls ([ v /s n ] y) ◌ m ⟨ [v /s n] vMap ⟩

        | x external => ([ v /s n ] x) external
        | x internal => ([ v /s n ] x) internal
        end
    }.

  Inductive exp_satisfaction : mdl -> mdl -> config -> exp -> Prop :=
  | exp_sat : forall M1 M2 M σ e, M1 ⋄ M2 ≜ M ->
                             M ∙ σ ⊢ e ↪ v_true ->
                             exp_satisfaction M1 M2 σ e.

  Inductive has_class : mdl -> mdl -> config -> exp -> cls -> Prop :=
  | has_cls : forall M1 M2 M e α o χ ψ, M1 ⋄ M2 ≜ M ->
                                   M ∙ (χ, ψ) ⊢ e ↪ (v_ α) ->
                                   ⟦ α ↦ o ⟧_∈ χ ->
                                   has_class M1 M2 (χ, ψ) e (cname o).

  Inductive has_access : config -> a_val -> a_val -> Prop :=
  | acc_self : forall σ α, has_access σ (a_ α) (a_ α)
  | acc_fld : forall χ ψ α1 o f α2, ⟦ α1 ↦ o ⟧_∈ χ ->
                               ⟦ f ↦ (v_ α2) ⟧_∈ o.(flds) ->
                               has_access (χ, ψ) (a_ α1) (a_ α2)
  | acc_lcl : forall χ ψ x α1 α2, (exists ϕ, In ϕ ψ /\
                                   ϕ.(this) = α1 /\
                                   ⟦ x ↦ v_ α2 ⟧_∈ ϕ.(local)) ->
                             has_access (χ, ψ) (a_ α1) (a_ α2).

  Inductive makes_call : config -> a_val -> a_val -> mth -> partial_map name a_val ->
                         Prop :=
  | method_call : forall χ lcl b ψ x y m args α1 α2,
      ⟦ y ↦ (v_ α2) ⟧_∈ lcl ->
      makes_call (χ, frm α1 lcl (c_ call x y m args ;; b) :: ψ)
                 (a_ α1)
                 (a_ α2)
                 m
                 ((fun v => Some (av_ v)) ∘ (lcl ∘ args)).

  Inductive internal_obj : mdl -> config -> a_val -> Prop :=
  | is_int : forall M χ ψ α o, ⟦ α ↦ o ⟧_∈ χ ->
                          (cname o) ∈ M ->
                          internal_obj M (χ, ψ) (a_ α).

  Inductive external_obj : mdl -> config -> a_val -> Prop :=
  | is_ext : forall M χ ψ α o, ⟦ α ↦ o ⟧_∈ χ ->
                          (cname o) ∉ M ->
                          external_obj M (χ, ψ) (a_ α).

  Hint Constructors exp_satisfaction : chainmail_db.
  Hint Constructors has_class : chainmail_db.
  Hint Constructors has_access : chainmail_db.
  Hint Constructors makes_call : chainmail_db.
  Hint Constructors internal_obj : chainmail_db.
  Hint Constructors external_obj : chainmail_db.

  Inductive sat : mdl -> mdl -> config -> asrt -> Prop :=

  (** Simple: *)

  | sat_exp   : forall M1 M2 σ e,  exp_satisfaction M1 M2 σ e ->
                              M1 ⦂ M2 ◎ σ ⊨ (a_exp e)
  (**
[[[
                     M1 ⋄ M2 ≜ M 
                 M ∙ σ ⊢ e' ↪ v_true
               -----------------------                   (Sat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ e
]]]
   *)

  | sat_class : forall M1 M2 σ e C, has_class M1 M2 σ e C ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_class e C)
  (**
[[[
              (α ↦ o) ∈ σ     o has class C
               ----------------------------                   (Sat-Class)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (α : C)
]]]
   *)

  (** Connectives: *)
  | sat_and   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊨ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊨ (A1 ∧ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-And)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)
]]]
   *)

  | sat_or1   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
               ----------------------------                   (Sat-Or1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
   *)

  | sat_or2   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊨ (A1 ∨ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Or2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
   *)

  | sat_arr1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                                 M1 ⦂ M2 ◎ σ ⊨ (A1 ⟶ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Arr1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
   *)

  | sat_arr2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                 M1 ⦂ M2 ◎ σ ⊨ (A1 ⟶ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               ----------------------------                   (Sat-Arr2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
   *)

  | sat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                             M1 ⦂ M2 ◎ σ ⊨ (¬ A)
  (**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊭ A
               -----------------------                   (Sat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ ¬ A
]]]
   *)

  (** Quantifiers: *)

  | sat_all : forall M1 M2 σ A, (forall x, M1 ⦂ M2 ◎ σ ⊨ ([x /s 0]A)) ->
                           M1 ⦂ M2 ◎ σ ⊨ (∀x.[ A ])
  (**
[[[
                (∀ α o, (α ↦ o) ∈ σ.(heap) → M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               ------------------------------------------------------------                   (Sat-All-x)
                            M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀ x. A)
]]]
   *)

  | sat_ex  : forall M1 M2 σ x A, M1 ⦂ M2 ◎ σ ⊨ ([x /s 0] A) ->
                             M1 ⦂ M2 ◎ σ ⊨ (∃x.[ A ])
  (**
[[[
                     (α ↦ o) ∈ σ.(heap)
                M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               -------------------------------                   (Sat-Ex-x)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃ x. A)
  ]]]
   *)

  (** Permission: *)
  | sat_access : forall M1 M2 σ a1 a2, has_access σ a1 a2 ->
                                  M1 ⦂ M2 ◎ σ ⊨ (a1 access a2)

  (**
[[[

               ------------------------------                   (Sat-Access1)
                M1 ⦂ M2 ◎ σ0 … σ ⊨ α access α
]]]
   *)

  (*| sat_access2 : forall M1 M2 σ0 σ α α' o f, mapp σ α' = Some o ->
                                       (flds o) f = Some (v_addr α) ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α') access (a_ α))
(**
[[[
                 (α' ↦ o) ∈ σ     o.f = α
               ------------------------------                   (Sat-Access2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α' access α
]]]
   *)

| sat_access3 : forall M1 M2 σ0 σ ψ ϕ χ x α1 α2 s, ⌊this⌋ σ ≜ (v_addr α1) ->
                                              ⌊x⌋ σ ≜ (v_addr α2) ->
                                              σ = (χ, ϕ :: ψ) ->
                                              (contn ϕ) = c_stmt s ->
                                              in_stmt x s ->
                                              M1 ⦂ M2 ◎ σ0 … σ ⊨ ((a_ α1) access (a_ α2))
   (**
[[[
                     ⌊this⌋ σ ≜ α1
               ⌊x⌋ σ ≜ α2        x ∈ σ.(contn)
               -------------------------------                   (Sat-Access3)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α1 access α2
]]]
   *)*)

  (** Control: *)
  | sat_call : forall M1 M2 σ a1 a2 m β, makes_call σ a1 a2 m β ->
                                    M1 ⦂ M2 ◎ σ ⊨ (a1 calls a2 ◌ m ⟨ β ⟩)
  (**
[[[
                               ⌊this⌋ σ ≜ α1        
               ⌊y⌋ σ ≜ α2        σ.(contn) = (x := y.m(β); s)
               ------------------------------------------------                   (Sat-Call-1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α1 calls α2.m(β ∘ σ.(vMap))
]]]
   *)

  (*| sat_call_2 : forall M1 M2 σ0 σ χ ϕ ψ x y m β s α1 α2,
    ⌊ this ⌋ σ ≜ (v_addr α1) ->
    ⌊ y ⌋ σ ≜ (v_addr α2) ->
    σ = (χ, ϕ :: ψ) ->
    (contn ϕ) = (c_stmt (s_stmts (s_meth x y m β) s)) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_call' (a_ α1) (a_ α2) (am_ m))
 (**
[[[
                               ⌊this⌋ σ ≜ α1        
               ⌊y⌋ σ ≜ α2        σ.(contn) = (x := y.m(β); s)
               ------------------------------------------------                   (Sat-Call-2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ α1 calls α2.m(β ∘ σ.(vMap))
]]]
   *)
   *)
  (** Viewpoint: *)
  | sat_extrn : forall M1 M2 σ a, external_obj M1 σ a ->
                             M1 ⦂ M2 ◎ σ ⊨ (a external)
  (**
[[[
               (α ↦ o) ∈ χ   o.(className) ∉ M1
               ---------------------------------                   (Sat-Extrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α external
]]]
   *)

  | sat_intrn : forall M1 M2 σ a, internal_obj M1 σ a ->
                             M1 ⦂ M2 ◎ σ ⊨ (a internal)
  (**
[[[
               (α ↦ o) ∈ χ   o.(className) ∈ M1
               ---------------------------------                   (Sat-Intrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α internal
]]]
   *)

  where "M1 '⦂' M2 '◎' σ '⊨' A" := (sat M1 M2 σ A) : chainmail_scope

  with
    nsat : mdl -> mdl -> config -> asrt -> Prop :=

  (*simple*)
  | nsat_exp : forall M1 M2 σ e, ~ exp_satisfaction M1 M2 σ e ->
                               M1 ⦂ M2 ◎ σ ⊭ (a_exp e)
  (**
[[[
                   M1 ⋄ M2 ≜ M
               M ∙ σ ⊢ e ↪ v_false
               --------------------                   (NSat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ e
]]]
   *)

  | nsat_class : forall M1 M2 σ e C, ~ has_class M1 M2 σ e C ->
                                M1 ⦂ M2 ◎ σ ⊭ (a_class e C)
  (**
[[[
                        (α ↦ o) ∈ σ     
               o has class C'      C' ≠ C
               --------------------------                   (NSat-Class1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ (α : C)
]]]
   *)

  (*connectives*)
  | nsat_and1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                  M1 ⦂ M2 ◎ σ ⊭ (A1 ∧ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               --------------------------                   (NSat-And1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
   *)

  | nsat_and2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                  M1 ⦂ M2 ◎ σ ⊭ (A1 ∧ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-And2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
   *)

  | nsat_or    : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                  M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                  M1 ⦂ M2 ◎ σ ⊭ (A1 ∨ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Or)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∨ A2
]]]
   *)

  | nsat_arr   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                                  M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                  M1 ⦂ M2 ◎ σ ⊭ (A1 ⟶ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Arr)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ⇒ A2
]]]
   *)

  | nsat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                              M1 ⦂ M2 ◎ σ ⊭ (¬ A)
  (**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊨ A
               ----------------------                   (NSat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ ¬ A
]]]
   *)

  (*quantifiers*)
  | nsat_all : forall M1 M2 σ A x, M1 ⦂ M2 ◎ σ ⊭ ([x /s 0]A) ->
                              M1 ⦂ M2 ◎ σ ⊭ (∀x.[ A ]) 
  (**
[[[
                      (α ↦ o) ∈ σ.(heap)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               ----------------------------                   (NSat-All-x)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ ∀ x. A
]]]
   *)

  | nsat_ex : forall M1 M2 σ A, (forall x, M1 ⦂ M2 ◎ σ ⊭ ([x /s 0]A)) ->
                           M1 ⦂ M2 ◎ σ ⊭ (∃x.[ A ])
  (**
[[[
               ∀ α o. (α ↦ o) ∈ σ.(heap) → M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               --------------------------------------------------------                   (NSat-Ex-x)
                         M1 ⦂ M2 ◎ σ0 … σ ⊭ ∃ x. A
]]]
   *)

  (** Permission: *)
  | nsat_access : forall M1 M2 σ a1 a2, ~ has_access σ a1 a2 ->
                                   M1 ⦂ M2 ◎ σ ⊭ (a1 access a2)
  (**
[[[
                α1 ≠ α2        (∀ o f α3. (α1 ↦ o) ∈ σ ∧ o.f = α3 → α2 ≠ α3)
                    (∀ x. ⌊x⌋ σ ≜ α2 ∧ ⌊this⌋ ≜ α1 → x ∉ σ.(contn))
               ---------------------------------------------------------------                   (NSat-Access)
                       M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 access α2
]]]
   *)

  (** Control: *)
  | nsat_call : forall M1 M2 σ a1 a2 m β, ~ makes_call σ a1 a2 m β ->
                                     M1 ⦂ M2 ◎ σ ⊭ (a1 calls a2 ◌ m ⟨ β ⟩)
  (**
[[[
                    ⌊this⌋ σ ≜ α          α ≠ α1
               ------------------------------------------                   (NSat-Call1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 calls α2 ▸ m ⟨ β ⟩
]]]
   *)

  | nsat_extrn : forall M1 M2 σ a, ~ external_obj M1 σ a ->
                              M1 ⦂ M2 ◎ σ ⊭ a_extrn a
  (**
[[[
                       α ∉ σ.(heap)
               -----------------------------                   (NSat-Extrn1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α external
]]]
   *)

  | nsat_intrn : forall M1 M2 σ a, ~ internal_obj M1 σ a ->
                              M1 ⦂ M2 ◎ σ ⊭ (a internal)
  (**
[[[
                       α ∉ σ.(heap)
               -----------------------------                   (NSat-Intrn1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α internal
]]]
   *)

  (*space*)
  (*| nsat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                 M1 ⦂ M2 ◎ σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_in A (s_bind Σ))*)

  (*time*)

  where "M1 '⦂' M2 '◎' σ '⊭' A" := (nsat M1 M2 σ A) : chainmail_scope.


  Scheme sat_mut_ind := Induction for sat Sort Prop
    with nsat_mut_ind := Induction for nsat Sort Prop.

  Combined Scheme sat_mutind from sat_mut_ind, nsat_mut_ind.

  Hint Constructors sat nsat : chainmail_db.

  Definition mdl_sat (M : mdl)(A : asrt) :=
    forall M' σ0 σ, (exists M'', M ⋄ M' ≜ M'') ->
               initial σ0 ->
               M ⦂ M' ⦿ σ0 ⤳⋆ σ ->
               M ⦂ M' ◎ σ ⊨ A.

  Notation "M '⊨m' A" := (mdl_sat M A)(at level 40) : chainmail_scope.

  Definition arising (M1 M2 : mdl)(σ : config) :=
    exists σ0, initial σ0 /\ M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ.

  Inductive entails : mdl -> asrt -> asrt -> Prop :=
  | ent : forall M A1 A2, (forall σ M', arising M M' σ ->
                              M ⦂ M' ◎ σ ⊨ A1 ->
                              M ⦂ M' ◎ σ ⊨ A2) ->
                     entails M A1 A2.

  Hint Constructors entails : chainmail_db.

  Notation "M '⊢' A1 '⊇' A2" := (entails M A1 A2)(at level 40).

  Definition equiv_a (M : mdl)(A1 A2 : asrt): Prop :=
    (entails M A1 A2) /\ (entails M A2 A1).

  Notation "M '⊢' A1 '≡' A2" := (equiv_a M A1 A2)(at level 40).


  Class Raiseable (A : Type) :=
    {
    raise : A -> nat -> A
    }.

  Notation "a '↑' n" := (raise a n)(at level 40) : chainmail_scope.

  Instance raiseNat : Raiseable nat :=
    {
    raise n m := if leb m n
                 then (S n)
                 else n
    }.
  Instance raiseAVar : Raiseable a_val :=
    {
    raise x n := match x with
                 | av_hole m => av_hole (m ↑ n)
                 | _ => x
                 end
    }.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.

End Chainmail.
