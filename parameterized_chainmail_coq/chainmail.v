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
  Import L_Semantics.

  Declare Scope chainmail_scope.

  Open Scope reduce_scope.

  Inductive a_type : Type :=
  | a_Obj : a_type
  | a_Bool : a_type
  | a_Int  : a_type
  | a_Val  : a_type
  | a_Mth  : a_type
  | a_Set  : a_type.

  Inductive a_val : Type :=
  | av_hole : nat -> a_val
  | av_bnd  : value -> a_val.

  Notation "'a♢' n" := (av_hole n)(at level 40) : chainmail_scope.
  Open Scope chainmail_scope.
  Notation "'av_' v" := (av_bnd v)(at level 40) : chainmail_scope.
  Notation "'v_' α" := (v_addr α)(at level 39) : chainmail_scope.
  Notation "'a_' α" := (av_bnd (v_ α))(at level 40) : chainmail_scope.

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
  | a_class : a_val -> cls -> asrt
  | a_elem   : exp -> a_set -> asrt

  (** Connectives: *)
  | a_arr   : asrt -> asrt -> asrt
  | a_and   : asrt -> asrt -> asrt
  | a_or    : asrt -> asrt -> asrt
  | a_neg   : asrt -> asrt

  (** Quantifiers: *)
  | a_all : a_type -> asrt -> asrt
  | a_ex  : a_type -> asrt -> asrt

  (** Permission: *)
  | a_acc   : a_val -> a_val -> asrt

  (** Control: *)
  | a_call  : a_val -> a_val -> a_mth -> partial_map name a_val  -> asrt

  (** Time: *)
  | a_next  : asrt -> asrt
  | a_will  : asrt -> asrt
  | a_prev  : asrt -> asrt
  | a_was   : asrt -> asrt

  (** Space: *)
  | a_in    : asrt -> a_set -> asrt

  (** Viewpoint: *)
  | a_extrn : a_val -> asrt
  | a_intrn : a_val -> asrt
  (*)| a_private : a_val -> a_val -> asrt*)

  | a_self : a_val -> asrt

  with
    a_set :=
  | as_hole : nat -> a_set
  | as_bnd  : set a_val -> a_set
  | as_asrt : asrt -> a_set.

  Scheme asrt_mut_ind := Induction for asrt Sort Prop
    with a_set_mut_ind := Induction for a_set Sort Prop.

  Combined Scheme asrt_mutind from asrt_mut_ind, a_set_mut_ind.

  Notation "A1 '⟶' A2" := (a_arr A1 A2)(at level 40) : chainmail_scope.
  Notation "A1 '∧' A2" :=(a_and A1 A2)(at level 40) : chainmail_scope.
  Notation "A1 '∨' A2" :=(a_or A1 A2)(at level 40) : chainmail_scope.
  Notation "'¬' A" :=(a_neg A)(at level 40) : chainmail_scope.
  Notation "'∀[x⦂' T ']∙' A" :=(a_all T A)(at level 40) : chainmail_scope.
  Notation "'∃[x⦂' T ']∙' A" :=(a_ex T A)(at level 40) : chainmail_scope.
  Notation "'⦃x⃒' A '⦄'" := (as_asrt A)(at level 40) : chainmail_scope.
  Notation "e '∈' Σ" := (a_elem e Σ)(at level 40) : chainmail_scope.
  Notation "A 'in_' Σ" := (a_in A Σ)(at level 40) : chainmail_scope.
  Notation "x 'internal'" :=(a_intrn x)(at level 40) : chainmail_scope.
  Notation "x 'external'" :=(a_extrn x)(at level 40) : chainmail_scope.
  Notation "x 'access' y" :=(a_acc x y)(at level 40) : chainmail_scope.
  Notation "x 'calls' y '◌' m '⟨' vMap '⟩'" :=(a_call x y m vMap)(at level 40) : chainmail_scope.

  Inductive a_var : Type :=
  | ax_val : value -> a_var
  | ax_mth : mth -> a_var
  | ax_set : set a_val -> a_var.

  Instance substAVal : Subst a_val nat a_var :=
    {
    sbst x n y :=
      match x with
      | av_hole m => match y with
                     | ax_val v => if (m =? n)
                                   then av_bnd v
                                   else x
                     | _ => x
                     end 
      | _ => x
      end
    }.

  Instance substAMth : Subst a_mth nat a_var :=
    {
    sbst m n y :=
      match m with
      | am_hole n' => match y with
                      | ax_mth m' => if (n' =? n)
                                     then am_bnd m'
                                     else m
                      | _ => m
                      end 
      | _ => m
      end
    }.

  Instance substAVarMap : Subst (partial_map name a_val) nat a_var :=
    {
    sbst m n x := fun y => bind (m y) (fun a => Some (⟦x /s n⟧ a))
    }.

  Instance substExp : Subst exp nat a_var :=
    {
    sbst :=
      fix sbst' e n x :=
        match e with
        | e_hole m =>
          match x with
          | ax_val v =>
            if n =? m
            then (e_val v)
            else e
          | _ => e
          end
        | e_eq e1 e2 => e_eq (sbst' e1 n x) (sbst' e2 n x)
        | e_lt e1 e2 => e_lt (sbst' e1 n x) (sbst' e2 n x)
        | e_if e1 e2 e3 => e_if (sbst' e1 n x) (sbst' e2 n x) (sbst' e3 n x)
        | e_acc_f e' f => e_acc_f (sbst' e' n x) f
        | e_acc_g e1 g e2 => e_acc_g (sbst' e1 n x) g (sbst' e2 n x)
        | _ => e
        end
    }.

  Fixpoint sbstA (A : asrt)(n : nat)(x : a_var) : asrt :=
    match A with
    | a_exp e => a_exp (⟦x /s n⟧ e)
    | a_class y C       => a_class (⟦x /s n⟧ y) C
    | e ∈ Σ => (⟦x /s n⟧ e) ∈ (sbstΣ Σ n x)

    (*connectives*)
    | a_arr A1 A2       => a_arr (sbstA A1 n x) (sbstA A2 n x)
    | a_and A1 A2       => a_and (sbstA A1 n x) (sbstA A2 n x)
    | a_or A1 A2        => a_or (sbstA A1 n x) (sbstA A2 n x)
    | a_neg A'          => a_neg (sbstA A' n x)
    (*quantifiers*)
    | (∀[x⦂ T ]∙ A')          => (∀[x⦂ T ]∙ (sbstA A' (S n) x))
    | (∃[x⦂ T ]∙ A')          => ∃[x⦂ T ]∙ (sbstA A' (S n) x)
    (*permission*)
    | a_acc v1 v2       => a_acc (sbst v1 n x) (sbst v2 n x)
    (*control*)
    | a_call v1 v2 m vMap => a_call (⟦x /s n⟧ v1)
                                    (⟦x /s n⟧ v2)
                                    (⟦x /s n⟧ m)
                                    (⟦x /s n⟧ vMap)

    (*time*)
    | a_next A'         => a_next (sbstA A' n x)
    | a_will A'         => a_will (sbstA A' n x)
    | a_prev A'         => a_prev (sbstA A' n x)
    | a_was A'          => a_was (sbstA A' n x)

    (*space*)
    | A' in_ Σ           => (sbstA A' n x) in_ (sbstΣ Σ n x)

    (*viewpoint*)
    | a_extrn v          => a_extrn (⟦x /s n⟧ v)
    | a_intrn v          => a_intrn (⟦x /s n⟧ v)
    (*)  | a_private y z      => a_private (⟦x /s n⟧ y) (⟦x /s n⟧ z)*)

    | a_self y         => a_self (⟦x /s n⟧ y)
    end

  with
  sbstΣ (Σ : a_set)(n : nat)(x : a_var) : a_set :=
    match Σ with
    | as_bnd Σ' => as_bnd (set_map eq_dec (fun y => ⟦x /s n⟧ y) Σ')
    | ⦃x⃒ A'⦄ => ⦃x⃒ sbstA A' (S n) x⦄
    | as_hole m => match x with
                   | ax_set Σ' => as_bnd Σ'
                   | _ => Σ
                   end
    end.

  (*Instance substAssertionVar : Subst asrt nat value :=
  {sbst := sbstxA}.

Instance substAMth : Subst a_mth nat mth :=
  {
  sbst a n m := match a with
                | am♢ n' => if n' =? n
                           then am_ m
                           else a
                | _ => a
                end
  }.

Fixpoint substmA (A : asrt)(n : nat)(m : mth) :=
  match A with
  (*connectives*)
  | a_arr A1 A2       => a_arr (substmA A1 n m) (substmA A2 n m)
  | a_and A1 A2       => a_and (substmA A1 n m) (substmA A2 n m)
  | a_or A1 A2        => a_or (substmA A1 n m) (substmA A2 n m)
  | a_neg A'          => a_neg (substmA A' n m)
  (*quantifiers*)      
  | a_all T A'      => a_all T (substmA A' (S n) m)
  | a_ex T A'       => a_ex T (substmA A' (S n) m)
  (*control*)
  | a_call v1 v2 am β => a_call v1 v2 ([m /s n] am) β
  (*time*)
  | a_next A'         => a_next (substmA A' n m)
  | a_will A'         => a_will (substmA A' n m)
  | a_prev A'         => a_prev (substmA A' n m)
  | a_was A'          => a_was (substmA A' n m)

  | e ∈ Σ => e ∈ (substmΣ Σ n m)
  | (A' in_ Σ) => (substmA A' n m) in_ (substmΣ Σ n m)

  | _ => A
  end

with
substmΣ (Σ : a_set)(n : nat)(m : mth) :=
  match Σ with
  | ⦃x⃒ A ⦄ => ⦃x⃒ substmA A (S n) m ⦄
  | _ => Σ
  end.

Instance sbstAssertionMth : Subst asrt nat mth :=
  {sbst := substmA
  }.

Fixpoint sbstΣ (Σ1 : a_set)(n : nat)(Σ2 : set a_val) :=
  match Σ1 with
  |as_hole m => if n =? m
               then as_bnd Σ2
               else Σ1
  | ⦃x⃒ A ⦄ => ⦃x⃒ sbstΣA A (S n) Σ2 ⦄
  | _ => Σ1
  end

with
sbstΣA (A : asrt)(n : nat)(Σ : set a_val) : asrt :=
  match A with
  (*connectives*)
  | a_arr A1 A2       => a_arr (sbstΣA A1 n Σ) (sbstΣA A2 n Σ)
  | a_and A1 A2       => a_and (sbstΣA A1 n Σ) (sbstΣA A2 n Σ)
  | a_or A1 A2        => a_or (sbstΣA A1 n Σ) (sbstΣA A2 n Σ)
  | a_neg A'          => a_neg (sbstΣA A' n Σ)
  (*quantifiers*)      
  | a_all T A'      => a_all T (sbstΣA A' (S n) Σ)
  | a_ex T A'       => a_ex T (sbstΣA A' (S n) Σ)
  (*time*)
  | a_next A'         => a_next (sbstΣA A' n Σ)
  | a_will A'         => a_will (sbstΣA A' n Σ)
  | a_prev A'         => a_prev (sbstΣA A' n Σ)
  | a_was A'          => a_was (sbstΣA A' n Σ)

  | e ∈ Σ' => e ∈ (sbstΣ Σ' n Σ)
  | (A' in_ Σ') => (sbstΣA A' n Σ) in_ (sbstΣ Σ' (S n) Σ)

  | _ => A
  end. 

Instance substΣ : Subst a_set nat (set a_val) :=
  { sbst := sbstΣ }.

Instance substΣA : Subst asrt nat (set a_val) :=
  { sbst := sbstΣA }.*)

  Instance substXA : Subst asrt nat a_var :=
    {
    sbst A n x := sbstA A n x
    }.

  Definition initial (σ : config) : Prop :=
    exists c, σ = ([address 0 ↦ ObjectInstance] empty,
                   frm (address 0) empty c :: nil).

  Inductive has_type : config -> a_var -> a_type -> Prop :=
  | t_val : forall σ v, has_type σ (ax_val v) a_Val
  | t_obj : forall χ ψ α o, χ α = Some o ->
                            has_type (χ, ψ) (ax_val (v_ α)) a_Obj
  | t_true : forall σ, has_type σ (ax_val (v_true)) a_Bool
  | t_false : forall σ, has_type σ (ax_val (v_false)) a_Bool
  | t_int : forall σ i, has_type σ (ax_val (v_int i)) a_Int
  | t_mth : forall σ m, has_type σ (ax_mth m) a_Mth
  | t_set : forall σ Σ, has_type σ (ax_set Σ) a_Set.

  Hint Constructors has_type : chainmail_db.

  Inductive has_access_aval : mdl -> mdl -> config -> a_val -> a_val -> Prop :=
  | has_acc : forall M1 M2 σ α1 α2, has_access M1 M2 σ α1 α2 ->
                               has_access_aval M1 M2 σ (a_ α1) (a_ α2).

  Hint Constructors has_access_aval : chainmail_db.

  Inductive makes_call : config -> a_val -> a_val -> a_mth -> partial_map name a_val ->
                         Prop :=
  | method_call : forall χ lcl b ψ m args α1 α2,
      makes_call (χ, frm α1 lcl (call α2 m args ;; b) :: ψ)
                 (a_ α1)
                 (a_ α2)
                 (am_ m)
                 (fun x => bind (args x) (fun v => Some (av_bnd v))).

  Hint Constructors makes_call : chainmail_db.

  Inductive internal_obj : mdl -> mdl -> config -> a_val -> Prop :=
  | int_obj : forall M1 M2 χ ψ α o CDef, χ α = Some o ->
                                         M1 (cname o) = Some CDef ->
                                         internal_obj M1 M2 (χ, ψ) (a_ α).

  Inductive external_obj : mdl -> mdl -> config -> a_val -> Prop :=
  | ext_obj : forall M1 M2 χ ψ α o, χ α = Some o ->
                                    M1 (cname o) = None ->
                                    external_obj M1 M2 (χ, ψ) (a_ α).

  Hint Constructors internal_obj external_obj : chainmail_db.

  Inductive has_class : config -> a_val -> cls -> Prop :=
  | has_cls : forall χ ψ α o, χ α = Some o ->
                              has_class (χ, ψ) (a_ α) (cname o).

  Inductive is_self : config -> a_val -> Prop :=
  | is_slf : forall χ α lcl c ψ, is_self (χ, frm α lcl c :: ψ) (a_ α).

  Inductive exp_satisfaction : mdl -> mdl -> config -> exp -> Prop :=
  | exp_sat : forall M1 M2 M σ e,  M1 ⋄ M2 ≜ M ->
                                   M ∙ σ ⊢ e ↪ v_true ->
                                   exp_satisfaction M1 M2 σ e.

  Hint Constructors has_class is_self exp_satisfaction : chainmail_db.

  Inductive elem_of_set : mdl -> mdl -> config -> exp -> a_set -> Prop :=
  | in_set : forall M1 M2 M σ e α Σ, M1 ⋄ M2 ≜ M ->
                                     M ∙ σ ⊢ e ↪ (v_addr α) ->
                                     set_In (av_bnd (v_addr α)) Σ ->
                                     elem_of_set M1 M2 σ e (as_bnd Σ).

  Hint Constructors elem_of_set : chainmail_db.

  Inductive restrict : a_set -> heap -> heap -> Prop :=
  | rest : forall Σ χ χ', (forall α, set_In (a_ α) Σ ->
                                     exists o, χ' α = Some o) ->
                          (forall α o, χ' α = Some o ->
                                       set_In (a_ α) Σ) ->
                          (forall α o, χ' α = Some o ->
                                       χ α = Some o) ->
                          restrict (as_bnd Σ) χ χ'.

  Hint Constructors restrict : chainmail_db.

  (*  Inductive is_private : mdl -> mdl -> config -> a_val -> a_val -> Prop :=
  | is_priv : forall M1 M2 M σ α1 α2,
      M1 ⋄ M2 ≜ M ->
      M ∙ σ ⊢ (e_acc_g (e_val (v_addr α1)) private (e_val (v_addr α2))) ↪ v_true ->
      is_private M1 M2 σ (a_ α1) (a_ α2).*)

  Reserved Notation "M1 '⦂' M2 '◎' σ0 '…' σ '⊨' A"(at level 40).
  Reserved Notation "M1 '⦂' M2 '◎' σ0 '…' σ '⊭' A"(at level 40).

  Inductive sat : mdl -> mdl -> config -> config -> asrt -> Prop :=

  | sat_self : forall M1 M2 σ σ0 a, is_self σ a ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊨ a_self a

  (** Simple: *)
  (**
Note: #<code>#is_exp e e'#</code># simply maps an #<code>#expr#</code># (defined above) to an expression (#<code>#exp#</code>#) in L#<sub>#oo#</sub>#. #<code>#expr#</code># differs from #<code>#exp#</code># in L#<sub>#oo#</sub># only in that an #<code>#expr#</code># may not contain any variables.
To aid readability, I ignore this distinction between #<code>#e#</code># and #<code>#e'#</code># in the descriptions of #<code>#sat_exp#</code># and #<code>#nsat_exp#</code>#.
   *)
  | sat_exp   : forall M1 M2 σ0 σ e, exp_satisfaction M1 M2 σ e ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_exp e)
  (**
[[[
                     M1 ⋄ M2 ≜ M 
                 M ∙ σ ⊢ e' ↪ v_true
               -----------------------                   (Sat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ e
]]]
   *)

  | sat_class : forall M1 M2 σ0 σ a C, has_class σ a C ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_class a  C)
  (**
[[[
              (α ↦ o) ∈ σ     o has class C
               ----------------------------                   (Sat-Class)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (α : C)
]]]
   *)

  (** Connectives: *)
  | sat_and   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-And)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∧ A2)
]]]
   *)

  | sat_or1   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
               ----------------------------                   (Sat-Or1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
   *)

  | sat_or2   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Or2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ∨ A2)
]]]
   *)

  | sat_arr1  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A2 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊨ A2
               ----------------------------                   (Sat-Arr1)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
   *)

  | sat_arr2  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                         M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⟶ A2)
  (**
[[[
                   M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               ----------------------------                   (Sat-Arr2)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ (A1 ⇒ A2)
]]]
   *)

  | sat_not   : forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊭ A ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ (¬ A)
  (**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊭ A
               -----------------------                   (Sat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ ¬ A
]]]
   *)

  (** Quantifiers: *)

  | sat_all : forall M1 M2 σ0 σ T A, (forall x, has_type σ x T ->
                                                M1 ⦂ M2 ◎ σ0 … σ ⊨ (⟦x /s 0⟧A)) ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀[x⦂ T ]∙ A)
  (**
[[[
                (∀ α o, (α ↦ o) ∈ σ.(heap) → M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               ------------------------------------------------------------                   (Sat-All-x)
                            M1 ⦂ M2 ◎ σ0 … σ ⊨ (∀ x. A)
]]]
   *)

  | sat_ex  : forall M1 M2 σ0 σ x T A, has_type σ x T ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ (⟦x /s 0⟧ A) ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃[x⦂ T ]∙ A)
  (**
[[[
                     (α ↦ o) ∈ σ.(heap)
                M1 ⦂ M2 ◎ σ0 … σ ⊨ ([α / x]A))
               -------------------------------                   (Sat-Ex-x)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ (∃ x. A)
  ]]]
   *)

  (** Permission: *)
  | sat_access : forall M1 M2 σ0 σ a1 a2, has_access_aval M1 M2 σ a1 a2 ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ (a1 access a2)

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
  | sat_call : forall M1 M2 σ0 σ a1 a2 m β,
      makes_call σ a1 a2 m β ->
      M1 ⦂ M2 ◎ σ0 … σ ⊨ (a1 calls a2 ◌ m ⟨ β ⟩)
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
  | sat_extrn : forall M1 M2 σ0 σ a, external_obj M1 M2 σ a ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ a_extrn a
  (**
[[[
               (α ↦ o) ∈ χ   o.(className) ∉ M1
               ---------------------------------                   (Sat-Extrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α external
]]]
   *)

  | sat_intrn : forall M1 M2 σ0 σ a, internal_obj M1 M2 σ a ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊨ a_intrn a
  (**
[[[
               (α ↦ o) ∈ χ   o.(className) ∈ M1
               ---------------------------------                   (Sat-Intrn)
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ α internal
]]]
   *)

  (** Time: *)
  (**
Non-determinism in the temporal operators is removed by using the initial
configuration that satisfaction is defined with.
   *)
  | sat_next : forall M1 M2 σ0 σ A σ', M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ' ->
                                       M1 ⦂ M2 ◎ σ0 … σ' ⊨ A ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_next A)
  (**
[[[
                 M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ'
               M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               -------------------------                   (Sat-Next)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ next A
]]]
   *)

  | sat_will : forall M1 M2 σ0 σ A σ', M1 ⦂ M2 ⦿ σ ⌈⤳⋆⌉ σ' ->
                                       M1 ⦂ M2 ◎ σ0 … σ' ⊨ A ->
                                       M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_will A)
  (**
[[[
                 M1 ⦂ M2 ⦿ σ ⌈⤳⋆⌉ σ'
               M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               -------------------------                   (Sat-Will)
               M1 ⦂ M2 ◎ σ0 … σ ⊨ will A
]]]
   *)

  | sat_prev : forall M1 M2 σ0 σ A, (forall σ', (M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' \/
                                                 σ' = σ0) ->
                                                M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                                M1 ⦂ M2 ◎ σ0 … σ' ⊨ A) ->
                                    M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_prev A)
  (**
[[[
                    M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'
                    M1 ⦂ M2 ⦿ σ' ⤳ σ
                    M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               ---------------------------------                   (Sat-Prev-1)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ prev A
]]]
   *)

  | sat_was : forall M1 M2 σ0 σ A σ', (M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' \/
                                       σ0 = σ') ->
                                      M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                                      M1 ⦂ M2 ◎ σ0 … σ' ⊨ A ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_was A)
  (**
[[[
                    M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'
                    M1 ⦂ M2 ⦿ σ' ⤳⋆ σ
                    M1 ⦂ M2 ◎ σ0 … σ' ⊨ A
               --------------------------------                   (Sat-Was-1)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ was A
]]]
   *)

  (*| sat_was_2 : forall M1 M2 σ0 σ A, M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                              M1 ⦂ M2 ◎ σ0 … σ0 ⊨ A ->
                              M1 ⦂ M2 ◎ σ0 … σ ⊨ (a_was A)*)
  (**
[[[
                    M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ
                    M1 ⦂ M2 ◎ σ0 … σ0 ⊨ A
               --------------------------------                   (Sat-Was-2)
               M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊨ was A
]]]
   *)

  (**
#<h3>#Space#</h3>#
   *)
  | sat_elem : forall M1 M2 σ0 σ e Σ, elem_of_set M1 M2 σ e Σ ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊨ (e ∈ Σ)

  (*)| sat_elem_comp : forall M1 M2 M σ0 σ e e' α A,
    M1 ⋄ M2 ≜ M ->
    M ∙ σ ⊢ e' ↪ (v_addr α) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ ([ax_val (v_ α) /s 0] A) ->
    is_exp e e' ->
    M1 ⦂ M2 ◎ σ0 … σ ⊨ (e ∈ ⦃x⃒ A ⦄)*)

  | sat_in : forall M1 M2 σ0 χ ψ χ' A Σ,
      restrict Σ χ χ' ->
      M1 ⦂ M2 ◎ σ0 … (χ', ψ) ⊨ A ->
      M1 ⦂ M2 ◎ σ0 … (χ, ψ) ⊨ (A in_ Σ)

  where "M1 '⦂' M2 '◎' σ0 '…' σ '⊨' A" := (sat M1 M2 σ0 σ A) : chainmail_scope

  with
    nsat : mdl -> mdl -> config -> config -> asrt -> Prop :=

  | nsat_self : forall M1 M2 σ0 σ a, ~ is_self σ a ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ a_self a

  (*simple*)
  | nsat_exp : forall M1 M2 σ0 σ e, ~ exp_satisfaction M1 M2 σ e ->
                               M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_exp e)
  (**
[[[
                   M1 ⋄ M2 ≜ M
               M ∙ σ ⊢ e ↪ v_false
               --------------------                   (NSat-Exp)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ e
]]]
   *)

  | nsat_class : forall M1 M2 σ0 σ a C, ~ has_class σ a C ->
                                   M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_class a C)
  (**
[[[
                        (α ↦ o) ∈ σ     
               o has class C'      C' ≠ C
               --------------------------                   (NSat-Class1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ (α : C)
]]]
   *)

  (*connectives*)
  | nsat_and1  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∧ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
               --------------------------                   (NSat-And1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
   *)

  | nsat_and2  : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∧ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-And2)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∧ A2
]]]
   *)

  | nsat_or    : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ∨ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Or)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ∨ A2
]]]
   *)

  | nsat_arr   : forall M1 M2 σ0 σ A1 A2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ A2 ->
                                          M1 ⦂ M2 ◎ σ0 … σ ⊭ (A1 ⟶ A2)
  (**
[[[
                 M1 ⦂ M2 ◎ σ0 … σ ⊨ A1
                 M1 ⦂ M2 ◎ σ0 … σ ⊭ A2
               --------------------------                   (NSat-Arr)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ A1 ⇒ A2
]]]
   *)

  | nsat_not   : forall M1 M2 σ0 σ A, M1 ⦂ M2 ◎ σ0 … σ ⊨ A ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ (¬ A)
  (**
[[[
                M1 ⦂ M2 ◎ σ0 … σ ⊨ A
               ----------------------                   (NSat-Not)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ ¬ A
]]]
   *)

  (*quantifiers*)
  | nsat_all : forall M1 M2 σ0 σ A x T, has_type σ x T ->
                                        M1 ⦂ M2 ◎ σ0 … σ ⊭ (⟦x /s 0⟧A) ->
                                        M1 ⦂ M2 ◎ σ0 … σ ⊭ (∀[x⦂ T ]∙ A) 
  (**
[[[
                      (α ↦ o) ∈ σ.(heap)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               ----------------------------                   (NSat-All-x)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ ∀ x. A
]]]
   *)

  | nsat_ex : forall M1 M2 σ0 σ T A, (forall x, has_type σ x T ->
                                                M1 ⦂ M2 ◎ σ0 … σ ⊭ (⟦x /s 0⟧A)) ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ (∃[x⦂ T ]∙ A)
  (**
[[[
               ∀ α o. (α ↦ o) ∈ σ.(heap) → M1 ⦂ M2 ◎ σ0 … σ ⊭ [α / x]A
               --------------------------------------------------------                   (NSat-Ex-x)
                         M1 ⦂ M2 ◎ σ0 … σ ⊭ ∃ x. A
]]]
   *)

  (** Permission: *)
  | nsat_access : forall M1 M2 σ0 σ a1 a2, ~ has_access_aval M1 M2 σ a1 a2 ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ (a1 access a2)
  (**
[[[
                α1 ≠ α2        (∀ o f α3. (α1 ↦ o) ∈ σ ∧ o.f = α3 → α2 ≠ α3)
                    (∀ x. ⌊x⌋ σ ≜ α2 ∧ ⌊this⌋ ≜ α1 → x ∉ σ.(contn))
               ---------------------------------------------------------------                   (NSat-Access)
                       M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 access α2
]]]
   *)

  (** Control: *)
  | nsat_call : forall M1 M2 σ0 σ a1 a2 m β, ~ makes_call σ a1 a2 m β ->
                                        M1 ⦂ M2 ◎ σ0 … σ ⊭ (a1 calls a2 ◌ m ⟨ β ⟩)
  (**
[[[
                    ⌊this⌋ σ ≜ α          α ≠ α1
               ------------------------------------------                   (NSat-Call1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α1 calls α2 ▸ m ⟨ β ⟩
]]]
   *)

  | nsat_extrn : forall M1 M2 σ0 σ a, ~ external_obj M1 M2 σ a ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ a_extrn a
  (**
[[[
                       α ∉ σ.(heap)
               -----------------------------                   (NSat-Extrn1)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ α external
]]]
   *)

  | nsat_intrn : forall M1 M2 σ0 σ a, ~ internal_obj M1 M2 σ a ->
                                      M1 ⦂ M2 ◎ σ0 … σ ⊭ (a internal)
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

  | nsat_next : forall M1 M2 σ0 σ A, (forall σ', M1 ⦂ M2 ⦿ σ ⌈⤳⌉ σ' ->
                                                 M1 ⦂ M2 ◎ σ0 … σ' ⊭ A) ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_next A)
  (**
[[[
                    
                  M1 ⦂ M2 ⦿ σ0 ⌈⤳⌉ σ'
                M1 ⦂ M2 ◎ σ0 … σ' ⊭ A
               -------------------------                   (NSat-Next)
               M1 ⦂ M2 ◎ σ0 … σ ⊭ next A
]]]
   *)

  | nsat_will : forall M1 M2 σ0 σ A, (forall σ', (M1 ⦂ M2 ⦿ σ ⌈⤳⋆⌉ σ') ->
                                                 M1 ⦂ M2 ◎ σ0 … σ' ⊭ A) ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_will A)
  (**
[[[
                    
               (∀ σ'. M1 ⦂ M2 ⦿ σ0 ⌈⤳⋆⌉ σ' →
                      M1 ⦂ M2 ◎ σ0 … σ' ⊭ A)
               -----------------------------                   (NSat-Will)
                M1 ⦂ M2 ◎ σ0 … σ ⊭ will A
]]]
   *)

  | nsat_prev : forall M1 M2 σ0 σ A σ', (M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' \/
                                         σ0 = σ') ->
                                        M1 ⦂ M2 ⦿ σ' ⤳ σ ->
                                        M1 ⦂ M2 ◎ σ0 … σ' ⊭ A ->
                                        M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_prev A)
  (**
[[[
                    
               M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ'       M1 ⦂ M2 ⦿ σ' ⤳ σ
                          M1 ⦂ M2 ◎ σ0 … σ' ⊭ A
               -------------------------------------------                   (NSat-Prev-1)
                    M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ prev A
]]]
   *)

  | nsat_was1 : forall M1 M2 σ0 σ A, (forall σ', M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ->
                                                 M1 ⦂ M2 ⦿ σ' ⤳⋆ σ ->
                                                 M1 ⦂ M2 ◎ σ0 … σ' ⊭ A) ->
                                     M1 ⦂ M2 ◎ σ0 … σ0 ⊭ A ->
                                     M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_was A)
  (**
[[[
                    
               (∀ σ'. M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ∧ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ →
                      M1 ⦂ M2 ◎ σ0 … σ' ⊭ A)
                             M1 ⦂ M2 ◎ σ0 … σ0 ⊭ A
               ------------------------------------------------                   (NSat-Was)
                       M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ prev A
]]]
   *)

  | nsat_was2 : forall M1 M2 σ0 σ A, ~ M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ ->
                                     M1 ⦂ M2 ◎ σ0 … σ ⊭ (a_was A)
  (**
[[[
                    
               (∀ σ'. M1 ⦂ M2 ⦿ σ0 ⤳⋆ σ' ∧ M1 ⦂ M2 ⦿ σ' ⤳⋆ σ →
                      M1 ⦂ M2 ◎ σ0 … σ' ⊭ A)
                             M1 ⦂ M2 ◎ σ0 … σ0 ⊭ A
               ------------------------------------------------                   (NSat-Was)
                       M1 ⦂ M2 ◎ σ0 … (χ, ϕ::ψ) ⊭ prev A
]]]
   *)

  (**
#<h3>#Space#</h3>#
   *)
  | nsat_elem : forall M1 M2 σ0 σ e Σ,
      ~ elem_of_set M1 M2 σ e Σ ->
      M1 ⦂ M2 ◎ σ0 … σ ⊭ (e ∈ Σ)

  (*)| nsat_elem_comp1 : forall M1 M2 M σ0 σ e e' α A,
    M1 ⋄ M2 ≜ M ->
    is_exp e e' ->
    M ∙ σ ⊢ e' ↪ (v_addr α) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ ([ax_val (v_ α) /s 0] A) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ (e ∈ ⦃x⃒ A ⦄)

| nsat_elem_comp2 : forall M1 M2 σ0 σ e A,
    (forall M, ~ M1 ⋄ M2 ≜ M) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ (e ∈ ⦃x⃒ A ⦄)

| nsat_elem_comp3 : forall M1 M2 M σ0 σ e e' A,
    M1 ⋄ M2 ≜ M ->
    is_exp e e' ->
    (forall α, ~ M ∙ σ ⊢ e' ↪ (v_addr α)) ->
    M1 ⦂ M2 ◎ σ0 … σ ⊭ (e ∈ ⦃x⃒ A ⦄)*)

  | nsat_in1 : forall M1 M2 σ0 χ ψ A Σ, (forall χ', ~ restrict Σ χ χ') ->
                                        M1 ⦂ M2 ◎ σ0 … (χ, ψ) ⊭ (A in_ Σ)

  | nsat_in2 : forall M1 M2 σ0 χ χ' ψ A Σ, restrict Σ χ χ' ->
                                           M1 ⦂ M2 ◎ σ0 … (χ', ψ) ⊭ A ->
                                           M1 ⦂ M2 ◎ σ0 … (χ, ψ) ⊭ (A in_ Σ)

  where "M1 '⦂' M2 '◎' σ0 '…' σ '⊭' A" := (nsat M1 M2 σ0 σ A) : chainmail_scope.


  Scheme sat_mut_ind := Induction for sat Sort Prop
    with nsat_mut_ind := Induction for nsat Sort Prop.

  Combined Scheme sat_mutind from sat_mut_ind, nsat_mut_ind.

  Hint Constructors sat nsat : chainmail_db.

  Definition mdl_sat (M : mdl)(A : asrt) := forall M' σ0 σ, (exists M'', M ⋄ M' ≜ M'') ->
                                                            initial σ0 ->
                                                            M ⦂ M' ⦿ σ0 ⤳⋆ σ ->
                                                            M ⦂ M' ◎ σ0 … σ ⊨ A.

  Notation "M '⊨m' A" := (mdl_sat M A)(at level 40) : chainmail_scope.

  Inductive entails : asrt -> asrt -> Prop :=
  | ent : forall A1 A2, (forall σ0 σ M1 M2, M1 ⦂ M2 ◎ σ0 … σ ⊨ A1 ->
                                            M1 ⦂ M2 ◎ σ0 … σ⊨ A2) ->
                        entails A1 A2.

  Hint Constructors entails : chainmail_db.

  Definition equiv_a (A1 A2 : asrt): Prop :=
    (entails A1 A2) /\ (entails A2 A1).


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
