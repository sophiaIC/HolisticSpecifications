Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Import chainmail.defs.
Require Import chainmail.L_def.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


Module AbstractOperationalSemantics(L : LanguageDef).

  Import L.

  Declare Scope reduce_scope.

  Reserved Notation "M '∙' σ1 '⤳' σ2" (at level 40).

  Definition add{A : Type}`{Eq A}(a : A)(s : set A) :=
    set_add eq_dec a s.

  Definition remove{A : Type}`{Eq A}(a : A)(s : set A) :=
    set_remove eq_dec a s.

  Inductive reduction : mdl -> config -> config -> Prop :=
  | r_skip : forall M χ self lcl c ψ,
      M ∙
        (χ, frm self lcl (skip ;; c) :: ψ)
        ⤳
        (χ, frm self lcl c :: ψ)

  | r_call : forall M χ self lcl c α m vs ψ o C CDef b,
      χ α = Some o ->
      cname o = C ->
      M C = Some CDef ->
      c_meths CDef m = Some b ->
      (forall v, In v vs -> visible_r (χ, frm self lcl (α ▸ m ⟨ vs ⟩ ;; c) :: ψ) self v) ->
      visible_r (χ, frm self lcl (α ▸ m ⟨ vs ⟩ ;; c) :: ψ) self (v_addr α) ->
      visible_m (χ, frm self lcl (α ▸ m ⟨ vs ⟩ ;; c) :: ψ) self α m ->
      M ∙
        (χ, (frm self lcl (α ▸ m ⟨ vs ⟩ ;; c)) :: ψ)
        ⤳
        (χ, (frm α vs b) :: (frm self lcl c :: ψ))

  | r_rtrn_1 : forall M χ self1 lcl1 v self2 lcl2 c ψ,
      visible_r (χ, frm self1 lcl1 (c_rtrn v) :: frm self2 lcl2 c :: ψ) self1 v ->
      M ∙
        (χ, (frm self1 lcl1 (c_rtrn v)) :: (frm self2 lcl2 c) :: ψ)
        ⤳
        (χ, (frm self2 (add v lcl2) c) :: ψ)

  | r_rtrn_2 : forall M χ self1 lcl1 v c1 self2 lcl2 c2 ψ,
      visible_r (χ, frm self1 lcl1 (rtrn v ;; c1) :: frm self2 lcl2 c2 :: ψ) self1 v ->
      M ∙
        (χ, (frm self1 lcl1 (rtrn v ;; c1)) :: (frm self2 lcl2 c2) :: ψ)
        ⤳
        (χ, (frm self2 (add v lcl2) c2) :: ψ)

  | r_acc : forall M χ self lcl v c ψ,
      visible_r (χ, frm self lcl (acc v ;; c) :: ψ) self v ->
      M ∙
        (χ, frm self lcl (acc v ;; c) :: ψ)
        ⤳
        (χ, frm self (add v lcl) c :: ψ)

  | r_drop : forall M χ self lcl v c ψ,
      visible_r (χ, frm self lcl c :: ψ) self v ->
      M ∙
        (χ, frm self lcl (drop v ;; c) :: ψ)
        ⤳
        (χ, frm self (remove v lcl) c :: ψ)

  | r_mut : forall M χ self lcl α f v c ψ o,
      visible_w (χ, frm self lcl (α ∙ f ≔ v ;; c) :: ψ) self α f ->
      visible_r (χ, frm self lcl (α ∙ f ≔ v ;; c) :: ψ) self v ->
      χ α = Some o ->
      M ∙
        (χ, frm self lcl (α ∙ f ≔ v ;; c) :: ψ)
        ⤳
        ([α ↦ obj (cname o) ([f ↦ v] (flds o))] χ, frm self lcl c :: ψ)

  | r_new : forall M χ self lcl c α C fs ψ,
      visible_c (χ, frm self lcl (constr C ⟨ fs ⟩ ;; c) :: ψ) self C ->
      max_χ χ α ->
      M ∙
        (χ, frm self lcl (constr C ⟨ fs ⟩ ;; c) :: ψ)
        ⤳
        ([inc α ↦ obj C fs] χ, frm self lcl c :: ψ)

  where "M '∙' σ1 '⤳' σ2" := (reduction M σ1 σ2) : reduce_scope.

  Hint Constructors reduction : reduce_db.

  Definition is_internal (M1 M2 : mdl)(σ : config)(α : addr) :=
    (exists o CDef, fst σ α = Some o  /\
                    M1 (cname o) = Some CDef).

  Definition is_external (M1 M2 : mdl)(σ : config)(α : addr) :=
    (exists o, fst σ α = Some o /\
               (cname o) ∉ M1).

  Definition internal_self (M1 M2 : mdl)(σ : config) :=
    exists χ ϕ ψ, σ = (χ, ϕ :: ψ) /\
                  is_internal M1 M2 σ (this ϕ).

  Definition external_self (M1 M2 : mdl)(σ : config) :=
    exists χ ϕ ψ, σ = (χ, ϕ :: ψ) /\
                  is_external M1 M2 σ (this ϕ).

  Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳…' σ'" (at level 40).

  Inductive internal_reductions : mdl -> mdl -> config -> config -> Prop :=
  | pr_single : forall M1 M2 M σ σ', M1 ⋄ M2 ≜ M ->
                                     M ∙ σ ⤳ σ' ->
                                     external_self M1 M2 σ ->
                                     internal_self M1 M2 σ' ->
                                     M1 ⦂ M2 ⦿ σ ⤳… σ'

  | pr_trans : forall M1 M2 M σ1 σ σn, M1 ⦂ M2 ⦿ σ1 ⤳… σ ->
                                       M1 ⋄ M2 ≜ M ->
                                       M ∙ σ ⤳ σn ->
                                       internal_self M1 M2 σn ->
                                       M1 ⦂ M2 ⦿ σ1 ⤳… σn

  where "M1 '⦂' M2 '⦿' σ '⤳…' σ'" := (internal_reductions M1 M2 σ σ') : reduce_scope.

  Hint Constructors internal_reductions : reduce_db.

  Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳' σ'" (at level 40).

  Inductive pair_reduction : mdl -> mdl -> config -> config -> Prop :=

  | p_internal : forall M1 M2 M σ1 σ σn, M1 ⦂ M2 ⦿ σ1 ⤳… σ ->
                                         M1 ⋄ M2 ≜ M ->
                                         M ∙ σ ⤳ σn ->
                                         external_self M1 M2 σn ->
                                         M1 ⦂ M2 ⦿ σ1 ⤳ σn
  | p_external : forall M1 M2 M σ1 σ2, M1 ⋄ M2 ≜ M ->
                                       M ∙ σ1 ⤳ σ2 ->
                                       external_self M1 M2 σ1 ->
                                       external_self M1 M2 σ2 ->
                                       M1 ⦂ M2 ⦿ σ1 ⤳ σ2

  where "M1 '⦂' M2 '⦿' σ '⤳' σ'" := (pair_reduction M1 M2 σ σ') : reduce_scope.

  Hint Constructors pair_reduction : reduce_db.

  Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" (at level 40).

  Inductive pair_reductions : mdl -> mdl -> config -> config -> Prop :=
  | prs_single : forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                                     M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2

  | prs_trans : forall M1 M2 σ1 σ σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ ->
                                      M1 ⦂ M2 ⦿ σ ⤳⋆ σ2 ->
                                      M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2

  where "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" := (pair_reductions M1 M2 σ σ') : reduce_scope.

  Hint Constructors pair_reductions : reduce_db.

  Definition stack_append (σ : config)(ψ : stack):=
    (fst σ, (snd σ)++ψ).

  Notation "σ '◁' ψ" := (stack_append σ ψ)(at level 40) : reduce_scope.

  Open Scope reduce_scope.
  Definition constrained_pair_reduction (M1 M2 : mdl)(σ1 σ2 : config):=
    exists χ ϕ ψ σ, σ1 = (χ, ϕ :: ψ) /\
                    M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ /\
                    σ2 = (σ ◁ ψ).
  Close Scope reduce_scope.

  Notation "M1 '⦂' M2 '⦿' σ1 '⌈⤳⌉' σ2":=
    (constrained_pair_reduction M1 M2 σ1 σ2)(at level 40) : reduce_scope.

  Open Scope reduce_scope.
  Definition constrained_pair_reductions (M1 M2 : mdl)(σ1 σ2 : config):=
    exists χ ϕ ψ σ, σ1 = (χ, ϕ :: ψ) /\
                    M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ /\
                    σ2 = (σ ◁ ψ).
  Close Scope reduce_scope.

  Notation "M1 '⦂' M2 '⦿' σ1 '⌈⤳⋆⌉' σ2":=
    (constrained_pair_reductions M1 M2 σ1 σ2)(at level 40) : reduce_scope.

  (* reduction lemmas *)
  Open Scope reduce_scope.

  Lemma pair_reductions_transitive :
    forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2 ->
                   forall σ3, M1 ⦂ M2 ⦿ σ2 ⤳⋆ σ3 ->
                         M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ3.
  Proof.
    intros M1 M2 σ1 σ2 Hred;
      induction Hred;
      intros;
      eauto with reduce_db.
  Qed.

  Close Scope reduce_scope.

End AbstractOperationalSemantics.

Module Type SemanticProperties(L : LanguageDef).

  Import L.
  Module LSemantics := AbstractOperationalSemantics(L).
  Import LSemantics.

  Open Scope reduce_scope.
  Open Scope L_scope.


  Parameter semantic_equivalence :
    forall M1 M2 σ1 σ2, (L_red M1 M2 σ1 σ2 <->
                    M1 ⦂ M2 ⦿ ⟦ σ1 ⟧ ⤳ ⟦ σ2 ⟧).


  Close Scope L_scope.
  Close Scope reduce_scope.
End SemanticProperties.
