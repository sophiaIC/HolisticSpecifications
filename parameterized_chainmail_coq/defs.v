Require Export Arith.
Require Import List.

Require Import chainmail.CpdtTactics.
Require Import chainmail.common.
Require Export Coq.Numbers.BinNums.
Require Export Coq.Lists.ListSet.
Require Export ZArith.

Inductive fld : Type := fieldID : nat -> fld.

Inductive mth : Type := methID : nat -> mth.

Inductive gfld : Type := gFieldID : nat -> gfld.

Definition internal_g : gfld := gFieldID 0.

Inductive cls : Type := classID : nat -> cls.

Inductive addr : Type := address : nat -> addr.

Inductive name : Type := n_ : nat -> name.

Inductive var : Type := x_this : var | x_ : name -> var.

Inductive value : Type :=
| v_true  : value
| v_false : value
| v_null  : value
| v_addr  : addr -> value
| v_int   : Z -> value.

Hint Resolve Z.eqb_refl Z.eqb_neq Z.eqb_sym Z.eqb_eq Z.eq_dec Z.eqb_neq : eq_db.
Hint Rewrite Z.eqb_refl Z.eqb_neq Z.eqb_sym Z.eqb_eq Z.eq_dec Z.eqb_neq : eq_db.

Program Instance eqbFld : Eq fld :=
  {
  eqb := fun f1 f2 =>
           match f1, f2 with
           | fieldID n1, fieldID n2 => n1 =? n2
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
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
Defined.
Next Obligation.
  destruct a1 as [n];
    destruct a2 as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

Program Instance eqbMth : Eq mth :=
  {
  eqb := fun m1 m2 =>
           match m1, m2 with
           | methID n1, methID n2 => n1 =? n2
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
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
Defined.
Next Obligation.
  destruct a1 as [n];
    destruct a2 as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

Program Instance eqbGfld : Eq gfld :=
  {
  eqb := fun g1 g2 =>
           match g1, g2 with
           | gFieldID n1, gFieldID n2 => n1 =? n2
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
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
Defined.
Next Obligation.
  destruct a1 as [n];
    destruct a2 as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

Program Instance eqbCls : Eq cls :=
  {
  eqb := fun C1 C2 =>
           match C1, C2 with
           | classID n1, classID n2 => n1 =? n2
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
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
Defined.
Next Obligation.
  destruct a1 as [n];
    destruct a2 as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

Program Instance eqbAddr : Eq addr :=
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
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.
Next Obligation.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
Defined.
Next Obligation.
  destruct a1 as [n];
    destruct a2 as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

Program Instance eqbValue : Eq value :=
  {
  eqb := fun v1 v2 =>
           match v1, v2 with
           | v_true, v_true => true
           | v_false, v_false => true
           | v_null, v_null => true
           | v_addr α1, v_addr α2 => eqb α1 α2
           | v_int i, v_int j => Z.eqb i j
           | _, _ => false
           end
  }.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  repeat split;
    intro Hcontra;
    try solve [crush].
Defined.
Next Obligation.
  destruct a; simpl; auto;
    try solve [apply Z.eqb_refl].
  destruct a; simpl; auto.
  apply Nat.eqb_refl.
Defined.
Next Obligation.
  destruct a1; simpl; auto;
    destruct a2; simpl; auto.
  destruct a; simpl; auto;
    destruct a0; simpl; auto.
  rewrite Nat.eqb_sym; auto.
  rewrite Z.eqb_sym; auto.
  (*  rewrite Z.eqb_sym; auto.*)
Defined.
Next Obligation.
  destruct a1, a2; simpl;
    try solve [crush].
  destruct a, a0; simpl; crush; eauto.
  apply Nat.eqb_eq in H; subst; auto.
  apply Z.eqb_eq in H; subst; auto.
  (*  apply Z.eqb_eq in H; subst; auto.*)
Defined.
Next Obligation.
  destruct a1, a2; simpl;
    try solve [crush].
  destruct a, a0; simpl; crush; eauto.
  inversion H0; subst.
  apply Nat.eqb_neq in H; subst; auto.
  apply Z.eqb_neq in H; subst; auto.
  crush.
(*  apply Z.eqb_neq in H; subst; auto.
  crush.*)
Defined.
Next Obligation.
  destruct a1, a2; simpl;
    try solve [crush].
  destruct a, a0; simpl.
  destruct (Nat.eq_dec n n0) as [|Hneq];
    [crush
    |apply <- Nat.eqb_neq in Hneq; auto].
  destruct (Z.eq_dec z z0) as [|Hneq];
    [crush
    |apply <- Z.eqb_neq in Hneq; auto].
  (*  apply Z.eqb_neq; crush.*)
Defined.
Next Obligation.
  destruct a1, a2; simpl; auto;
    try solve [right; intros Hcontra; inversion Hcontra].
  destruct (eq_dec a a0) as [|Hneq]; [subst|];
    auto.
  right; crush.
  destruct (Z.eq_dec z z0) as [|Hneq]; [subst|];
    auto.
  right; crush.
(*  destruct (Z.eq_dec z z0) as [|Hneq]; [subst|];
    auto.
  right; crush.*)
Defined.

Program Instance eqbName : Eq name :=
  {
  eqb := fun l1 l2 =>
           match l1, l2 with
           | n_ n, n_ m => n =? m
           end
  }.
Next Obligation.
  destruct a;
    try (rewrite Nat.eqb_refl);
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    try (rewrite Nat.eqb_sym);
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [crush];
    match goal with
    | [H : (?x =? ?y) = true |- _ ] =>
      apply (Nat.eqb_eq) in H
    end;
    subst;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    match goal with
    | [H : (?x =? ?y) = false |- _ ] =>
      apply (Nat.eqb_neq) in H
    end;
    intro Hcontra;
    match goal with
    | [H : n_ _ = n_ _ |- _ ] =>
      inversion H;
        subst
    end;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [crush].
  apply Nat.eqb_neq;
    intro Hcontra;
    subst;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [right; crush].
  match goal with
  | [|- {n_ ?n = n_ ?m} + {_}] =>
    destruct (Nat.eq_dec n m);
      subst;
      auto
  end.
  right;
    intro Hcontra;
    match goal with
    | [H : n_ _ = n_ _ |- _ ] =>
      inversion H;
        subst;
        auto
    end.
Defined.

Program Instance eqbVar : Eq var :=
  {
  eqb := fun x y =>
           match x, y with
           | x_ n, x_ m => eqb n m
           | x_this, x_this => true
           | _, _ => false
           end
  }.
Next Obligation.
  split;
    intros;
    try intro Hcontra;
    andDestruct;
    crush.
Defined.
Next Obligation.
  split;
    intros;
    try intro Hcontra;
    andDestruct;
    crush.
Defined.
Next Obligation.
  destruct a;
    auto.
  destruct n;
    try (rewrite Nat.eqb_refl);
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    destruct n, n0;
    try (rewrite Nat.eqb_sym);
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [crush].
  destruct n, n0;
    match goal with
    | [H : (?x =? ?y) = true |- _ ] =>
      apply (Nat.eqb_eq) in H
    end;
    subst;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [crush].
  destruct n, n0;
    match goal with
    | [H : (?x =? ?y) = false |- _ ] =>
      apply (Nat.eqb_neq) in H
    end;
    intro Hcontra;
    match goal with
    | [H : x_ _ = x_ _ |- _ ] =>
      inversion H;
        subst
    end;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [crush].
  destruct n, n0.
  apply Nat.eqb_neq;
    intro Hcontra;
    subst;
    auto.
Defined.
Next Obligation.
  destruct a1, a2;
    auto;
    try solve [right; crush].
  destruct n, n0;
    match goal with
    | [|- {x_ (n_ ?n) = x_ (n_ ?m)} + {_}] =>
      destruct (Nat.eq_dec n m);
        subst;
        auto
    end.
  right;
    intro Hcontra;
    match goal with
    | [H : x_ _ = x_ _ |- _ ] =>
      inversion H;
        subst;
        auto
    end.
Defined.

Inductive stmt : Type :=
| skip : stmt
| call : name -> addr -> mth -> partial_map name value -> stmt
| rtrn : value -> stmt
| acc  : name -> value -> stmt
| drop : name -> stmt
| mut  : addr -> fld -> value -> stmt
| new  : cls -> partial_map fld value -> stmt.

Notation "α '∙' f '≔' v" := (mut α f v)(at level 40).
Notation "n '≔m' α '▸' m '⟨' args '⟩'" := (call n α m args)(at level 40).
Notation "'constr' C '⟨' fs '⟩'" := (new C fs)(at level 40).

Inductive block : Type :=
| b_rtrn : value -> block
| b_stmt : stmt -> block -> block.

Inductive continuation :=
| c_hole : name -> block -> continuation
| c_block : block -> continuation.

Notation "s ';;' b" := (b_stmt s b)(at level 40).
Notation "n '≔♢' ';;' b" := (c_hole n b)(at level 41).
Notation "'c_' b" := (c_block b)(at level 41).
Notation "'c_rtrn' v" := (c_ b_rtrn v)(at level 40).

(*fields are a mapping from field names to locations in the heap*)
Definition fields := partial_map fld value.

Record object := obj{cname : cls;
                     flds : fields}.

Record frame := frm{this : addr;
                    local : partial_map name value;
                    contn : continuation}.

Definition stack := list frame.

Definition heap := partial_map addr object.

Definition config : Type := (heap * stack).

Inductive exp : Type :=
| e_val   : value -> exp
| e_var   : var -> exp
| e_hole  : nat -> exp
| e_eq    : exp -> exp -> exp
| e_lt    : exp -> exp -> exp
| e_plus  : exp -> exp -> exp
| e_minus : exp -> exp -> exp
| e_mult  : exp -> exp -> exp
| e_div   : exp -> exp -> exp
| e_if    : exp -> exp -> exp -> exp
| e_acc_f : exp -> fld -> exp
| e_acc_g : exp -> gfld -> exp -> exp.

Hint Constructors exp : L_db.

Notation "'e_true'" := (e_val v_true)(at level 40).
Notation "'e_false'" := (e_val v_false)(at level 40).
Notation "'e_null'" := (e_val v_null)(at level 40).
Notation "'e_addr' r" := (e_val (v_addr r))(at level 40).
Notation "'e_int' i" := (e_val (v_int i))(at level 40).
Notation "e1 '⩵' e2" := (e_eq e1 e2)(at level 40).
Notation "e1 '⩵̸' e2" := ((e1 ⩵ e2) ⩵ e_false)(at level 40).
Notation "e1 '⩻' e2" := (e_lt e1 e2)(at level 40).
Notation "e1 '⩑' e2" := (e_if e1 (e_if e2 (e_true) (e_false)) (e_false))(at level 40).
Notation "e1 '⩒' e2" := (e_if e1 (e_true) (e_if e2 (e_true) (e_false)))(at level 40).
Notation "e1 '⩽' e2" := ((e1 ⩻ e2) ⩒ (e1 ⩵ e2))(at level 40).
Notation "'neg' e" := (e ⩵ (e_false))(at level 40).
Notation "e1 '⩼' e2" := (neg (e1 ⩽ e2))(at level 40).
Notation "e1 '⩾' e2" := ((e1 ⩼ e2) ⩒ (e1 ⩵ e2))(at level 40).

(*)Inductive var : Type :=
| hole : nat -> var
| bnd : nat -> var.*)

(*ghost_fields is a mapping from ghost field names to expressions*)
Definition ghost_fields := partial_map gfld exp.

Record classDef := clazz{c_name : cls;
                         c_meths : partial_map mth block;
                         c_g_fields : ghost_fields}.

Definition mdl := partial_map cls classDef.

Inductive le_α : addr -> addr -> Prop :=
| le_addr : forall n m, n <= m ->
                   le_α (address n) (address m).

Hint Constructors le_α : L_db.

Definition inc (α : addr) : addr :=
  match α with
  | address n => address (S n)
  end.

Inductive max_χ {B : Type} : partial_map addr B -> addr -> Prop :=
| max_heap : forall χ α, (exists b, χ α = Some b) ->
                    (forall α' b, χ α' = Some b ->
                             le_α α' α) ->
                    max_χ χ α.

Hint Constructors max_χ : L_db.

Lemma max_χ_neq :
  forall {B : Type} χ α, max_χ χ α ->
                    forall α' (b : B), χ α' = Some b ->
                                  inc α <> α'.
Proof.
  intros B χ α Hmax;
    inversion Hmax;
    subst;
    clear Hmax;
    intros;
    intro Hcontra;
    subst.
  match goal with
  | [Ha : forall _ _, ?m _ = Some _ -> _,
       Hb : ?m _ = Some _ |- _] =>
    apply Ha in Hb;
      inversion Hb;
      subst;
      simpl in *;
      clear Hb
  end.
  match goal with
  | [H : address _ = address _ |- _] =>
    inversion H;
      subst;
      clear H
  end.
  crush.
Qed.

Inductive classOf : config -> addr -> cls -> Prop :=
| cls_of : forall χ ψ α o, χ α = Some o ->
                      classOf (χ, ψ) α (cname o).

Definition Object := classID 0.

Definition ObjectDefn := clazz Object
                               empty
                               empty.

Definition ObjectInstance := obj Object
                                 empty.

Definition initial (σ : config) : Prop :=
  exists c, σ = ([address 0 ↦ ObjectInstance] empty,
            frm (address 0) empty c :: nil).

Reserved Notation "M1 '⋄' M2 '≜' M"(at level 40).

Inductive link : mdl -> mdl -> mdl -> Prop :=
| m_link : forall M1 M2, (forall C def, C <> Object ->
                              M1 C = Some def ->
                              C ∉ M2) ->
                    (forall C def, C <> Object ->
                              M2 C = Some def ->
                              C ∉ M1) ->
                    M1 ⋄ M2 ≜ (M1 ∪ M2)

where "M1 '⋄' M2 '≜' M" := (link M1 M2 M).

Lemma linking_unique :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             forall M', M1 ⋄ M2 ≜ M' ->
                   M' = M.
Proof.
  intros M1 M2 M Hlink1 M' Hlink2;
    inversion Hlink1; inversion Hlink2;
      subst;
      auto.
Qed.

Ltac link_unique_auto :=
  match goal with
  | [H1 : ?M1 ⋄ ?M2 ≜ ?M, H2 : ?M1 ⋄ ?M2 ≜ ?M' |-_] =>
    assert (M' = M);
    [eapply linking_unique;
     eauto|subst M']
  end.

Ltac auto_specialize :=
  match goal with
  | [H : ?P -> ?Q,
         H' : ?P |- _ ] => specialize (H H')
  | [H : ?x = ?x -> _ |- _] =>
    specialize (H eq_refl)
  end.

Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.

Ltac destruct_exists_loo :=
  match goal with
  | [H : exists _ : config, _ |- _] =>
    let σ := fresh "σ" in
    destruct H as [σ]
  | [H : exists _ : frame, _ |- _] =>
    let ϕ := fresh "ϕ" in
    destruct H as [ϕ]
  | [H : exists _ : list frame, _ |- _] =>
    let ψ := fresh "ψ" in
    destruct H as [ψ]
  | [H : exists _ : stack, _ |- _] =>
    let ψ := fresh "ψ" in
    destruct H as [ψ]
  | [H : exists _ : heap, _ |- _] =>
    let χ := fresh "χ" in
    destruct H as [χ]
  | [H : exists _ : stmt, _ |- _] =>
    let s := fresh "s" in
    destruct H as [s]
  | [H : exists _ : continuation, _ |- _] =>
    let c := fresh "c" in
    destruct H as [c]
  | [H : exists _ : partial_map _ _, _ |- _] =>
    let f := fresh "f" in
    destruct H as [f]
  | [H : exists _ : mth, _ |- _] =>
    let m := fresh "m" in
    destruct H as [m]
  | [H : exists _ : fld, _ |- _] =>
    let f := fresh "f" in
    destruct H as [f]
  | [H : exists _ : gfld, _ |- _] =>
    let g := fresh "g" in
    destruct H as [g]
  | [H : exists _ : cls, _ |- _] =>
    let C := fresh "C" in
    destruct H as [C]
  | [H : exists _ : addr, _ |- _] =>
    let α := fresh "α" in
    destruct H as [α]
  | [H : exists _ : value, _ |- _] =>
    let v := fresh "v" in
    destruct H as [v]
  | [H : exists _ : obj, _ |- _] =>
    let o := fresh "o" in
    destruct H as [o]
  | [H : exists _ : mdl, _ |- _] =>
    let M := fresh "M" in
    destruct H as [M]
  | [H : exists _, _ |- _] => destruct H
  end.

Ltac cleanup :=
  match goal with
  | [Ha : ?P, Hb : ?P |- _] =>
    clear Hb
  end.

Definition stack_append (σ : config)(ψ : stack):=
  (fst σ, (snd σ)++ψ).

Notation "σ '◁' ψ" := (stack_append σ ψ)(at level 40).

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

Lemma is_internal_stack_append :
  forall M1 M2 σ α, is_internal M1 M2 σ α ->
               forall ψ, is_internal M1 M2 (σ ◁ ψ) α.
Proof.
  intros;
    unfold is_internal, stack_append in *;
    repeat destruct_exists_loo;
    andDestruct.
  repeat eexists;
    eauto.
Qed.

Lemma is_external_stack_append :
  forall M1 M2 σ α, is_external M1 M2 σ α ->
               forall ψ, is_external M1 M2 (σ ◁ ψ) α.
Proof.
  intros;
    unfold is_external, stack_append in *;
    repeat destruct_exists_loo;
    andDestruct.
  repeat eexists;
    eauto.
Qed.

Lemma internal_self_stack_append :
  forall M1 M2 σ, internal_self M1 M2 σ ->
             forall ψ, internal_self M1 M2 (σ ◁ ψ).
Proof.
  intros;
    unfold internal_self, is_internal, stack_append in *;
    repeat destruct_exists_loo;
    andDestruct;
    repeat destruct_exists_loo;
    andDestruct;
    subst.
  repeat eexists;
    eauto.
Qed.

Lemma external_self_stack_append :
  forall M1 M2 σ, external_self M1 M2 σ ->
             forall ψ, external_self M1 M2 (σ ◁ ψ).
Proof.
  intros;
    unfold external_self, is_external, stack_append in *;
    repeat destruct_exists_loo;
    andDestruct;
    repeat destruct_exists_loo;
    andDestruct;
    subst.
  repeat eexists;
    eauto.
Qed.


Ltac eq_auto :=
  match goal with

  | [Heqb : context[eqb ?a ?a]|- _] => rewrite eqb_refl in Heqb; auto
  | [|- context[eqb ?a ?a]] => rewrite eqb_refl; auto

  | [Heq : ?a1 <> ?a2, Heqb : context[eqb ?a1 ?a2]|- _] => rewrite neq_eqb in Heqb; auto
  | [Heq : ?a1 <> ?a2, Heqb : context[eqb ?a2 ?a1]|- _] => rewrite eqb_sym in Heqb;
                                                        rewrite neq_eqb in Heqb; auto
  | [Heq : ?a1 <> ?a2 |- context[eqb ?a1 ?a2]] => rewrite neq_eqb; auto
  | [Heq : ?a1 <> ?a2 |- context[eqb ?a2 ?a1]] => rewrite eqb_sym;
                                               rewrite neq_eqb; auto

  | [H : eqb ?a1 ?a2 = true |- _] =>
    let Hnew := fresh in
    assert (Hnew : a1 = a2);
    [eapply eqb_eqp in H; auto|subst; auto]
  | [H : eqb ?a1 ?a2 = false |- _] =>
    let Hnew := fresh in
    assert (Hnew : a1 <> a2);
    [eapply eqb_neq in H; auto|auto]

  | [H : Some ?a1 <> Some ?a2 |- _] =>
    notHyp (a1 <> a2);
    assert (a1 <> a2);
    [intro Hcontra; subst; crush|auto]
  end.

Ltac map_rewrite :=
  match goal with
  | [H : context[update _ _] |-_] => unfold update in H; repeat eq_auto
  | [|- context[update _ _]] => unfold update; repeat eq_auto
  | [H : context[t_update _ _] |-_] => unfold t_update in H; repeat eq_auto
  | [|- context[t_update _ _]] => unfold t_update; repeat eq_auto
  | [H : context[empty] |-_] => unfold empty in H; repeat eq_auto
  | [|- context[empty]] => unfold empty; repeat eq_auto
  | [H : context[t_empty] |-_] => unfold t_empty in H; repeat eq_auto
  | [|- context[t_empty]] => unfold t_empty; repeat eq_auto
  | [H : context[fst (_, _)] |- _] => unfold fst in H; repeat eq_auto
  | [|- context[fst (_, _)]] => unfold fst; repeat eq_auto
  | [H : context[snd (_, _)] |- _] => unfold snd in H; repeat eq_auto
  | [|- context[snd (_, _)]] => unfold snd; repeat eq_auto
  end.

Lemma partial_map_in_not_in_contra :
  forall {A B : Type}`{Eq A}{m : partial_map A B} {a} {b},
    m a = Some b ->
    a ∉ m ->
    False.
Proof.
  intros A B Heq m a b;
    intros.
  crush.
Qed.

Inductive contn_is : continuation -> config -> Prop :=
| is_stmt : forall self lcl c χ ψ,
    contn_is c (χ, frm self lcl c :: ψ).

Hint Constructors contn_is : L_db.

Lemma le_α_eq :
  forall α1 α2, le_α α1 α2 ->
           le_α α2 α1 ->
           α1 = α2.
Proof.
  intros.
  repeat match goal with
         | [H : le_α ?α1 ?α2 |- _] =>
           inversion H;
             subst;
             clear H
         end.
  crush.
Qed.

Lemma max_χ_unique :
  forall {B : Type} (χ : partial_map addr B) α1,
    max_χ χ α1 ->
    forall α2, max_χ χ α2 ->
          α2 = α1.
Proof.
  intros.
  repeat match goal with
         | [H : max_χ ?χ ?α |- _] =>
           inversion H;
             subst;
             clear H
         end.
  repeat destruct_exists_loo.
  repeat match goal with
         | [Ha : forall _ _, ?m _ = Some _ -> le_α _ ?α1,
              Hb : forall _ _, ?m _ = Some _ -> le_α _ ?α2,
              Hc : ?m ?α2 = Some _ |- _] =>
           apply Ha in Hc
         end.
  apply le_α_eq;
    auto.
Qed.

Lemma nil_app_contra :
  forall {A : Type} l1 (a : A) l2,
    nil = l1 ++ a :: l2 ->
    False.
Proof.
  intros A l1;
    induction l1;
    intros;
    simpl in *;
    crush.
Qed.

Lemma cons_app_contra :
  forall {A : Type} l1 (a1 a2 a3 : A) l2,
    a1 :: nil = l1 ++ a2 :: a3 :: l2 ->
    False.
Proof.
  intros A l1;
    induction l1;
    intros;
    simpl in *;
    crush.
  apply nil_app_contra in H;
    auto.
Qed.

Lemma length_neq :
  forall {A : Type}{l1 l2 : list A},
    length l1 <> length l2 ->
    l1 <> l2.
Proof.
  intros A l1;
    induction l1;
    intros;
    destruct l2;
    simpl in *;
    crush.
Qed.

Ltac simpl_crush :=
  match goal with
  | [ H : (_, _) = (_, _) |- _] =>
    inversion H; subst;
    clear H
  | [ H : _::_ = _::_ |- _] =>
    inversion H; subst;
    clear H
  | [ H : Some _ = Some _ |- _] =>
    inversion H; subst;
    clear H
  | [ Ha : ?x = ?y,
           Hb : ?M ?x = Some _ |- _] =>
    rewrite Ha in Hb
  | [ Ha : ?M ?x = None,
           Hb : ?M ?x = Some _ |- _] =>
    rewrite Ha in Hb;
    inversion Hb
  | [ H : v_addr _ = v_addr _ |- _] =>
    inversion H; subst;
    clear H
  | [ Ha : contn ?ϕ = _, Hb : contn ?ϕ = _ |- _] =>
    rewrite Ha in Hb;
    inversion Hb;
    subst;
    clear Hb
  | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _] =>
    rewrite Ha in Hb;
    inversion Hb;
    subst;
    clear Hb
  | [H : true = false |- _] =>
    inversion H
  | [H : false = true |- _] =>
    inversion H
  | [H : ?x <> ?x |- _] =>
    contradiction H;
    auto
  | [Ha : ?χ ?α = Some _,
          Hb : max_χ ?χ ?α' |- _ ] =>
    notHyp (inc α' <> α);
    assert (inc α' <> α);
    [eapply max_χ_neq; eauto|]
  | [Ha : ?m ?a = Some ?b,
          Hb : ?a ∉ ?m |- _] =>
    contradiction (partial_map_in_not_in_contra Ha Hb)
  | [H : contn_is _ _ |- _] =>
    inversion H;
    subst;
    clear H
  | [Ha : max_χ ?χ ?α1,
          Hb : max_χ ?χ ?α2 |- _ ] =>
    assert (α1 = α2);
    [eapply max_χ_unique; eauto|subst; clear Ha]

  | [H : _ ≔♢ ;; _ = _ ≔♢ ;; _ |- _ ] =>
    inversion H;
    subst;
    clear H
  | [H : c_ _ = c_ _ |- _ ] =>
    inversion H;
    subst;
    clear H

  | [H : _ ;; _ = _ ;; _ |- _ ] =>
    inversion H;
    subst;
    clear H

  | [H : nil = _ :: _ |- _ ] =>
    inversion H
  | [H : _ :: _ = nil |- _ ] =>
    inversion H

  | [H : nil = _ ++ _ :: _ |- _ ] =>
    apply nil_app_contra in H;
    crush
  | [H : _ ++ _ :: _ = nil |- _ ] =>
    symmetry in H;
    apply nil_app_contra in H;
    crush

  | [H : _ :: nil = _ ++ _ :: _ :: _ |- _ ] =>
    apply cons_app_contra in H;
    crush
  | [H : _ ++ _ :: _ :: _ = _ :: nil |- _ ] =>
    symmetry in H;
    apply cons_app_contra in H;
    crush
  end.
