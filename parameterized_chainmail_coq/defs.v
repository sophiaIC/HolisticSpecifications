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

Inductive stmt : Type :=
| skip : stmt
| call : addr -> mth -> list value -> stmt
| rtrn : value -> stmt
| acc  : value -> stmt
| mut  : addr -> fld -> value -> stmt
| drop : value -> stmt
| new  : cls -> partial_map fld value -> stmt.

Notation "α '∙' f '≔' v" := (mut α f v)(at level 40).
Notation "α '▸' m '⟨' vs '⟩'" := (call α m vs)(at level 40).
Notation "'constr' C '⟨' fs '⟩'" := (new C fs)(at level 40).

Inductive continuation : Type :=
| c_rtrn : value -> continuation
| c_stmt : stmt -> continuation -> continuation.

Notation "s ';;' b" := (c_stmt s b)(at level 40).

(*fields are a mapping from field names to locations in the heap*)
Definition fields := partial_map fld value.

Record object := obj{cname : cls;
                     flds : fields}.

Record frame := frm{this : addr;
                    local : set value;
                    contn : continuation}.

Definition stack := list frame.

Definition heap := partial_map addr object.

Definition config : Type := (heap * stack).

Inductive exp : Type :=
| e_val   : value -> exp
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
                         c_meths : partial_map mth continuation;
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

Inductive classOf : config -> addr -> cls -> Prop :=
| cls_of : forall χ ψ α o, χ α = Some o ->
                      classOf (χ, ψ) α (cname o).

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
  end.

Definition Object := classID 0.

Definition ObjectDefn := clazz Object
                               empty
                               empty.

Definition ObjectInstance := obj Object
                                 empty.

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
