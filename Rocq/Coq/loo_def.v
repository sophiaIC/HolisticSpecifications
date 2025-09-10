Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Numbers.BinNums.
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
| v_addr   : addr -> value
| v_int : Z -> value.

Hint Resolve Z.eqb_refl Z.eqb_neq Z.eqb_sym Z.eqb_eq Z.eq_dec Z.eqb_neq : eq_db.
Hint Rewrite Z.eqb_refl Z.eqb_neq Z.eqb_sym Z.eqb_eq Z.eq_dec Z.eqb_neq : eq_db.

Definition state := partial_map var value.

Program Instance eqbFld : Eq fld :=
  {
    eqb := fun f1 f2 =>
             match f1, f2 with
             | fieldID n1, fieldID n2 => n1 =? n2
             end
  }.
Next Obligation.
  intros. destruct a. apply Nat.eqb_refl.
Defined.
Next Obligation.
  intros. destruct a1. destruct a2. apply Nat.eqb_sym.
Defined.
Next Obligation.
  intros.
    destruct a1.
    destruct a2.
    symmetry in H.
    apply beq_nat_eq in H.
    subst. auto.
Defined.
Next Obligation.
  intros.
    destruct a1.
    destruct a2.
    rewrite Nat.eqb_neq in H.
    crush.
Defined.
Next Obligation.
  intros.
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

Definition this := bnd 0.

(*fields are a mapping from field names to locations in the heap*)
Definition fields := partial_map fld value.

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

Hint Constructors exp : loo_db.

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

Inductive ref : Type :=
| r_exp : exp -> ref
| r_var : var -> ref
| r_fld : var -> fld -> ref.

Hint Constructors ref : loo_db.

Inductive stmt : Type :=
| s_asgn : ref -> ref -> stmt
| s_meth : var -> var -> mth -> partial_map var var -> stmt
| s_new  : var -> cls -> partial_map var var -> stmt
| s_if : exp -> stmt -> stmt -> stmt
| s_stmts : stmt -> stmt -> stmt
| s_rtrn : var -> stmt.

Hint Constructors stmt : loo_db.

Notation "'r_' x" := (r_var x)(at level 40).
Notation "x '◌' f" := (r_fld x f)(at level 40).
Notation "s1 ';;' s2" := (s_stmts s1 s2)(at level 40).
Notation "r1 '≔' r2" := (s_asgn r1 r2)(at level 40).
Notation "x '≔′' e" := (s_asgn (r_var x) (r_exp e))(at level 40).

Definition stmts (xs : list stmt) dflt : stmt := fold_right s_stmts (last xs dflt) (removelast xs).

Inductive continuation : Type :=
| c_stmt : stmt -> continuation
| c_hole : var -> stmt -> continuation.

Hint Constructors continuation : loo_db.

(* A method is arguments and a body *)
Definition method := ((list var) * stmt)%type.

(*methods is a mapping from method names to a method*)
Definition methods := partial_map mth method.

(*ghost_fields is a mapping from ghost field names to expressions*)
Definition ghost_fields := partial_map gfld (var * exp).

Definition private := gFieldID 0.

Record classDef := clazz'{c_name : cls;
                          c_flds : list fld;
                          c_intrn : list fld;
                          c_constructor: option method;
                          c_meths : methods;
                          c_g_fields : ghost_fields}.

Definition clazz c_name c_flds c_intrn := clazz' c_name c_flds c_intrn None.

(* Useful for calling 'default constructors', if the fields have existing names *)
Definition field_param field := match field with fieldID k => bnd (S k) end.

Definition constructor cDef := match c_constructor cDef with
  | Some c => c
  | None   => let vars := map field_param (c_flds cDef) in
              let mkAssign field := s_asgn (r_fld this field) (r_var (field_param field)) in
              let assignments := stmts (map mkAssign (c_flds cDef)) (s_asgn (r_var this) (r_var this)) in
              (vars, assignments)
  end.

Record obj := new{cname : cls;
                  flds : fields}.

Definition Object := classID 0.

Definition ObjectDefn := clazz Object
                               nil
                               nil
                               empty
                               empty.

Definition ObjectInstance := new Object
                                 empty.

Definition mdl := partial_map cls classDef.

Definition heap := partial_map addr obj.

Record frame := frm{vMap : state;
                    contn : continuation}.

Definition stack := list frame.

(*Inductive stack :=
| base : stack
| scons : frame -> stack -> stack.*)

(*Definition peek (ψ : stack) : option frame :=
  match ψ with
  | nil => None
  | ϕ :: _ => Some ϕ
  end.*)

(*Definition pop (ψ : stack) : option stack :=
  match ψ with
  | nil => None
  | _ :: ψ => Some ψ
  end.*)

Instance stackMap : Mappable stack var (option value) :=
  {mapp :=
     fix mapp S x :=
       match S with
       | nil => None
       | ϕ :: S' => ϕ.(vMap) x
       end
  }.

Definition config : Type := (heap * stack).

Instance configMapHeap : Mappable config addr (option obj) :=
  {mapp σ α := (fst σ) α}.

Instance configMapStack : Mappable config var (option value) :=
  {mapp σ x := mapp (snd σ) x}.

(*Instance expFoldable : PropFoldable exp var :=
  {
    foldAnd :=
      fix foldE e f n P :=
        match e with
        | e_var x => f x n
        | e_eq e1 e2 => foldE e1 f n P /\ foldE e2 f n P
        | e_if e1 e2 e3 => foldE e1 f n P /\ foldE e2 f n P /\ foldE e3 f n P
        | e_acc_f e' f' => foldE e' f n P
        | e_acc_g e1 g e2 => foldE e1 f n P /\ foldE e2 f n P
        | _ => P
        end;

    foldOr :=
      fix foldE e f n P :=
        match e with
        | e_var x => f x n
        | e_eq e1 e2 => foldE e1 f n P \/ foldE e2 f n P
        | e_if e1 e2 e3 => foldE e1 f n P \/ foldE e2 f n P \/ foldE e3 f n P
        | e_acc_f e' f' => foldE e' f n P
        | e_acc_g e1 g e2 => foldE e1 f n P \/ foldE e2 f n P
        | _ => P
        end
  }.*)

Reserved Notation "'⌊' x '⌋' σ '≜' α" (at level 40).
Reserved Notation "'⌊' Σ '⌋' σ '≜′' As" (at level 40).

(** #<h3># Variable and Set Interpretation (Definition 4, OOPSLA2019):#</h3># *)

Inductive interpret_x : var -> config -> value -> Prop :=
| int_x : forall x σ v, mapp σ x = Some v -> 
                   ⌊ x ⌋ σ ≜ v
where "'⌊' x '⌋' σ '≜' v" := (interpret_x x σ v).

Hint Constructors interpret_x : loo_db.
  
Inductive interpret_Σ : list var -> config -> list value -> Prop :=
| int_nil  : forall σ, ⌊ nil ⌋ σ ≜′ nil
| int_cons : forall x Σ σ α αs, ⌊ x ⌋ σ ≜ α ->
                           ⌊ Σ ⌋ σ ≜′ αs ->
                           ⌊ x::Σ ⌋ σ ≜′ (α::αs)
where "'⌊' Σ '⌋' σ '≜′' αs" := (interpret_Σ Σ σ αs).

Hint Constructors interpret_Σ : loo_db.

Reserved Notation "σ1 '↓' Σ '≜' σ2" (at level 80).

Inductive restrict : config -> list var -> config -> Prop :=
| rstrct : forall Σ σ As χ χ', ⌊ Σ ⌋ σ ≜′ As ->
                          fst σ = χ ->
                          (forall α o, χ' α = Some o ->
                                  χ α = Some o) ->
                          (forall α o, χ' α = Some o ->
                                  In (v_addr α) As) ->
                          (forall α o, In (v_addr α) As ->
                                  χ' α = Some o) ->
                          σ ↓ Σ ≜ (χ', snd σ)
where "σ1 '↓' Σ '≜' σ2" := (restrict σ1 Σ σ2).


Definition update_ϕ_map (ϕ : frame)(x : var)(v : value) :=
  frm (update x v ϕ.(vMap)) (ϕ.(contn)).

Definition update_ϕ_contn (ϕ : frame)(c : continuation) :=
  frm (ϕ.(vMap)) c.

Definition update_ψ_map (ψ : stack)(x : var)(v : value) : stack :=
  match ψ with
  | nil => nil
  | ϕ :: ψ' => (update_ϕ_map ϕ x v) :: ψ'
  end.

Definition update_ψ_contn (ψ : stack)(c : continuation) : stack :=
  match ψ with
  | nil => nil
  | ϕ :: ψ' => (update_ϕ_contn ϕ c) :: ψ'
  end.

Definition update_σ_map (σ : config)(x : var)(v : value) :=
  (fst σ, update_ψ_map (snd σ) x v).

Definition update_σ_contn (σ : config)(c : continuation) :=
  (fst σ, update_ψ_contn (snd σ) c).

Inductive classOf : var -> config -> cls -> Prop :=
|cls_of : forall x σ α χ o C, ⌊ x ⌋ σ ≜ (v_addr α) ->
                         fst σ = χ ->
                         χ α = Some o ->
                         cname o = C ->
                         classOf x σ C.

Definition finite_ϕ (ϕ : frame) : Prop :=
  finite (vMap ϕ).

Definition finite_ψ (ψ : stack) : Prop :=
  forall ϕ, In ϕ ψ -> finite_ϕ ϕ.

Definition finite_σ (σ : config) : Prop :=
  finite_ψ (snd σ).

Inductive not_stuck : continuation -> Prop :=
| ns_stmt : forall s, not_stuck (c_stmt s).

Hint Constructors not_stuck : loo_db.

Definition not_stuck_ϕ (ϕ : frame) : Prop :=
  not_stuck (contn ϕ).

Definition not_stuck_σ (σ : config) : Prop :=
  exists ϕ ψ, snd σ = ϕ::ψ /\ not_stuck_ϕ ϕ.

Inductive waiting : continuation -> Prop :=
| w_hole : forall x s, waiting (c_hole x s).

Hint Constructors waiting : loo_db.

Definition waiting_ϕ (ϕ : frame) : Prop :=
  waiting (contn ϕ).

Definition waiting_ψ (ψ: stack) : Prop :=
  forall ϕ, In ϕ ψ ->
       waiting_ϕ ϕ.

Definition waiting_σ (σ : config) : Prop :=
  exists ϕ ψ, snd σ = ϕ :: ψ /\
         waiting_ψ ψ.

Inductive val_wf : heap -> value -> Prop :=
| true_wf : forall χ, val_wf χ v_true
| false_wf : forall χ, val_wf χ v_false
| null_wf : forall χ, val_wf χ v_null
| addr_wf : forall χ α o, χ α = Some o ->
                     val_wf χ (v_addr α).

Hint Constructors val_wf : loo_db.

Inductive state_wf : heap -> state -> Prop :=
| st_wf : forall χ m, (forall x v, m x = Some v ->
                         val_wf χ v) ->
                 state_wf χ m.

Hint Constructors state_wf : loo_db.

Inductive has_self_ϕ : heap -> frame -> Prop :=
| self_frm : forall χ ϕ, (exists α o, ϕ.(vMap) this = Some (v_addr α) /\
                            χ α = Some o) ->
                    has_self_ϕ χ ϕ.

Hint Constructors has_self_ϕ : loo_db.

Inductive has_self_σ : config -> Prop :=
| self_config : forall χ ψ, (forall ϕ, In ϕ ψ ->
                             has_self_ϕ χ ϕ) ->
                       has_self_σ (χ, ψ).

Hint Constructors has_self_σ : loo_db.

Inductive σ_wf : config -> Prop :=
| config_wf : forall σ, has_self_σ σ ->
                   finite_σ σ ->
                   not_stuck_σ σ ->
                   waiting_σ σ ->
                   σ_wf σ.

Hint Constructors σ_wf : loo_db.

Inductive χ_wf : mdl -> heap -> Prop :=
| heap_wf :  forall M χ, (forall α o C, χ α = Some o ->
                              cname o = C ->
                              exists CDef,
                                M C = Some CDef /\
                                (forall f, In f (c_flds CDef) ->
                                      exists v, (flds o) f = Some v)) ->
                    χ_wf M χ.

Hint Constructors χ_wf : loo_db.

Inductive notin_exp : exp -> var -> Prop :=
| ni_val   : forall v x, notin_exp (e_val v) x
| ni_var   : forall x y, x <> y ->
                    notin_exp (e_var x) y
| ni_hole  : forall m x, notin_exp (e_hole m) x
| ni_eq    : forall e1 e2 x, notin_exp e1 x ->
                        notin_exp e2 x ->
                        notin_exp (e_eq e1 e2) x
| ni_plus : forall e1 e2 x, notin_exp e1 x ->
                       notin_exp e2 x ->
                       notin_exp (e_plus e1 e2) x
| ni_minut : forall e1 e2 x, notin_exp e1 x ->
                        notin_exp e2 x ->
                        notin_exp (e_minus e1 e2) x
| ni_mult : forall e1 e2 x, notin_exp e1 x ->
                       notin_exp e2 x ->
                       notin_exp (e_mult e1 e2) x
| ni_div : forall e1 e2 x, notin_exp e1 x ->
                       notin_exp e2 x ->
                       notin_exp (e_div e1 e2) x
| ni_if    : forall e1 e2 e3 x, notin_exp e1 x ->
                           notin_exp e2 x ->
                           notin_exp e3 x ->
                           notin_exp (e_if e1 e2 e3) x
| ni_acc_f : forall e f x, notin_exp e x ->
                      notin_exp (e_acc_f e f) x
| ni_acc_g : forall e f e' x, notin_exp e x ->
                         notin_exp e' x ->
                         notin_exp (e_acc_g e f e') x.

Hint Constructors notin_exp : loo_db.

Inductive notin_ref : ref -> var -> Prop :=
| ni_ref_var : forall x y, x <> y ->
                      notin_ref (r_var x) y
| ni_ref_fld : forall x y f, x <> y ->
                        notin_ref (r_fld x f) y.

Hint Constructors notin_ref : loo_db.

Inductive notin_stmt : stmt -> var -> Prop :=
| ni_asgn : forall r1 r2 x, notin_ref r1 x ->
                       notin_ref r2 x ->
                       notin_stmt (s_asgn r1 r2) x
| ni_meth : forall x y m ps z, x <> z ->
                          y <> z ->
                          (forall x1 x2, ps x1 = Some x2 ->
                                    x2 <> z) ->
                          notin_stmt (s_meth x y m ps) z
| ni_new : forall x C fs y, x <> y ->
                       (forall f z, fs f = Some z ->
                               z <> y) ->
                       notin_stmt (s_new x C fs) y
| ni_if_stmt : forall e s1 s2 x, notin_exp e x ->
                            notin_stmt s1 x ->
                            notin_stmt s2 x ->
                            notin_stmt (s_if e s1 s2) x
| ni_stmts : forall s1 s2 x, notin_stmt s1 x ->
                        notin_stmt s2 x ->
                        notin_stmt (s_stmts s1 s2) x
| ni_rtrn : forall x y, x <> y ->
                   notin_stmt (s_rtrn x) y.

Hint Constructors notin_ref notin_stmt : loo_db.

Inductive meths_wf : methods -> Prop :=
| mths_wf : forall mths, (forall m xs s, mths m = Some (xs, s) ->
                               (forall x, ~ In x xs ->
                                     notin_stmt s x)) ->
                    meths_wf mths.

Inductive gFields_wf : ghost_fields -> Prop :=
| g_wf : forall gs, (forall g x e, gs g = Some (x, e) ->
                         (forall y, y <> x ->
                               y <> this ->
                               notin_exp e y)) ->
               gFields_wf gs.

Inductive cls_wf : classDef -> Prop :=
| cdef_wf : forall CDef, meths_wf (c_meths CDef) ->
                    gFields_wf (c_g_fields CDef) ->
                    cls_wf CDef.

Inductive M_wf : mdl -> Prop :=
| module_wf : forall M,  M Object = Some ObjectDefn ->
                    (forall C CDef, M C = Some CDef ->
                               c_name CDef = C) ->
                    (forall C CDef, M C = Some CDef ->
                               cls_wf CDef) ->
                    M_wf M.

Hint Constructors M_wf : loo_db.

Reserved Notation "M '∙' σ '⊢' e1 '↪' e2" (at level 40).

(** #<h3>#Expression evaluation (Fig 4, OOPSLA2019)#</h3>#  *)
Open Scope Z_scope.
Inductive evaluate : mdl -> config -> exp -> value -> Prop :=

(** M, σ true ↪ true     (True_Val) *)
(**| v_true     : forall M σ, M ∙ σ ⊢ e_true ↪ v_true*)

(** M, σ false ↪ false     (False_Val) *)
(**| v_false    : forall M σ, M ∙ σ ⊢ e_false ↪ v_false*)

(** M, σ null ↪ null     (Null_Val) *)
(**| v_null     : forall M σ, M ∙ σ ⊢ e_null ↪ v_null*)

(** This rule has been added to replace the original rules for values *)
(** i.e. Var_Value replaces Null_Val, False_Val, and True_Val, and *)
(** further extends the val to include evaluation of addresses *)
(** M, σ v ↪ v     (Var_Value) *)
| v_value     : forall M σ v, M ∙ σ ⊢ e_val v ↪ v

(** M, σ x ↪ σ(x)     (Var_Val) *)
| v_var      : forall M σ x v, mapp σ x = Some v ->
                          M ∙ σ ⊢ e_var x ↪ v

(** M, σ e.f() ↪ α *)
(** σ(α, f) = v*)
(** ---------------- (Field_Heap_Val) *)
(** M, σ ⊢ e.f ↪ v      *)
| v_f_heap   : forall M σ e f α o v, M ∙ σ ⊢ e ↪ (v_addr α) ->
                                mapp σ α = Some o ->
                                o.(flds) f = Some v ->
                                M ∙ σ ⊢ e_acc_f e f ↪ v


(** M, σ e0 ↪ α *)
(** M, σ e ↪ v *)
(** σ(α) = o *)
(** o has class C in M *)
(** G(M, Class(α, σ), f) = f(x) { e' } (note: the x here corresponds with the 0 in the Coq) *)
(** M, σ e ↪ v*)
(** M, σ [v/x]e' ↪ v'*)
(** ------------------------ (Field_Ghost_Val) *)
(** M, σ ⊢ e0.f(e) ↪ v'      *)
| v_f_ghost  : forall M σ e0 e f α o x e' v v' C,
    M ∙ σ ⊢ e0 ↪ (v_addr α) ->
    mapp σ α = Some o ->
    M o.(cname) = Some C ->
    C.(c_g_fields) f = Some (x, e') ->
    M ∙ σ ⊢ e ↪ v ->
    M ∙ (update_σ_map (update_σ_map σ x v) this (v_addr α)) ⊢ e' ↪ v' ->
    M ∙ σ ⊢ e_acc_g e0 f e ↪ v'

(** M, σ e ↪ true *)
(** M, σ e1 ↪ v *)
(** -------------------------------- (If_True_Val) *)
(** M, σ ⊢ if e then e1 else e2 ↪ v  *)
| v_if_true  : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ v_true ->
                                M ∙ σ ⊢ e1 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

(** M, σ e ↪ false *)
(** M, σ e2 ↪ v *)
(** -------------------------------- (If_False_Val) *)
(** M, σ ⊢ if e then e1 else e2 ↪ v  *)
| v_if_false : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ v_false -> 
                                M ∙ σ ⊢ e2 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

(** M, σ e1 ↪ v *)
(** M, σ e2 ↪ v *)
(** ------------------------- (Field_Heap_Val) *)
(** M, σ ⊢ e1 = e2 ↪ true *)
| v_equals   : forall M σ e1 e2 v, M ∙ σ ⊢ e1 ↪ v ->
                              M ∙ σ ⊢ e2 ↪ v ->
                              M ∙ σ ⊢ (e_eq e1 e2) ↪ v_true

(** M, σ e1 ↪ v1 *)
(** M, σ e2 ↪ v2 *)
(** v ≠ v' *)
(** ------------------------ (Field_Heap_Val) *)
(** M, σ ⊢ e1 = e2 ↪ false *)
| v_nequals  : forall M σ e1 e2 v1 v2, M ∙ σ ⊢ e1 ↪ v1 ->
                                  M ∙ σ ⊢ e2 ↪ v2 ->
                                  v1 <> v2 ->
                                  M ∙ σ ⊢ (e_eq e1 e2) ↪ v_false

| v_lt : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                            M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                            i1 < i2 ->
                            M ∙ σ ⊢ (e_lt e1 e2) ↪ v_true

| v_nlt : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                             M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                             ~ i1 < i2 ->
                             M ∙ σ ⊢ (e_lt e1 e2) ↪ v_false

| v_plus : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                              M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                              M ∙ σ ⊢ (e_plus e1 e2) ↪ (v_int (i1 + i2))

| v_minus : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                               M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                               M ∙ σ ⊢ (e_minus e1 e2) ↪ (v_int (i1 - i2))

| v_mult : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                              M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                              M ∙ σ ⊢ (e_mult e1 e2) ↪ (v_int (i1 * i2))

| v_div : forall M σ e1 e2 i1 i2, M ∙ σ ⊢ e1 ↪ (v_int i1) ->
                             M ∙ σ ⊢ e2 ↪ (v_int i2) ->
                             M ∙ σ ⊢ (e_div e1 e2) ↪ (v_int (i1 / i2))

where "M '∙' σ '⊢' e1 '↪' e2":= (evaluate M σ e1 e2).

Close Scope Z_scope.

Hint Constructors evaluate : loo_db.


(*Inductive dom {A B : Type}`{Eq A} : partial_map A B -> list A -> Prop :=
| d_empty : dom empty nil
| d_update1 : forall m a b d, dom m d ->
                         In a d ->
                         dom (update a b m) d
| d_update2 : forall m a b d, dom m d ->
                         ~ In a d ->
                         dom (update a b m) (a::d).

Hint Constructors dom.*)

Inductive unique {A : Type} `{Eq A} : list A -> Prop :=
| u_nil : unique nil
| u_con : forall a l, ~ In a l ->
                 unique l ->
                 unique (a :: l).

Hint Constructors unique : loo_db.

Definition dom {A B : Type}`{Eq A} (m : partial_map A B)(d : list A) : Prop :=
  (forall a b, m a = Some b ->
          In a d) /\
  (forall a, In a d ->
        exists b, m a = Some b) /\
  unique d.

(*Inductive dom {A B : Type}`{Eq A} : partial_map A B -> list A -> Prop :=
| d_dom : forall m d, (forall a b, m a = Some b ->
                         In a d) ->
                 (forall a, In a d ->
                       exists b, m a = Some b) ->
                 unique d ->
                 dom m d.*)

(** #<h3># Loo Operational Semantics (Fig 6, App A.2, OOPSLA2019):#</h3># *)

Reserved Notation "M '∙' σ '⤳' σ'" (at level 40).

Inductive le_α : addr -> addr -> Prop :=
| le_addr : forall n m, n <= m ->
                   le_α (address n) (address m).

Hint Constructors le_α : loo_db.

Definition S_α (α : addr) : addr :=
  match α with
  | address n => address (S n)
  end.

Inductive max_χ {B : Type} : partial_map addr B -> addr -> Prop :=
| max_heap : forall χ α, (exists b, χ α = Some b) ->
                    (forall α' b, χ α' = Some b ->
                             le_α α' α) ->
                    max_χ χ α.

Hint Constructors max_χ : loo_db.

Lemma max_χ_injective : forall b (χ : partial_map addr b) α α', max_χ χ α -> max_χ χ α' -> α = α'.
Proof.
  intros b χ α α' Hα Hα'.
  inversion Hα; subst. destruct H as [v Hαv].
  inversion Hα'; subst. destruct H as [v' Hα'v].
  apply H1 in Hαv as Hα'le. apply H0 in Hα'v as Hαle.
  inversion Hαle. inversion Hα'le. subst. 
  inversion H5. inversion H6. subst. crush.
Qed.

Inductive fresh_χ : heap -> addr -> Prop :=
| frsh_heap : forall χ α, max_χ χ α ->
                     fresh_χ χ (S_α α).

Hint Constructors fresh_χ : loo_db.

(** 
limiting expressions used in variable assignment to 
non-address, and non-access expressions.

Addresses: we don't want addresses, because we don't 
want programs to forge references to objects.

Access: because we don't want to inadvertently allow 
access to fields that shouldn't be able to be accessed
It is still possible to write expressions that use 
values stored in fields, the only restriction is that
the field has to be explicitly written to a local variable
first
*)

Inductive no_addr : exp -> Prop :=
| na_value : forall v, (forall α, v <> v_addr α) ->
                  no_addr (e_val v)
| na_var : forall x, no_addr (e_var x)
| na_hole : forall n, no_addr (e_hole n)
| na_eq : forall e1 e2, no_addr e1 ->
                   no_addr e2 ->
                   no_addr (e_eq e1 e2)
| na_plus : forall e1 e2, no_addr e1 ->
                     no_addr e2 ->
                     no_addr (e_plus e1 e2)
| na_minus : forall e1 e2, no_addr e1 ->
                      no_addr e2 ->
                      no_addr (e_minus e1 e2)
| na_mult : forall e1 e2, no_addr e1 ->
                     no_addr e2 ->
                     no_addr (e_mult e1 e2)
| na_div : forall e1 e2, no_addr e1 ->
                    no_addr e2 ->
                    no_addr (e_div e1 e2)
| na_if : forall e1 e2 e3, no_addr e1 ->
                      no_addr e2 ->
                      no_addr e3 ->
                      no_addr (e_if e1 e2 e3).

Fixpoint merge (s1 s2 : stmt) : stmt :=
  match s1 with
  | s ;; s' => s ;; (merge s' s2)
  | _ => s1 ;; s2
  end.

Inductive reduction : mdl -> config -> config -> Prop :=

    (** ϕ.contn = x:=y.m(ps); s' *)
    (** ⌊y⌋ϕ ≜ α*)
    (** ϕ' = ϕ❲contn ↦ x:=∙; s'❳ *)
    (** ϕ'' = (ps ∘ (ϕ.(varMap)), s) *)
    (** ------------------------------------ (Meth_Call_OS) *)
    (** M, σ ⤳ (χ, ϕ'' : ϕ' : ψ') *)
| r_mth : forall M ϕ ψ χ x y ps σ m zs α o s s' C ϕ' ϕ'',
    x <> this ->
    σ = (χ, ϕ :: ψ) ->
    ϕ.(contn) = c_stmt (s_stmts (s_meth x y m ps) s') ->
    (*finite ps ->*)
    ⌊ y ⌋ σ ≜ (v_addr α) ->
    χ α = Some o ->
    (M (o.(cname))) = Some C ->
    C.(c_meths) m = Some (zs, s) ->
    dom ps zs ->
    maps_into ps (vMap ϕ) ->
    ϕ' =  frm (vMap ϕ) (c_hole x s') ->
    ϕ'' = frm (update this (v_addr α) (ps ∘ (vMap ϕ))) (c_stmt s) ->
    M ∙ σ ⤳ (χ, ϕ'' :: (ϕ' :: ψ))

| r_eAssgn : forall M χ ϕ ψ x e v s,
    x <> this ->
    contn ϕ = (c_stmt (s_stmts (s_asgn (r_var x) (r_exp e)) s)) ->
    no_addr e ->
    M ∙ (χ, ϕ::ψ) ⊢ e ↪ v ->
    M ∙ (χ, ϕ::ψ) ⤳ (χ, (frm (update x v (vMap ϕ)) (c_stmt s))::ψ)

    (** x ≠ this *)
    (** σ = (χ, ψ)*)
    (** ψ = ϕ : _ *)
    (** ϕ.contn = x := y.f; s*)
    (** ⌊y⌋ϕ ≜ α*)
    (** Class(this) in σ = C *)
    (** Class(y) in σ = C *)
    (** χ(α) = o*)
    (** o.f = α' *)
    (** σ' = update σ with (x ↦ α) *)
    (** ------------------------------------ (Var_Assgn_OS) *)
    (** M, σ ⤳ σ' *)
| r_xAssgn : forall M σ ϕ x y f s ψ χ α v o ϕ' C,
    x <> this ->
    σ = (χ, ϕ :: ψ) ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_var x) (r_fld y f)) s)) ->
    ⌊ y ⌋ σ ≜ (v_addr α) ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    (flds o) f = Some v ->
    ϕ' = frm (update x v (vMap ϕ)) (c_stmt s) ->
    M ∙ σ ⤳ (χ, ϕ'::ψ)

    (** σ = (χ, ϕ : ψ') *)
    (** ϕ.contn = y.f := x; s*)
    (** χ(α) = C{ flds; mths } *)
    (** o' = C{ flds❲f ↦ α❳; mths } *)
    (** χ' = update χ with (α ↦ o') *)
    (** ϕ' = update ϕ with (contn ↦ s) *)
    (** σ' = (χ, ϕ' : ψ') *)
    (** ---------------------------------------- (Field_Assgn_OS) *)
    (** M, σ ⤳ σ' *)
| r_fAssgn : forall M σ ϕ ϕ' x y f s ψ χ α v o σ' χ' o' C,
    σ = (χ, ϕ :: ψ) ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_fld y f) (r_var x)) s)) ->
    ⌊ y ⌋ σ ≜ (v_addr α) ->
    ⌊ x ⌋ σ ≜ v ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    (exists v, (flds o) f = Some v) ->
    o' = new (cname o) (update f v (flds o))->
    χ' = update α o' χ ->
    ϕ' = frm (vMap ϕ) (c_stmt s) ->
    σ' = (χ', ϕ' :: ψ) ->
    M ∙ σ ⤳ σ'

    (** σ = (χ, ϕ : ψ) *)
    (** ϕ.contn = x := new C(...x_n); s *)
    (** α fresh in χ *)
    (** M C = CDef *)
    (** constructor(CDef) = constructor(...p_n) { Stmts' } *)
    (** ϕ'  = ϕ❲contn ↦ x:=∙; s'❳ *)
    (** o   = new C ()    (all class fields set to null to allow reassignment) *)
    (** ϕ'' = (Stmts'; return this, (this ↦ α, (...p_n ↦ ⌊x_n⌋) = ps ∘ xs)) *)
    (** σ'  = (update χ with (α ↦ o), ϕ'' : ϕ' : ψ') *)
    (** ------------------------------------------------ (objCreate_OS) *)
    (** M, σ ⤳ σ' *)
| r_new : forall M σ σ' χ ψ ϕ ϕ' ϕ'' α x C fMap zs s s' o CDef ps,
    x <> this ->                                              (* If the target is not `this` *)
    σ = (χ, ϕ :: ψ) ->                                        (* with configuration (χ, ϕ :: ψ) *)
    ϕ.(contn) = (c_stmt (s_stmts (s_new x C ps) s')) ->       (* Where new C(ps) is the next statement *)
    fresh_χ χ α ->                                            (* α is fresh in χ *)
    M C = Some CDef ->                                        (* M(C) = CDef = class { ... } *)
    (zs, s) = constructor CDef ->                             (* constructor(CDef) = constructor(zs) { s } *)
    (forall p x, ps p = Some x ->                             (* All variables passed in for a parameter *)
            exists v, (vMap ϕ) x = Some v) ->                 (*    exist in the variable map *)
    dom ps zs ->                                              (* ps = (z_1 ↦ p_1, ..., z_n ↦ p_n); the arguments match the constructor *)
    dom fMap (c_flds CDef) ->                                 (* let domain(fMap) = fields(CDef) *)
    (forall f x, fMap f = Some x -> x = v_null) ->            (* fMap maps to v_nil; fMap = (f_1 ↦ v_nil, ..., f_n ↦ v_nil) *)
    ϕ' = frm (vMap ϕ) (c_hole x s') ->                        (* ϕ' is ϕ with a hole assignment in place of the new *) (* was originally (update x (v_addr α) (vMap ϕ)) but this isn't right *)
    o = new C fMap ->                                         (* o = (C, fMap) *)
    ϕ'' = frm (update this (v_addr α) (ps ∘ (vMap ϕ))) (c_stmt (merge s (s_rtrn this))) -> (* ϕ'' = (this ↦ α, z_1 ↦ p_1 ↦ x_1, ...) *)
    σ' = (update α o χ, ϕ'' :: ϕ' :: ψ) ->                    (* End up with o at α in the heap, executing ϕ'', with ϕ' to come back to *)
    M ∙ σ ⤳ σ'
    

    (** σ = (χ, ϕ : ϕ' : ψ) *)
    (** ϕ.contn = return x *)
    (** ϕ'.contn = y := ∙; s *)
    (** ⌊ x ⌋ σ ≜ α *)
    (** ϕ'' = update (ϕ') with (y ↦ α) and (contn ↦ s) *)
    (** ----------------------------------------------------- (Return_OS_1) *)
    (** M, σ ⤳ (χ, ϕ'' : ψ *)

| r_if1 : forall M χ ϕ ψ e s1 s2 s,
    contn ϕ = c_stmt ((s_if e s1 s2) ;; s) ->
    M ∙ (χ, ϕ::ψ) ⊢ e ↪ v_true ->
    M ∙ (χ, ϕ::ψ) ⤳ (χ, (frm (vMap ϕ) (c_stmt (merge s1 s)))::ψ)

| r_if2 : forall M χ ϕ ψ e s1 s2 s,
    contn ϕ = c_stmt ((s_if e s1 s2) ;; s) ->
    M ∙ (χ, ϕ::ψ) ⊢ e ↪ v_false ->
    M ∙ (χ, ϕ::ψ) ⤳ (χ, (frm (vMap ϕ) (c_stmt (merge s2 s)))::ψ)

| r_ret1 : forall M ϕ ϕ' ψ χ y x α ϕ'' σ s,
    σ = (χ, ϕ :: (ϕ' :: ψ)) ->
    ϕ.(contn) = c_stmt (s_rtrn x) ->
    ϕ'.(contn) = c_hole y s ->
    y <> this ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y α) (c_stmt s)->
    M ∙ σ ⤳ (χ, ϕ'' :: ψ)

    (** σ = (χ, ϕ : ϕ' : ψ'') *)
    (** ϕ.contn = return x; s' *)
    (** ϕ'.contn = y := ∙; s *)
    (** ⌊ x ⌋ σ ≜ α *)
    (** ϕ'' = update (ϕ') with (y ↦ α) and (contn ↦ s) *)
    (** --------------------------------------------------- (Return_OS_2) *)
    (** M, σ ⤳ (χ, ϕ'', ψ) *)
| r_ret2 : forall M ϕ ϕ' ψ χ y x α ϕ'' σ s s',
    σ = (χ, ϕ :: ϕ' :: ψ) ->
    ϕ.(contn) = c_stmt (s_stmts (s_rtrn x) s') ->
    ϕ'.(contn) = c_hole y s ->
    y <> this ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y α) (c_stmt s)->
    M ∙ σ ⤳ (χ, ϕ'' :: ψ)

where "M '∙' σ '⤳' σ'" := (reduction M σ σ').

Hint Constructors reduction : loo_db.

Reserved Notation "M1 '⋄' M2 '≜' M" (at level 40).

Inductive link : mdl -> mdl -> mdl -> Prop :=
| m_link : forall M1 M2, (forall C def, C <> Object ->
                              M1 C = Some def ->
                              M2 C = None) ->
                    (forall C def, C <> Object ->
                              M2 C = Some def ->
                              M1 C = None) ->
                    M1 ⋄ M2 ≜ (M1 ∪ M2)

where "M1 '⋄' M2 '≜' M" := (link M1 M2 M).

(*
  reductions: a helper definition that allows for the definition of pair
  evaluation
*)
(*
  unfortunately there is some abiguity with notation, so I am 
  having trouble maintaining consitent notation and using 
  '∙' in the reductions and pair reductions definitions
*)
(*Reserved Notation "M1 '∩' M2 '⊢' σ '⤳⋆' σ'" (at level 40).
                                               
Inductive reductions : mdl -> mdl -> config -> config -> Prop :=
| r_reduce : forall M1 M2 M σ σ', M1 ∘ M2 ≜ M ->
                             M ∙ σ ⤳ σ' ->
                             (forall C, classOf this σ' C ->
                                   exists Cdef, M1 C = Some Cdef) ->
                             M1 ∩ M2 ⊢ σ ⤳⋆ σ'

| r_trans : forall M1 M2 M σ σ1 σ2, M1 ∘ M ≜ M ->
                               M1 ∩ M2 ⊢ σ ⤳⋆ σ2 ->
                               M ∙ σ1 ⤳ σ2 ->
                               (forall C, classOf this σ2 C ->
                                     exists Cdef, M1 C = Some Cdef) ->
                               M1 ∩ M2 ⊢ σ ⤳⋆ σ2

where "M1 '∩'  M2 '⊢' σ '⤳⋆' σ'" := (reductions M1 M2 σ σ').
*)

Definition is_internal (M1 M2 : mdl)(σ : config)(x : var) :=
  (exists α o CDef, ⟦ x ↦ (v_addr α) ⟧ ∈ σ /\
               ⟦ α ↦ o ⟧ ∈ σ /\
               M1 (cname o) = Some CDef).

Definition is_external (M1 M2 : mdl)(σ : config)(x : var) :=
  (exists α o, ⟦ x ↦ (v_addr α) ⟧ ∈ σ /\
          ⟦ α ↦ o ⟧ ∈ σ /\
          M1 (cname o) = None).

Definition internal_self (M1 M2 : mdl)(σ : config) :=
  is_internal M1 M2 σ this.

Definition external_self (M1 M2 : mdl)(σ : config) :=
  is_external M1 M2 σ this.

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

where "M1 '⦂' M2 '⦿' σ '⤳…' σ'" := (internal_reductions M1 M2 σ σ').

Hint Constructors internal_reductions : loo_db.

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

where "M1 '⦂' M2 '⦿' σ '⤳' σ'" := (pair_reduction M1 M2 σ σ').

Hint Constructors pair_reduction : loo_db.

Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" (at level 40).

Inductive pair_reductions : mdl -> mdl -> config -> config -> Prop :=
| prs_single : forall M1 M2 σ1 σ2, M1 ⦂ M2 ⦿ σ1 ⤳ σ2 ->
                              M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2
                                 
| prs_trans : forall M1 M2 σ1 σ σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ ->
                               M1 ⦂ M2 ⦿ σ ⤳ σ2 ->
                               M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2

where "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" := (pair_reductions M1 M2 σ σ').

Hint Constructors pair_reductions : loo_db.

Definition stack_append (σ : config)(ψ : stack):=
  (fst σ, (snd σ)++ψ).

Notation "σ '◁' ψ" := (stack_append σ ψ)(at level 40).

Definition constrained_pair_reduction (M1 M2 : mdl)(σ1 σ2 : config):=
  exists χ ϕ ψ σ, σ1 = (χ, ϕ :: ψ) /\
             M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳ σ /\
             σ2 = (σ ◁ ψ).

Notation "M1 '⦂' M2 '⦿' σ1 '⌈⤳⌉' σ2":=
  (constrained_pair_reduction M1 M2 σ1 σ2)(at level 40).

Definition constrained_pair_reductions (M1 M2 : mdl)(σ1 σ2 : config):=
  exists χ ϕ ψ σ, σ1 = (χ, ϕ :: ψ) /\
             M1 ⦂ M2 ⦿ (χ, ϕ :: nil) ⤳⋆ σ /\
             σ2 = (σ ◁ ψ).

Notation "M1 '⦂' M2 '⦿' σ1 '⌈⤳⋆⌉' σ2":=
  (constrained_pair_reductions M1 M2 σ1 σ2)(at level 40).

Class Rename (A : Type) :=
  {rname : (partial_map var var) -> A -> A;
   empty_rename : forall a, rname empty a = a
  }.

Notation "'❲' f '↦' a '❳'" := (rname f a)(at level 40).

Program Instance varRename : Rename var :=
  {
    rname f x := match (f x) with
                 | Some y => y
                 | _ => x
                 end;
  }.

Hint Rewrite (@empty_rename var) : map_db.
Hint Resolve (@empty_rename var) : map_db.

Program Instance expRename : Rename exp :=
  {
  rname :=
    fix rname' f e :=
      match e with
      | e_var x => e_var (❲f ↦ x❳)
      | e_eq e1 e2 => e_eq (rname' f e1) (rname' f e2)
      | e_plus e1 e2 => e_plus (rname' f e1) (rname' f e2)
      | e_minus e1 e2 => e_minus (rname' f e1) (rname' f e2)
      | e_mult e1 e2 => e_mult (rname' f e1) (rname' f e2)
      | e_div e1 e2 => e_div (rname' f e1) (rname' f e2)
      | e_if e1 e2 e3 => e_if (rname' f e1) (rname' f e2) (rname' f e3)
      | e_acc_f e' f' => e_acc_f (rname' f e') f'
      | e_acc_g e1 g e2 => e_acc_g (rname' f e1) g (rname' f e2)
      | _ => e
      end
  }.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  crush.
Defined.
Next Obligation.
  induction a; simpl; crush.
Defined.

Hint Rewrite (@empty_rename exp) : map_db.
Hint Resolve (@empty_rename exp) : map_db.

Program Instance refRename : Rename ref :=
  {
  rname f r := match r with
               | r_exp e => r_exp (❲f ↦ e❳)
               | r_var x => r_var (❲f ↦ x❳)
               | r_fld x f' => r_fld (❲f ↦ x❳) f'
               end
  }.
Next Obligation.
  destruct a; auto.
  assert (Hrname : rname empty e = e);
    [auto with map_db
    |unfold rname in Hrname;
     simpl in Hrname;
     rewrite Hrname; auto].
Defined.

Hint Rewrite (@empty_rename ref) : map_db.
Hint Resolve (@empty_rename ref) : map_db.

Program Instance fldMapRename : Rename (partial_map fld var) :=
  {
    rname f m := (fun f' => bind (m f') (fun x => Some (❲ f ↦ x ❳)))
  }.
Next Obligation.
  intros.
  apply functional_extensionality;
    intros f.
  unfold bind; simpl; auto.
  destruct (a f); auto.
Qed.

Hint Rewrite (@empty_rename (partial_map fld var)) : map_db.
Hint Resolve (@empty_rename (partial_map fld var)) : map_db.

Program Instance varMapRename : Rename (partial_map var var) :=
  {
    rname f m := (fun x => bind (m x) (fun x => Some (❲ f ↦ x ❳)))
  }.
Next Obligation.
  intros.
  apply functional_extensionality;
    intros x.
  unfold bind; simpl.
  destruct (a x); auto.
Qed.

Hint Rewrite (@empty_rename (partial_map var var)) : map_db.
Hint Resolve (@empty_rename (partial_map var var)) : map_db.

Lemma map_wrap_id :
  forall {A B : Type}`{Eq A}(f : partial_map A B),
    (fun x => match f x with
           | Some y => Some y
           | None => None end) = f.
Proof.
  intros A B Heq f;
    apply functional_extensionality;
    intros a.
  destruct (f a); auto.
Qed.

Hint Rewrite (@map_wrap_id var var) : map_db.

Program Instance stmtRename : Rename stmt :=
  {
  rname :=
    fix rname' f s :=
      match s with
      | s_asgn r1 r2 => s_asgn (❲f ↦ r1❳) (❲f ↦ r2❳)
      | s_meth x y m' pMap => s_meth (❲f ↦ x❳)  (❲f ↦ y❳) m' (❲f ↦ pMap❳)
      | s_new x C fMap => s_new (❲f ↦ x❳) C (❲f ↦ fMap❳)
      | s_if e s1 s2 => s_if (❲f ↦ e❳) (rname' f s1) (rname' f s2)
      | s_stmts s1 s2 => s_stmts (rname' f s1) (rname' f s2)
      | s_rtrn x => s_rtrn (❲f ↦ x❳)
      end
  }.
Next Obligation.
  induction a;
    auto.

  - destruct r, r0; simpl in *; auto;
      try solve [assert (Hrname : rname empty e = e);
                 [apply empty_rename
                 |unfold rname in Hrname;
                  simpl in Hrname;
                  rewrite Hrname];
                 reflexivity].
    + assert (Hrname : rname empty e = e);
        [apply empty_rename
        |unfold rname in Hrname;
         simpl in Hrname;
         rewrite Hrname].
      assert (Hrname0 : rname empty e0 = e0);
        [apply empty_rename
        |unfold rname in Hrname0;
         simpl in Hrname0;
         rewrite Hrname0].
      reflexivity.
  - destruct v, v0; simpl in *; eauto.
    rewrite map_wrap_id; auto.
  - destruct v; simpl in *; eauto.
    rewrite map_wrap_id; auto.
  - fold rname in *.
    assert (Hrname : rname empty e = e);
      [apply empty_rename
      |unfold rname in Hrname;
       simpl in Hrname;
       rewrite Hrname].
    destruct a1, a2; simpl in *; crush.
  - destruct a1, a2;
      simpl in *;
      crush.
Defined.
Hint Rewrite (@empty_rename stmt) : map_db.
Hint Resolve (@empty_rename stmt) : map_db.

Hint Rewrite empty_rename : map_db.
Hint Resolve empty_rename : map_db.

Inductive in_exp : var -> exp -> Prop :=
| in_var : forall x, in_exp x (e_var x)
| in_eq1 : forall x e1 e2, in_exp x e1 ->
                      in_exp x (e_eq e1 e2)
| in_eq2 : forall x e1 e2, in_exp x e2 ->
                      in_exp x (e_eq e1 e2)
| in_lt1 : forall x e1 e2, in_exp x e1 ->
                      in_exp x (e_eq e1 e2)
| in_lt2 : forall x e1 e2, in_exp x e2 ->
                      in_exp x (e_eq e1 e2)
| in_plus1 : forall x e1 e2, in_exp x e1 ->
                        in_exp x (e_plus e1 e2)
| in_plus2 : forall x e1 e2, in_exp x e2 ->
                        in_exp x (e_plus e1 e2)
| in_minus1 : forall x e1 e2, in_exp x e1 ->
                         in_exp x (e_minus e1 e2)
| in_minus2 : forall x e1 e2, in_exp x e2 ->
                         in_exp x (e_minus e1 e2)
| in_mult1 : forall x e1 e2, in_exp x e1 ->
                        in_exp x (e_mult e1 e2)
| in_mult2 : forall x e1 e2, in_exp x e2 ->
                        in_exp x (e_mult e1 e2)
| in_div1 : forall x e1 e2, in_exp x e1 ->
                       in_exp x (e_div e1 e2)
| in_div2 : forall x e1 e2, in_exp x e2 ->
                       in_exp x (e_div e1 e2)
| in_if1 : forall x e1 e2 e3, in_exp x e1 ->
                         in_exp x (e_if e1 e2 e3)
| in_if2 : forall x e1 e2 e3, in_exp x e2 ->
                         in_exp x (e_if e1 e2 e3)
| in_if3 : forall x e1 e2 e3, in_exp x e3 ->
                         in_exp x (e_if e1 e2 e3)
| in_acc_f : forall x e f, in_exp x e ->
                      in_exp x (e_acc_f e f)
| in_acc_g1 : forall x e1 g e2, in_exp x e1 ->
                           in_exp x (e_acc_g e1 g e2)
| in_acc_g2 : forall x e1 g e2, in_exp x e2 ->
                           in_exp x (e_acc_g e1 g e2).

Inductive in_ref : var -> ref -> Prop :=
| in_r_exp : forall x e, in_exp x e ->
                    in_ref x (r_exp e)
| in_r_var : forall x, in_ref x (r_var x)
| in_r_fld : forall x f, in_ref x (r_fld x f).

Inductive in_stmt : var -> stmt -> Prop :=
| in_asgn_1 : forall x y z, in_ref x y ->
                       in_stmt x (s_asgn y z)
| in_asgn_2 : forall x y z, in_ref x z ->
                       in_stmt x (s_asgn y z)
| in_meth_1 : forall x y m ps, in_stmt x (s_meth x y m ps)
| in_meth_2 : forall x y m ps, in_stmt y (s_meth x y m ps)
| in_meth_3 : forall x y z m ps, (exists x', ps x' = Some z) ->
                            in_stmt z (s_meth x y m ps)
| in_new_1 : forall x C ps, in_stmt x (s_new x C ps)
| in_new_2 : forall x y C ps, (exists z, ps z = Some y) ->
                         in_stmt y (s_new x C ps)
| in_sif1 : forall x e s1 s2, in_exp x e ->
                         in_stmt x (s_if e s1 s2)
| in_sif2 : forall x e s1 s2, in_stmt x s1 ->
                         in_stmt x (s_if e s1 s2)
| in_sif3 : forall x e s1 s2, in_stmt x s2 ->
                         in_stmt x (s_if e s1 s2)
| in_stmts_1 : forall x s1 s2, in_stmt x s1 ->
                          in_stmt x (s_stmts s1 s2)
| in_stmts_2 : forall x s1 s2, in_stmt x s2 ->
                          in_stmt x (s_stmts s1 s2)
| in_retrn : forall x, in_stmt x (s_rtrn x).

Hint Constructors in_ref in_stmt : loo_db.
