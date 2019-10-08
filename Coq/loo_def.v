Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.

Inductive fld : Type := fieldID : nat -> fld.

Inductive mth : Type := methID : nat -> mth.

Inductive gfld : Type := gFieldID : nat -> gfld.

Inductive cls : Type := classID : nat -> cls.

Inductive addr : Type := address : nat -> addr.

Inductive value : Type :=
| v_true  : value
| v_false : value
| v_null  : value
| v_addr   : addr -> value.

Definition state := partial_map var value.

Instance eqbFld : Eqb fld :=
  {
    eqb := fun f1 f2 =>
             match f1, f2 with
             | fieldID n1, fieldID n2 => n1 =? n2
             end
  }.

Instance eqbMth : Eqb mth :=
  {
    eqb := fun m1 m2 =>
             match m1, m2 with
             | methID n1, methID n2 => n1 =? n2
             end
  }.

Instance eqbGfld : Eqb gfld :=
  {
    eqb := fun g1 g2 =>
             match g1, g2 with
             | gFieldID n1, gFieldID n2 => n1 =? n2
             end
  }.

Instance eqbCls : Eqb cls :=
  {
    eqb := fun C1 C2 =>
             match C1, C2 with
             | classID n1, classID n2 => n1 =? n2
             end
  }.

Instance eqbAddr : Eqb addr :=
  {
    eqb := fun a1 a2 =>
             match a1, a2 with
             | address n1, address n2 => n1 =? n2
             end
  }.

(*this is a bit of a hack*)
Definition this := bind 0.

(*fields are a mapping from field names to locations in the heap*)
Definition fields := partial_map fld value.

Inductive ref : Type :=
| r_var : var -> ref
| r_fld : var -> fld -> ref.

Inductive stmt : Type :=
| s_asgn : ref -> ref -> stmt
| s_meth : var -> var -> mth -> partial_map var var -> stmt
| s_new  : var -> cls -> partial_map fld var -> stmt
| s_stmts : stmt -> stmt -> stmt
| s_rtrn : var -> stmt.

Inductive continuation : Type :=
| c_stmt : stmt -> continuation
| c_hole : var -> stmt -> continuation.

Inductive exp : Type :=
| e_val   : value -> exp
| e_var   : var -> exp
| e_hole  : nat -> exp
| e_eq    : exp -> exp -> exp
| e_if    : exp -> exp -> exp -> exp
| e_acc_f : exp -> fld -> exp
| e_acc_g : exp -> gfld -> exp -> exp.

Notation "'e_true'" := (e_val v_true)(at level 40).
Notation "'e_false'" := (e_val v_false)(at level 40).
Notation "'e_null'" := (e_val v_null)(at level 40).
Notation "'e_addr' r" := (e_val (v_addr r))(at level 40).

(*methods is a mapping from method names to statements*)
Definition methods := partial_map mth stmt.

(*ghost_fields is a mapping from ghost field names to expressions*)
Definition ghost_fields := partial_map gfld (var * exp).

Record classDef := clazz{c_name : cls;
                         c_flds : list fld;
                         c_meths : methods;
                         c_g_fields: ghost_fields}.

Record obj := new{cname : cls;
                  flds : fields;
                  meths : methods}.

Definition mdl := partial_map cls classDef.

Definition heap := partial_map addr obj.

Record frame := frm{vMap : state;
                    contn : continuation}.

Definition stack := list frame.

(*Inductive stack :=
| base : stack
| scons : frame -> stack -> stack.*)

Definition peek (ψ : stack) : option frame :=
  match ψ with
  | nil => None
  | ϕ :: _ => Some ϕ
  end.

Definition pop (ψ : stack) : option stack :=
  match ψ with
  | nil => None
  | _ :: ψ => Some ψ
  end.

Instance stackMap : Mappable stack var (option value) :=
  {map :=
     fix map S x :=
       match S with
       | nil => None
       | ϕ :: S' => ϕ.(vMap) x
       end
  }.

Definition config : Type := (heap * stack).

Instance configMapHeap : Mappable config addr (option obj) :=
  {map σ α := (fst σ) α}.

Instance configMapStack : Mappable config var (option value) :=
  {map σ x := map (snd σ) x}.

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

Inductive interpret_x : var -> config -> addr -> Prop :=
| int_x : forall x σ ψ ϕ α, snd σ = ψ ->
                       peek ψ = Some ϕ ->
                       (vMap ϕ) x = Some (v_addr α) -> 
                       ⌊ x ⌋ σ ≜ α
where "'⌊' x '⌋' σ '≜' α" := (interpret_x x σ α).
  
Inductive interpret_Σ : list var -> config -> list addr -> Prop :=
| int_nil  : forall σ, ⌊ nil ⌋ σ ≜′ nil
| int_cons : forall x Σ σ α αs, ⌊ x ⌋ σ ≜ α ->
                           ⌊ Σ ⌋ σ ≜′ αs ->
                           ⌊ x::Σ ⌋ σ ≜′ (α::αs)
where "'⌊' Σ '⌋' σ '≜′' αs" := (interpret_Σ Σ σ αs).

Reserved Notation "σ1 '↓' Σ '≜' σ2" (at level 80).

Inductive restrict : config -> list var -> config -> Prop :=
| rstrct : forall Σ σ As χ χ', ⌊ Σ ⌋ σ ≜′ As ->
                          (forall α o, χ' α = Some o ->
                                  χ α = Some o) ->
                          (forall α o, χ' α = Some o ->
                                  In α As) ->
                          (forall α o, In α As ->
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
|cls_of : forall x σ α χ o C, ⌊ x ⌋ σ ≜ α ->
                         fst σ = χ ->
                         χ α = Some o ->
                         cname o = C ->
                         classOf x σ C.

Reserved Notation "M '∙' σ '⊢' e1 '↪' e2" (at level 40).

(** #<h3>#Expression evaluation (Fig 4, OOPSLA2019)#</h3>#  *)

Inductive val : mdl -> config -> exp -> value -> Prop :=

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
| v_var      : forall M σ x v, map σ x = Some v ->
                          M ∙ σ ⊢ e_var x ↪ v

(** M, σ e.f() ↪ α *)
(** σ(α, f) = v*)
(** ---------------- (Field_Heap_Val) *)
(** M, σ ⊢ e.f ↪ v      *)
| v_f_heap   : forall M σ e f α o v, M ∙ σ ⊢ e ↪ (v_addr α) ->
                                map σ α = Some o ->
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
| v_f_ghost  : forall M σ e0 e f α o x e' v v' C, M ∙ σ ⊢ e0 ↪ (v_addr α) ->
                                             map σ α = Some o ->
                                             M o.(cname) = Some C ->
                                             C.(c_g_fields) f = Some (x, e') ->
                                             M ∙ σ ⊢ e ↪ v ->
                                             M ∙ (update_σ_map σ x v) ⊢ e' ↪ v' ->
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

where "M '∙' σ '⊢' e1 '↪' e2":= (val M σ e1 e2).

(** #<h3># Loo Operational Semantics (Fig 6, App A.2, OOPSLA2019):#</h3># *)

Reserved Notation "M '∙' σ '⤳' σ'" (at level 40).

Inductive reduction : mdl -> config -> config -> Prop :=

    (** ϕ.contn = x:=y.m(ps); s' *)
    (** ⌊y⌋ϕ ≜ α*)
    (** ϕ' = ϕ❲contn ↦ x:=∙; s'❳ *)
    (** ϕ'' = (ps ∘ (ϕ.(varMap)), s) *)
    (** ------------------------------------ (Meth_Call_OS) *)
    (** M, σ ⤳ (χ, ϕ'' : ϕ' : ψ') *)
| r_mth : forall M ϕ ψ ψ' χ x y ps σ m α o s s' C ϕ' ϕ'',
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    pop ψ = Some ψ' ->
    ϕ.(contn) = c_stmt (s_stmts (s_meth x y m ps) s') ->
    ⌊ y ⌋ σ ≜ α ->
    χ α = Some o ->
    (M (o.(cname))) = Some C ->
    C.(c_meths) m = Some s ->
    ϕ' =  frm (vMap ϕ) (c_hole x s') ->
    ϕ'' = frm (update this (v_addr α) (compose ps (vMap ϕ))) (c_stmt s) ->
    M ∙ σ ⤳ (χ, ϕ'' :: (ϕ' :: (ψ')))

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
| r_vAssgn : forall M σ ϕ x y f s ψ χ α v o σ' C,
    x <> this ->
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_var x) (r_fld y f)) s)) ->
    ⌊ y ⌋ σ ≜ α ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    (flds o) f = Some v ->
    σ' = update_σ_map σ x v ->
    M ∙ σ ⤳ σ'

    (** σ = (χ, ϕ : ψ') *)
    (** ϕ.contn = y.f := x; s*)
    (** χ(α) = C{ flds; mths } *)
    (** o' = C{ flds❲f ↦ α❳; mths } *)
    (** χ' = update χ with (α ↦ o') *)
    (** ϕ' = update ϕ with (contn ↦ s) *)
    (** σ' = (χ, ϕ' : ψ') *)
    (** ---------------------------------------- (Field_Assgn_OS) *)
    (** M, σ ⤳ σ' *)
| r_fAssgn : forall M σ ϕ ϕ' x y f s ψ ψ' χ α α' o σ' χ' o' C,
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    pop ψ = Some ψ' ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_fld y f) (r_var x)) s)) ->
    ⌊ y ⌋ σ ≜ α ->
    ⌊ x ⌋ σ ≜ α' ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    o' = new (cname o) (update f (v_addr α') (flds o)) (meths o) ->
    χ' = update α o' χ ->
    ϕ' = frm (vMap ϕ) (c_stmt s) ->
    σ' = (χ', ϕ' :: ψ') ->
    M ∙ σ ⤳ σ'

    (** ψ = ϕ : ψ' *)
    (** ϕ.contn = x := new C(fMap); s *)
    (** M C = CDef *)
    (** dom(fMap) = flds of C *)
    (** ϕ' = update ϕ with (x ↦ α) and (contn ↦ s)*)
    (** σ' = (update χ with (α ↦ o), ϕ' : ψ') *)
    (** ------------------------------------------------ (objCreate_OS) *)
    (** M, σ ⤳ σ' *)
| r_new : forall M σ σ' χ ψ ψ' ϕ ϕ' α x C fMap s o CDef,
    σ = (χ, ψ) ->
    pop ψ = Some ψ' ->
    peek ψ = Some ϕ ->
    ϕ.(contn) = (c_stmt (s_stmts (s_new x C fMap) s)) ->
    χ α = None ->
    M C = Some CDef ->
    (forall f y, fMap f = Some y ->
            In f (c_flds CDef)) ->
    (forall f, fMap f = None ->
          ~ In f (c_flds CDef)) ->
    o = new C (compose fMap (vMap ϕ)) (c_meths CDef) ->
    ϕ' = frm (update x (v_addr α) (vMap ϕ)) (c_stmt s) ->
    σ' = (update α o χ, ϕ' :: ψ') ->
    M ∙ σ ⤳ σ'
    

    (** σ = (χ, ϕ : ϕ' : ψ) *)
    (** ϕ.contn = return x *)
    (** ϕ'.contn = y := ∙; s *)
    (** ⌊ x ⌋ σ ≜ α *)
    (** ϕ'' = update (ϕ') with (y ↦ α) and (contn ↦ s) *)
    (** ----------------------------------------------------- (Return_OS_1) *)
    (** M, σ ⤳ (χ, ϕ'' : ψ *)
| r_ret1 : forall M ϕ ϕ' ψ χ y x α ϕ'' σ s,
    σ = (χ, ϕ :: (ϕ' :: ψ)) ->
    ϕ.(contn) = c_stmt (s_rtrn x) ->
    ϕ'.(contn) = c_hole y s ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y (v_addr α)) (c_stmt s)->
    M ∙ σ ⤳ (χ, ϕ'' :: ψ)

    (** σ = (χ, ϕ : ϕ' : ψ'') *)
    (** ϕ.contn = return x; s' *)
    (** ϕ'.contn = y := ∙; s *)
    (** ⌊ x ⌋ σ ≜ α *)
    (** ϕ'' = update (ϕ') with (y ↦ α) and (contn ↦ s) *)
    (** --------------------------------------------------- (Return_OS_2) *)
    (** M, σ ⤳ (χ, ϕ'', ψ) *)
| r_ret2 : forall M ϕ ϕ' ψ ψ' ψ'' χ y x α ϕ'' σ s s',
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    pop ψ = Some ψ' ->
    peek ψ' = Some ϕ' ->
    pop ψ' = Some ψ'' ->
    ϕ.(contn) = c_stmt (s_stmts (s_rtrn x) s') ->
    ϕ'.(contn) = c_hole y s ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y (v_addr α)) (c_stmt s)->
    M ∙ σ ⤳ (χ, ϕ'' :: ψ)

where "M '∙' σ '⤳' σ'" := (reduction M σ σ').

Reserved Notation "M1 '∘' M2 '≜' M" (at level 40).

Inductive link : mdl -> mdl -> mdl -> Prop :=
| m_link : forall M1 M2 M, (forall C def, M1 C = Some def ->
                                M2 C = None) ->
                      (forall C def, M2 C = Some def ->
                                M1 C = None) ->
                      (forall C def, M1 C = Some def ->
                                M C = Some def) ->
                      (forall C def, M2 C = Some def ->
                                M C = Some def) ->
                      (forall C, M C = None ->
                            M1 C = None) ->
                      (forall C, M C = None ->
                            M2 C = None) ->
                      M1 ∘ M2 ≜ M

where "M1 '∘' M2 '≜' M" := (link M1 M2 M).

(*
  reductions: a helper definition that allows for the definition of pair
  evaluation
*)
(*
  unfortunately there is some abiguity with notation, so I am 
  having trouble maintaining consitent notation and using 
  '∙' in the reductions and pair reductions definitions
*)
Reserved Notation "M1 '∩' M2 '⊢' σ '⤳⋆' σ'" (at level 40).
                                               
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

Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳' σ'" (at level 40).
                                               
Inductive pair_reduction : mdl -> mdl -> config -> config -> Prop :=
| pr_single : forall M1 M2 M σ σ', M1 ∘ M2 ≜ M ->
                              M ∙ σ ⤳ σ' ->
                              (forall C, classOf this σ C ->
                                    M1 C = None) ->
                              (forall C, classOf this σ' C ->
                                    M1 C = None) ->                             
                              M1 ⦂ M2 ⦿ σ ⤳ σ'

| pr_trans : forall M1 M2 M σ1 σ σn, M1 ∩ M2 ⊢ σ1 ⤳⋆ σ ->
                                M1 ∘ M2 ≜ M ->
                                M ∙ σ ⤳ σn ->
                                M1 ⦂ M2 ⦿ σ1 ⤳ σn                            

where "M1 '⦂' M2 '⦿' σ '⤳' σ'" := (pair_reduction M1 M2 σ σ').

Reserved Notation "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" (at level 40).
                                               
Inductive pair_reductions : mdl -> mdl -> config -> config -> Prop :=
| prs_single : forall M1 M2 σ σ', M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                             M1 ⦂ M2 ⦿ σ ⤳⋆ σ'

| prs_trans : forall M1 M2 σ1 σ σ2, M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ ->
                               M1 ⦂ M2 ⦿ σ ⤳ σ2 ->
                               M1 ⦂ M2 ⦿ σ1 ⤳⋆ σ2

where "M1 '⦂' M2 '⦿' σ '⤳⋆' σ'" := (pair_reductions M1 M2 σ σ').

Class Rename (A : Type) :=
  {rname : A -> var -> var -> A
  }.

Notation "'❲' n '↦' m '❳' a" := (rname a n m)(at level 40).

Instance varRename : Rename var :=
  {
    rname := fun x y z =>
              if eqb x y
              then z
              else x    
  }.

Instance refRename : Rename ref :=
  {
    rname := fun r n m =>
              match r with
              | r_var x => r_var (❲n ↦ m❳ x)
              | r_fld x f => r_fld (❲n ↦ m❳ x) f
              end
  }.

Definition remap {A B : Type} `{Eqb A} `{Eqb B}
           (b1 b2 : B) (pmap : partial_map A B) : partial_map A B :=
  fun a => match pmap a with
        | Some b => if (eqb b b1)
                   then Some b2
                   else Some b
        | _ => pmap a
        end.

Instance fldMapRename : Rename (partial_map fld var) :=
  {
    rname map n m := remap n m map
  }.

Instance varMapRename : Rename (partial_map var var) :=
  {
    rname map n m := remap n m map
  }.

(*this is not possible using remap, because it requires <> to be
  extensional, but it is syntactically based in Coq*)
(*Instance mapRename : Subst (partial_map nat nat) nat :=
  {
    sbst map x y := remap x y map;

    closed map x := forall n y, map n = Some y ->
                           y <> x
  }.
Proof.
  intros.
  
  
Qed.*)


(*as a result of the extenstionality issue with maps,
 this means that substitution of stmts does not observe the
 closed property ...*)
(*Instance stmtSubst : Subst stmt nat :=
  {
    sbst := fun s n m =>
              match s with
              | s_asgn r1 r2 => s_asgn ([m /s n] r1) ([m /s n] r2)
              | s_meth x y m' pMap => s_meth ([m /s n] x)  ([m /s n] y) m' (pMap)
              | s_new x C fMap => s_new ([m /s n] x) C fMap
              | s_stmts s1 s2 => s_stmts s1 s2
              | s_rtrn _ => s
              end
                
  }.*)


Instance stmtRename : Rename stmt :=
  {
    rname := fix rname' s n m :=
             match s with
             | s_asgn r1 r2 => s_asgn (❲m ↦ n❳ r1) (❲m ↦ n❳ r2)
             | s_meth x y m' pMap => s_meth (❲m ↦ n❳ x)  (❲m ↦ n❳ y) m' (❲m ↦ n❳ pMap)
             | s_new x C fMap => s_new (❲m ↦ n❳ x) C (❲m ↦ n❳ fMap)
             | s_stmts s1 s2 => s_stmts (rname' s1 n m) (rname' s2 n m)
             | s_rtrn _ => s
             end
  }.

