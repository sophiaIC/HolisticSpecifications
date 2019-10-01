Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.

Definition fld := nat.

Definition mth := nat.

Definition gfld := nat.

Definition cls := nat.

Definition state := partial_map nat nat.

(*this is a bit of a hack*)
Definition this := 0.

 (*fields are a mapping from field names to locations in the heap*)
Definition fields := partial_map fld nat.

(*term is not used*)
Inductive term : Type :=
| t_var  : var -> term
| t_new  : cls -> list nat -> term
| t_fld  : term -> fld -> term
| t_mth  : term -> mth -> term -> term
| t_hole : term.

Inductive ref : Type :=
| r_var : nat -> ref
| r_fld : nat -> fld -> ref. (*should this be ref -> fld -> ref?*)

Inductive stmt : Type :=
| s_asgn : ref -> ref -> stmt
| s_meth : nat -> nat -> mth -> state -> stmt
| s_new  : nat -> cls -> state -> stmt
| s_stmts : stmt -> stmt -> stmt
| s_rtrn : nat -> stmt.

Inductive continuation : Type :=
| c_stmt : stmt -> continuation
| c_hole : nat -> stmt -> continuation.

Inductive e_value : Type :=
| ev_true  : e_value
| ev_false : e_value
| ev_null  : e_value
| ev_addr   : nat -> e_value.

Inductive exp : Type :=
| e_val   : e_value -> exp
| e_var   : var -> exp
| e_eq    : exp -> exp -> exp
| e_if    : exp -> exp -> exp -> exp
| e_acc_f : exp -> fld -> exp
| e_acc_g : exp -> gfld -> exp -> exp.

Notation "'e_true'" := (e_val ev_true)(at level 40).
Notation "'e_false'" := (e_val ev_false)(at level 40).
Notation "'e_null'" := (e_val ev_null)(at level 40).
Notation "'e_addr' r" := (e_val (ev_addr r))(at level 40).

(*methods is a mapping from method names to statements*)
Definition methods := partial_map mth stmt.

(*ghost_fields is a mapping from ghost field names to expressions*)
Definition ghost_fields := partial_map gfld exp.

Record classDef := clazz{c_name : cls;
                         c_flds : list fld;
                         c_meths : methods;
                         c_g_fields: ghost_fields}.

Record obj := new{cname : cls;
                  flds : fields;
                  meths : methods}.

Definition mdl := partial_map cls classDef.

Definition heap := partial_map nat obj.

Record frame := frm{varMap : state;
                    contn : continuation}.

Inductive stack :=
| base : stack
| scons : frame -> stack -> stack.

Definition peek (ψ : stack) : option frame :=
  match ψ with
  | base => None
  | scons ϕ _ => Some ϕ
  end.

Definition pop (ψ : stack) : option stack :=
  match ψ with
  | base => None
  | scons _ ψ => Some ψ
  end.


Instance stackMap : Mappable stack nat (option nat) :=
  {map :=
     fix map S x :=
       match S with
       | base => None
       | scons ϕ S' => ϕ.(varMap) x
       end
  }.

Definition config : Type := (heap * stack).

Instance configMapHeap : Mappable config nat (option obj) :=
  {map σ α := (fst σ) α}.

Instance configMapStack : Mappable config nat (option nat) :=
  {map σ x := map (snd σ) x}.

Instance expFoldable : PropFoldable exp var :=
  {
    foldAnd :=
      fix foldE e f n P :=
        match e with
        | e_val _ => P
        | e_var x => f x n
        | e_eq e1 e2 => foldE e1 f n P /\ foldE e2 f n P
        | e_if e1 e2 e3 => foldE e1 f n P /\ foldE e2 f n P /\ foldE e3 f n P
        | e_acc_f e' f' => foldE e' f n P
        | e_acc_g e1 g e2 => foldE e1 f n P /\ foldE e2 f n P
        end;

    foldOr :=
      fix foldE e f n P :=
        match e with
        | e_val _ => P
        | e_var x => f x n
        | e_eq e1 e2 => foldE e1 f n P \/ foldE e2 f n P
        | e_if e1 e2 e3 => foldE e1 f n P \/ foldE e2 f n P \/ foldE e3 f n P
        | e_acc_f e' f' => foldE e' f n P
        | e_acc_g e1 g e2 => foldE e1 f n P \/ foldE e2 f n P
        end
  }.

Definition closed_e (e : exp)(n : nat) :=
  foldAnd e
          (fun x n' =>
             match x with
             | hole m => n' <> m
             | _ => True
             end)
          n
          True.

Instance substExp : Subst exp var :=
  {sbst :=
     fix subst' e n x :=
       match e with
       | e_var y => e_var (sbst y n x)
       | e_eq e1 e2 => e_eq (subst' e1 n x) (subst' e2 n x)
       | e_if e1 e2 e3 => e_if (subst' e1 n x) (subst' e2 n x) (subst' e3 n x)
       | e_acc_f e' f => e_acc_f (subst' e' n x) f
       | e_acc_g e1 g e2 => e_acc_g (subst' e1 n x) g (subst' e2 n x)
       | _ => e
       end;

   closed := closed_e
  }.
Proof.
  intros e b Hcl;
    induction e;
    intros;
    auto;
    try unfold closed_e in *;
    andDestruct;
    crush;
    destruct v; auto; eqbNatAuto; crush.
Defined.

Lemma closed_e_closed_exp :
  forall e n, closed e n ->
         @closed exp var substExp e n.
Proof.
  auto.
Qed.

Lemma closed_exp_closed_e :
  forall e n,  @closed exp var substExp e n ->
          closed_e e n.
Proof.
  auto.
Qed.

Hint Rewrite closed_e_closed_exp closed_exp_closed_e : closed_db.

Instance substValInExp : Subst exp e_value :=
  {sbst :=
     fix subst' e n v :=
       match e with
       | e_var y => match y with
                   | hole m => if (n =? m)
                              then e_val v
                              else e
                   | _ => e
                   end
       | e_eq e1 e2 => e_eq (subst' e1 n v) (subst' e2 n v)
       | e_if e1 e2 e3 => e_if (subst' e1 n v) (subst' e2 n v) (subst' e3 n v)
       | e_acc_f e' f => e_acc_f (subst' e' n v) f
       | e_acc_g e1 g e2 => e_acc_g (subst' e1 n v) g (subst' e2 n v)
       | _ => e
       end;
   closed := closed_e
  }.
Proof.
  intros e b Hcl;
    induction e;
    intros;
    auto;
    try unfold closed_e in *;
    andDestruct;
    crush;
    destruct v; auto; eqbNatAuto; crush.
Defined.

Lemma closed_e_closed_val :
  forall e n, closed e n ->
         @closed exp e_value substValInExp e n.
Proof.
  auto.
Qed.

Lemma closed_val_closed_e :
  forall e n,  @closed exp e_value substValInExp e n ->
          closed_e e n.
Proof.
  auto.
Qed.

Hint Rewrite closed_e_closed_val closed_val_closed_e : closed_db.

Reserved Notation "M '∙' σ '⊢' e1 '↪' e2" (at level 40).

Inductive val : mdl -> config -> exp -> e_value -> Prop :=
| v_true     : forall M σ, M ∙ σ ⊢ e_true ↪ ev_true

| v_false    : forall M σ, M ∙ σ ⊢ e_false ↪ ev_false

| v_null     : forall M σ, M ∙ σ ⊢ e_null ↪ ev_null

| v_addr     : forall M σ r, M ∙ σ ⊢ e_addr r ↪ ev_addr r

| v_var      : forall M σ x α, map σ x = Some α ->
                          M ∙ σ ⊢ e_var (bind x) ↪ ev_addr α

| v_f_heap   : forall M σ e f α o α', M ∙ σ ⊢ e ↪ (ev_addr α) ->
                                 map σ α = Some o ->
                                 o.(flds) f = Some α' ->
                                 M ∙ σ ⊢ e_acc_f e f ↪ (ev_addr α')

| v_f_ghost  : forall M σ e0 e f α o e' v v' C, M ∙ σ ⊢ e0 ↪ (ev_addr α) ->
                                           map σ α = Some o ->
                                           M o.(cname) = Some C ->
                                           C.(c_g_fields) f = Some e' ->
                                           M ∙ σ ⊢ e ↪ v ->
                                           M ∙ σ ⊢ (sbst e' 0 v) ↪ v' ->
                                           M ∙ σ ⊢ e_acc_g e0 f e ↪ v'

| v_if_true  : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ ev_true ->
                                M ∙ σ ⊢ e1 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

| v_if_false : forall M σ e e1 e2 v, M ∙ σ ⊢ e ↪ ev_false -> 
                                M ∙ σ ⊢ e2 ↪ v ->
                                M ∙ σ ⊢ (e_if e e1 e2) ↪ v

| v_equals   : forall M σ e1 e2 v, M ∙ σ ⊢ e1 ↪ v ->
                              M ∙ σ ⊢ e2 ↪ v ->
                              M ∙ σ ⊢ (e_eq e1 e2) ↪ ev_true

| v_nequals  : forall M σ e1 e2 v1 v2, M ∙ σ ⊢ e1 ↪ v1 ->
                                  M ∙ σ ⊢ e2 ↪ v2 ->
                                  v1 <> v2 ->
                                  M ∙ σ ⊢ (e_eq e1 e2) ↪ ev_false

where "M '∙' σ '⊢' e1 '↪' e2":= (val M σ e1 e2).

Ltac closed_unfold_e :=
  match goal with
  | [H : closed_e _ _ |- _] => unfold closed_e in H; try solve [crush]
  end.

Reserved Notation "'⌊' x '⌋' σ '≜' α" (at level 40).
Reserved Notation "'⌊' Σ '⌋' σ '≜′' As" (at level 40).

Inductive interpret_x : nat -> config -> nat -> Prop :=
| int_x : forall x σ ψ ϕ α, snd σ = ψ ->
                       peek ψ = Some ϕ ->
                       (varMap ϕ) x = Some α -> 
                       ⌊ x ⌋ σ ≜ α
where "'⌊' x '⌋' σ '≜' α" := (interpret_x x σ α).
  
Inductive interpret_Σ : list nat -> config -> list nat -> Prop :=
| int_nil  : forall σ, ⌊ nil ⌋ σ ≜′ nil
| int_cons : forall x Σ σ α As, ⌊ x ⌋ σ ≜ α ->
                           ⌊ Σ ⌋ σ ≜′ As ->
                           ⌊ x::Σ ⌋ σ ≜′ (α::As)
where "'⌊' Σ '⌋' σ '≜′' As" := (interpret_Σ Σ σ As).

Reserved Notation "σ1 '↓' Σ '≜' σ2" (at level 80).

Inductive restrict : config -> list nat -> config -> Prop :=
| rstrct : forall Σ σ As χ χ', ⌊ Σ ⌋ σ ≜′ As ->
                          (forall α o, χ' α = Some o ->
                                  χ α = Some o) ->
                          (forall α o, χ' α = Some o ->
                                  In α As) ->
                          (forall α o, In α As ->
                                  χ' α = Some o) ->
                          σ ↓ Σ ≜ (χ', snd σ)
where "σ1 '↓' Σ '≜' σ2" := (restrict σ1 Σ σ2).


Definition update_ϕ_map (ϕ : frame)(x α : nat) :=
  frm (update x α ϕ.(varMap)) (ϕ.(contn)).

Definition update_ϕ_contn (ϕ : frame)(c : continuation) :=
  frm (ϕ.(varMap)) c.

Definition update_ψ_map (ψ : stack)(x α : nat) : stack :=
  match ψ with
  | base => base
  | scons ϕ ψ' => scons (update_ϕ_map ϕ x α) ψ'
  end.

Definition update_ψ_contn (ψ : stack)(c : continuation) : stack :=
  match ψ with
  | base => base
  | scons ϕ ψ' => scons (update_ϕ_contn ϕ c) ψ'
  end.

Definition update_σ_map (σ : config)(x α : nat) :=
  (fst σ, update_ψ_map (snd σ) x α).

Definition update_σ_contn (σ : config)(c : continuation) :=
  (fst σ, update_ψ_contn (snd σ) c).

Inductive classOf : nat -> config -> cls -> Prop :=
|cls_of : forall x σ α χ o C, ⌊ x ⌋ σ ≜ α ->
                         fst σ = χ ->
                         χ α = Some o ->
                         cname o = C ->
                         classOf x σ C.

Reserved Notation "M '∙' σ '⤳' σ'" (at level 40).

Inductive reduction : mdl -> config -> config -> Prop :=
| r_mth : forall M ϕ ψ ψ' χ x y ps σ m α o s s' C ϕ' ϕ'',
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    pop ψ = Some ψ' ->
    ϕ.(contn) = c_stmt (s_stmts (s_meth x y m ps) s') ->
    ⌊ y ⌋ σ ≜ α ->
    χ α = Some o ->
    (M (o.(cname))) = Some C ->
    C.(c_meths) m = Some s ->    
    ϕ' =  frm (varMap ϕ) (c_hole x s') ->
    ϕ'' = frm (update this α (compose ps (varMap ϕ))) (c_stmt s) ->
    M ∙ σ ⤳ (χ, scons ϕ'' (scons ϕ' (ψ')))

| r_vAssgn : forall M σ ϕ x y f s ψ χ α α' o σ' C,
    x <> this ->
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_var x) (r_fld y f)) s)) ->
    ⌊ y ⌋ σ ≜ α ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    (flds o) f = Some α' ->
    σ' = update_σ_map σ x α' ->
    M ∙ σ ⤳ σ'

| r_fAssgn : forall M σ ϕ ϕ' x y f s ψ ψ' χ α α' o σ' χ' o' C,
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    ϕ.(contn) = (c_stmt (s_stmts (s_asgn (r_fld y f) (r_var x)) s)) ->
    ⌊ y ⌋ σ ≜ α ->
    ⌊ x ⌋ σ ≜ α' ->
    classOf this σ C ->
    classOf y σ C ->
    χ α = Some o ->
    o' = new (cname o) (update f α' (flds o)) (meths o) ->
    χ' = update α o' χ ->
    ϕ' = frm (varMap ϕ) (c_stmt s) ->
    pop ψ = Some ψ' ->
    σ' = (χ', scons ϕ' ψ') ->
    M ∙ σ ⤳ σ'

| r_new : forall M σ σ' χ ψ ψ' ϕ ϕ' α x C fMap s o CDef,
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    ϕ.(contn) = (c_stmt (s_stmts (s_new x C fMap) s)) ->
    χ α = None ->
    M C = Some CDef ->
    (forall f y, fMap f = Some y ->
            In f (c_flds CDef)) ->
    (forall f, fMap f = None ->
          ~ In f (c_flds CDef)) ->
    o = new C fMap (c_meths CDef) ->
    ϕ' = frm (update x α (varMap ϕ)) (c_stmt s) ->
    pop ψ = Some ψ' ->
    σ' = (update α o χ, scons ϕ' ψ') ->
    M ∙ σ ⤳ σ'
    

| r_ret1 : forall M ϕ ϕ' ψ χ y x α ϕ'' σ s,
    σ = (χ, scons ϕ (scons ϕ' ψ)) ->
    ϕ.(contn) = c_stmt (s_rtrn x) ->
    ϕ'.(contn) = c_hole y s ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y α) (c_stmt s)->
    M ∙ σ ⤳ (χ, scons ϕ'' ψ)

| r_ret2 : forall M ϕ ϕ' ψ ψ' ψ'' χ y x α ϕ'' σ s s',
    σ = (χ, ψ) ->
    peek ψ = Some ϕ ->
    pop ψ = Some ψ' ->
    peek ψ' = Some ϕ' ->
    pop ψ' = Some ψ'' ->
    ϕ.(contn) = c_stmt (s_stmts (s_rtrn x) s') ->
    ϕ'.(contn) = c_hole y s ->
    ⌊x⌋ σ ≜ α ->
    ϕ'' = update_ϕ_contn (update_ϕ_map ϕ' y α) (c_stmt s)->
    M ∙ σ ⤳ (χ, scons ϕ'' ψ)

where "M '∙' σ '⤳' σ'" := (reduction M σ σ').
                                               
