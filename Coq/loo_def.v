Require Export Arith.
Require Import CpdtTactics.
Require Import List.

Definition fld := nat.

Definition mth := nat.

Definition gfld := nat.

Definition cls := nat.

Inductive var : Type :=
| hole : nat -> var
| bind : nat -> var.
(*| addr : nat -> var.*)

(*
Inductive label : Type :=
| fld : id -> label
| mth : id -> label
| gst : id -> label
| cls : id -> label.

Fixpoint eqb_label (l1 l2 : label) : bool :=
  match l1, l2 with
  | fld n1, fld n2 => n1 =? n2
  | mth n1, mth n2 => n1 =? n2
  | gst n1, gst n2 => n1 =? n2
  | cls n1, cls n2 => n1 =? n2
  | _, _ => false
  end.
*)

Class Eqb (A : Type) :=
  {eqb : A -> A -> bool}.

(*
Instance label_Eqb : Eqb label :=
  {eqb := eqb_label}.
 *)

Instance nat_Eqb : Eqb nat :=
  {eqb n m := n =? m}.

Instance id_Eqb : Eqb var :=
  {eqb x y :=
     match x, y with
     | bind n, bind m => n =? m
     | hole n, hole m => n =? m
     | _, _ => false
     end}.

Definition total_map (A B : Type) `{Eqb A} := A -> B.

Definition t_empty {A B : Type} `{Eqb A} (b : B) : total_map A B := (fun _ => b).

Definition t_update {A B : Type} `{Eqb A} (map : total_map A B) (a : A)(b : B) :=
  fun x => if (eqb x a) then b else map x.

Definition partial_map (A B : Type) `{Eqb A} := total_map A (option B).

Definition empty {A B : Type} `{Eqb A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eqb A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).

(*Definition stack (A B : Type) `{Eqb A} := partial_map A B.

Definition s_empty {A B : Type} `{Eqb A} : stack A B := empty.

Definition s_update {A B : Type} `{Eqb A} (f : partial_map A B) (map : stack A B) :=
  fun a => match f a with
        | None => map a
        | Some b => Some b
        end.*)

Inductive term : Type :=
| t_var   : var -> term
| t_acc_f : var -> fld -> term
| t_acc_m : var -> mth -> term -> term
| t_new   : cls -> list var -> term.

Inductive stmt : Type :=
| s_set_v : var -> term -> stmt
| s_set_f : var -> fld -> term -> stmt
| s_retrn : var -> stmt.

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



Definition fields := partial_map fld nat.

Definition methods := partial_map mth stmt.

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

Definition state := partial_map nat nat.

Record frame := frm{varMap : state;
                    contn : stmt}.

Inductive stack :=
| base : frame -> stack
| stack_cons : frame -> stack -> stack.



Class Mappable (A B C : Type) :=
  map : A -> B -> C.

Instance stackMap : Mappable stack nat (option nat) :=
  {map :=
     fix map S x :=
       match S with
       | base f => f.(varMap) x
       | stack_cons f S' => f.(varMap) x
       end
  }.

Definition config : Type := (heap * stack).

Instance configMapHeap : Mappable config nat (option obj) :=
  {map σ α := (fst σ) α}.

Instance configMapStack : Mappable config nat (option nat) :=
  {map σ x := map (snd σ) x}.

Definition updateFrame (ϕ : frame)(x α : nat) :=
  frm (update x α ϕ.(varMap)) (ϕ.(contn)).

Definition updateStack (ψ : stack)(x α : nat) :=
  match ψ with
  | base ϕ => base (updateFrame ϕ x α)
  | stack_cons ϕ ψ' => stack_cons (updateFrame ϕ x α) ψ'
  end.

Definition updateσ (σ : config)(x α : nat) :=
  (fst σ, updateStack (snd σ) x α).


Class PropFoldable (A B : Type) :=
  {
    foldAnd : A -> (B -> nat -> Prop) -> nat -> Prop -> Prop;
    foldOr  : A -> (B -> nat -> Prop) -> nat -> Prop -> Prop
  }.

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

Class Subst (A B: Type) :=
  {sbst : A -> nat -> B -> A;
   closed : A -> nat -> Prop;
   closed_subst : forall a n, closed a n ->
                         forall b, sbst a n b = a
  }.

Notation "'[' b '/s' n ']' a" := (sbst a n b)(at level 80).

Inductive closed_v : var -> nat -> Prop :=
| cl_hole : forall n m, n <> m ->
                   closed_v (hole m) n
| cl_bind : forall n m, closed_v (bind m) n.

Instance substVar : Subst var var :=
  {sbst x n y := match x with
                  | hole m => if (m =? n)
                             then y
                             else x
                  | _ => x
                  end;
   closed x n := forall m, x = hole m -> m <> n}.
Proof.
  intros;
    destruct a;
    auto;
    assert (Hneq : n0 <> n);
    [auto
    |apply Nat.eqb_neq in Hneq;
     rewrite Hneq];
    auto.  
Defined.

(*Create HintDb foo_db.

Goal True.
  auto with foo_db nocore. (* no hints *)
  exact I.
Qed.*)

(*Instance substVar (A : Type)(cons : var -> A) : Subst A nat var A :=
  {subst a n y := match y with
                  | hole m => if (m =? n)
                             then a
                             else (cons y)
                  | _ => (cons y)
                  end}.*)

(*Inductive closed_e : exp -> nat -> Prop :=
| cl_var : forall x n, closed x n ->
                  closed_e (e_var x) n
| cl_eq  : forall e1 e2 n, closed_e e1 n ->
                      closed_e e2 n ->
                      closed_e (e_eq e1 e2) n
| cl_if  : forall e1 e2 e3 n, closed_e e1 n ->
                         closed_e e2 n ->
                         closed_e e3 n ->
                         closed_e (e_if e1 e2 e3) n
| cl_acc_f : forall e f n, closed_e e n ->
                      closed_e (e_acc_f e f) n
| cl_acc_g : forall e1 g e2 n, closed_e e1 n ->
                          closed_e e2 n ->
                          closed_e (e_acc_g e1 g e2) n
| cl_val   : forall v n, closed_e (e_val v) n.*)

Ltac andDestruct :=
  repeat match goal with
         | [H : ?P /\ ?Q |- _] => let Ha := fresh "Ha" in
                               let Hb := fresh "Hb" in
                               destruct H as [Ha Hb]
         end.

Ltac eqbNatAuto :=
  match goal with
  | [|- context[?n =? ?m]] => let Heq := fresh "Heq" in
                            destruct (Nat.eq_dec n m) as [Heq|Heq];
                            [subst; rewrite Nat.eqb_refl
                            |apply Nat.eqb_neq in Heq;
                             rewrite Heq]
  end.

Definition closed_e (e : exp)(n : nat) :=
  foldAnd e
          (fun x n' =>
             match x with
             | hole m => n' <> m
             | _ => True
             end)
          n
          True.

Create HintDb closed_db.

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

Reserved Notation "M 'en' σ '⊢' e1 '↪' e2" (at level 40).

Inductive val : mdl -> config -> exp -> e_value -> Prop :=
| v_true     : forall M σ, M en σ ⊢ e_true ↪ ev_true

| v_false    : forall M σ, M en σ ⊢ e_false ↪ ev_false

| v_null     : forall M σ, M en σ ⊢ e_null ↪ ev_null

| v_addr     : forall M σ r, M en σ ⊢ e_addr r ↪ ev_addr r

| v_var      : forall M σ x α, map σ x = Some α ->
                          M en σ ⊢ e_var (bind x) ↪ ev_addr α

| v_f_heap   : forall M σ e f α o α', M en σ ⊢ e ↪ (ev_addr α) ->
                                 map σ α = Some o ->
                                 o.(flds) f = Some α' ->
                                 M en σ ⊢ e_acc_f e f ↪ (ev_addr α')

| v_f_ghost  : forall M σ e0 e f α o e' v v' C, M en σ ⊢ e0 ↪ (ev_addr α) ->
                                           map σ α = Some o ->
                                           M o.(cname) = Some C ->
                                           C.(c_g_fields) f = Some e' ->
                                           M en σ ⊢ e ↪ v ->
                                           M en σ ⊢ (sbst e' 0 v) ↪ v' ->
                                           M en σ ⊢ e_acc_g e0 f e ↪ v'

| v_if_true  : forall M σ e e1 e2 v, M en σ ⊢ e ↪ ev_true ->
                                M en σ ⊢ e1 ↪ v ->
                                M en σ ⊢ (e_if e e1 e2) ↪ v

| v_if_false : forall M σ e e1 e2 v, M en σ ⊢ e ↪ ev_false ->
                                M en σ ⊢ e2 ↪ v ->
                                M en σ ⊢ (e_if e e1 e2) ↪ v

| v_equals   : forall M σ e1 e2 v, M en σ ⊢ e1 ↪ v ->
                              M en σ ⊢ e2 ↪ v ->
                              M en σ ⊢ (e_eq e1 e2) ↪ ev_true

| v_nequals  : forall M σ e1 e2 v1 v2, M en σ ⊢ e1 ↪ v1 ->
                                  M en σ ⊢ e2 ↪ v2 ->
                                  v1 <> v2 ->
                                  M en σ ⊢ (e_eq e1 e2) ↪ ev_false

where "M 'en' σ '⊢' e1 '↪' e2":= (val M σ e1 e2).

Inductive varSet : Type :=
| s_hole : nat -> varSet
| s_bind : list nat -> varSet.

Instance varSetSubst : Subst varSet varSet :=
  {
    sbst :=
      fun Σ1 n Σ2 =>
          match Σ1 with
          | s_hole m => if (m =? n)
                       then Σ2
                       else Σ1
          | s_bind _ => Σ1
          end;

    closed := fun Σ n =>
                match Σ with
                | s_hole m => n <> m
                | s_bind _ => True
                end
  }.
Proof.
  intros;
    destruct a; auto;
      eqbNatAuto; auto;
        contradiction H; auto.
Defined.

Lemma closed_bind_Set :
  forall l m (Σ : varSet), @sbst varSet varSet varSetSubst (s_bind l) m Σ = (s_bind l).
Proof.
  auto.
Qed.

Hint Rewrite closed_bind_Set : closed_db.

Inductive asrt : Type :=
(*simpl*)
| a_exp   : exp -> asrt
| a_eq    : exp -> exp -> asrt (* is this necessary? isn't it a redundant subcase of a_exp? *)
| a_class : exp -> cls -> asrt
| a_set   : exp -> varSet -> asrt

(*connectives*)
| a_arr   : asrt -> asrt -> asrt
| a_and   : asrt -> asrt -> asrt
| a_or    : asrt -> asrt -> asrt
| a_neg   : asrt -> asrt

(*quantifiers*)
| a_all_x : asrt -> asrt
| a_all_Σ : asrt -> asrt
| a_ex_x  : asrt -> asrt
| a_ex_Σ  : asrt -> asrt

(*permission*)
| a_acc   : var -> var -> asrt

(*control*)
| a_call  : var -> var -> mth -> var -> asrt

(*time*)
| a_next  : asrt -> asrt
| a_will  : asrt -> asrt
| a_prev  : asrt -> asrt
| a_was   : asrt -> asrt

(*space*)
| a_in    : asrt -> varSet -> asrt

(*viewpoint*)
| a_extrn : var -> asrt
| a_intrn : var -> asrt.

Instance asrtFoldableVar : PropFoldable asrt var :=
  {
    foldAnd :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => foldAnd e f n P
        | a_eq e1 e2        => foldAnd e1 f n P /\ foldAnd e2 f n P
        | a_class e C       => foldAnd e f n P
        | a_set e Σ         => foldAnd e f n P
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P /\ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => f v1 n /\ f v2 n
        (*control*)
        | a_call v1 v2 m v3 => f v1 n /\ f v2 n /\ f v3 n
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => f v n
        | a_intrn v          => f v n
        end;

    foldOr :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => foldAnd e f n P
        | a_eq e1 e2        => foldAnd e1 f n P /\ foldAnd e2 f n P
        | a_class e C       => foldAnd e f n P
        | a_set e Σ         => foldAnd e f n P
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P \/ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => f v1 n /\ f v2 n
        (*control*)
        | a_call v1 v2 m v3 => f v1 n \/ f v2 n \/ f v3 n
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => f v n
        | a_intrn v          => f v n
        end
  }.

Instance asrtFoldableVarSet : PropFoldable asrt varSet :=
  {
    foldAnd :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => P
        | a_eq e1 e2        => P
        | a_class e C       => P
        | a_set e Σ         => f Σ n
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P /\ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f n P
        | a_all_Σ A'      => foldA A' f (S n) P
        | a_ex_x A'       => foldA A' f n P
        | a_ex_Σ A'       => foldA A' f (S n) P
        (*permission*)
        | a_acc v1 v2       => P
        (*control*)
        | a_call v1 v2 m v3 => P
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P /\ f Σ n
        (*viewpoint*)
        | a_extrn v          => P
        | a_intrn v          => P
        end;

    foldOr :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => P
        | a_eq e1 e2        => P
        | a_class e C       => P
        | a_set e Σ         => f Σ n
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P \/ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => P
        (*control*)
        | a_call v1 v2 m v3 => P
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => P
        | a_intrn v          => P
        end
  }.

Definition closed_A (A : asrt)(n : nat) :=
  foldAnd A
          (fun x n' =>
             match x with
             | hole m => n' <> m
             | _ => True
             end)
          n
          True.

Definition closed_A_set (A : asrt)(n : nat) :=
  foldAnd A
          (fun x n' =>
             match x with
             | s_hole m => n' <> m
             | _ => True
             end)
          n
          True.


(*Inductive closed_A : asrt -> nat -> Prop :=
| cla_exp : forall e n, closed e n ->
                   closed_A (a_exp e) n
| cla_eq  : forall e1 e2 n, closed e1 n ->
                       closed e2 n ->
                       closed_A (a_eq e1 e2) n
| cla_class : forall e C n, closed e n ->
                       closed_A (a_class e C) n
| cla_set : forall e Σ n, closed_A (a_set e Σ) n
| cla_arr : forall A1 A2 n, closed_A A1 n ->
                       closed_A A2 n ->
                       closed_A (a_arr A1 A2) n
| cla_and : forall A1 A2 n, closed_A A1 n ->
                       closed_A A2 n ->
                       closed_A (a_and A1 A2) n
| cla_or : forall A1 A2 n, closed_A A1 n ->
                      closed_A A2 n ->
                      closed_A (a_or A1 A2) n
| cla_neg : forall A n, closed_A A n ->
                   closed_A (a_neg A) n
| cla_all_x : forall A n, closed_A A (S n) ->
                     closed_A (a_all_x A) n
| cla_all_Σ : forall A n, closed_A A n ->
                     closed_A (a_all_Σ A) n
| cla_ex_x : forall A n, closed_A A (S n) ->
                    closed_A (a_ex_x A) n
| cla_ex_Σ : forall A n, closed_A A n ->
                    closed_A (a_ex_Σ A) n
| cla_acc : forall x y n, closed x n ->
                     closed y n ->
                     closed_A (a_acc x y) n
| cla_call : forall x y m z n, closed x n ->
                          closed y n ->
                          closed z n ->
                          closed_A (a_call x y m z) n
| cla_next : forall A n, closed_A A n ->
                    closed_A (a_next A) n
| cla_will : forall A n, closed_A A n ->
                    closed_A (a_will A) n
| cla_prev : forall A n, closed_A A n ->
                    closed_A (a_prev A) n
| cla_was : forall A n, closed_A A n ->
                   closed_A (a_was A) n.*)

Ltac closed_unfold :=
  match goal with
  | [H : closed_e _ _ |- _] => unfold closed_e in H; try solve [crush]
  | [H : closed_A _ _ |- _] => unfold closed_A in H; try solve [crush]
  | [H : closed_A_set _ _ |- _] => unfold closed_A_set in H; try solve [crush]
  end.

Instance substAssertionVar : Subst asrt nat :=
  {sbst :=
     fix subst' A n x :=
       match A with
       | a_exp e           => a_exp (sbst e n (bind x))
       | a_eq e1 e2        => a_eq (sbst e1 n (bind x))
                                  (sbst e2 n (bind x))
       | a_class e C       => a_class (sbst e n (bind x)) C
       | a_set e Σ         => a_set (sbst e  n (bind x)) Σ
       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n x) (subst' A2 n x)
       | a_and A1 A2       => a_and (subst' A1 n x) (subst' A2 n x)
       | a_or A1 A2        => a_or (subst' A1 n x) (subst' A2 n x)
       | a_neg A'          => a_neg (subst' A' n x)
       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' (S n) x)
       | a_all_Σ A'      => a_all_Σ (subst' A' n x)
       | a_ex_x A'       => a_ex_x (subst' A' (S n) x)
       | a_ex_Σ A'       => a_ex_Σ (subst' A' n x)
       (*permission*)
       | a_acc v1 v2       => a_acc (sbst v1 n (bind x)) (sbst v2 n (bind x))
       (*control*)
       | a_call v1 v2 m v3 => a_call ([bind x /s n] v1)
                                    ([bind x /s n] v2) m
                                    ([bind x /s n] v3)
       (*time*)
       | a_next A'         => a_next (subst' A' n x)
       | a_will A'         => a_will (subst' A' n x)
       | a_prev A'         => a_prev (subst' A' n x)
       | a_was A'          => a_was (subst' A' n x)
       (*space*)
       | a_in A' Σ         => a_in (subst' A' n x) Σ
       (*viewpoint*)
       | a_extrn v          => a_extrn ([(bind x) /s n] v)
       | a_intrn v          => a_intrn ([(bind x) /s n] v)
       end;

   closed := closed_A
  }.
Proof.
  intros a;
    induction a;
    intros;
    try solve [repeat rewrite closed_subst; auto];
    auto;
    try solve [repeat rewrite closed_subst; closed_unfold].
Defined.
        
Instance substAssertionVarSet : Subst asrt varSet :=
  {
    sbst :=
     fix subst' A n Σ :=
       match A with
       (*simpl*)
       | a_set e Σ'         => a_set e ([Σ /s n] Σ')

       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n Σ) (subst' A2 n Σ)
       | a_and A1 A2       => a_and (subst' A1 n Σ) (subst' A2 n Σ)
       | a_or A1 A2        => a_or (subst' A1 n Σ) (subst' A2 n Σ)
       | a_neg A'          => a_neg (subst' A' n Σ)

       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' n Σ)
       | a_all_Σ A'      => a_all_Σ (subst' A' (S n) Σ)
       | a_ex_x A'       => a_ex_x (subst' A' (n) Σ)
       | a_ex_Σ A'       => a_ex_Σ (subst' A' (S n) Σ)

       (*time*)
       | a_next A'         => a_next (subst' A' n Σ)
       | a_will A'         => a_will (subst' A' n Σ)
       | a_prev A'         => a_prev (subst' A' n Σ)
       | a_was A'          => a_was (subst' A' n Σ)

       (*space*)
       | a_in A' Σ'         => a_in (subst' A' n Σ) ([Σ /s n] Σ')

       | _          => A
       end;

    closed := closed_A_set
  }.
Proof.
  intros a;
    induction a;
    intros;
    try solve [repeat rewrite closed_subst; closed_unfold; auto];
    auto.
Defined.

(*
implication cannot be directly used due to strict positivity requirement of Coq
thus, satisfaction rules are in CNF

Similarly, (¬ A) ≡ (A -> False) which also violates the strict positivity 
requirement of Coq thus we define sat mutually with nsat, the negation of sat

For positivity discussion, see: http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html#lab30
 *)

Reserved Notation "'⌊' x '⌋' σ '≜' α" (at level 40).
Reserved Notation "'⌊' Σ '⌋' σ '≜′' As" (at level 40).

Inductive interpret_x : nat -> config -> nat -> Prop :=
| int_x : forall x σ ϕ ψ α, snd σ = stack_cons ϕ ψ ->
                       ϕ.(varMap) x = Some α -> 
                       ⌊ x ⌋ σ ≜ α
where "'⌊' x '⌋' σ '≜' α" := (interpret_x x σ α).
  
Inductive interpret_Σ : list nat -> config -> list nat -> Prop :=
| int_nil  : forall σ, ⌊ nil ⌋ σ ≜′ nil
| int_cons : forall x Σ σ α As, ⌊ x ⌋ σ ≜ α ->
                           ⌊ Σ ⌋ σ ≜′ As ->
                           ⌊ x::Σ ⌋ σ ≜′ (α::As)
where "'⌊' Σ '⌋' σ '≜′' As" := (interpret_Σ Σ σ As).

Reserved Notation "M 'en' σ '⊨' A"(at level 40).
Reserved Notation "M 'en' σ '⊭' A"(at level 40).

Definition InΣ (n : nat)(Σ : varSet) :=
  match Σ with
  | s_hole _ => False
  | s_bind l => In n l
  end.

Inductive fresh_x : nat -> config -> asrt -> Prop :=
| frsh : forall x σ A, map (snd σ) x = None ->
                  closed A x -> 
                  fresh_x x σ A.

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

(*
  satisfaction only uses one module at the moment
  this needs to change once the time assetions are
  properly modeled
 *)

Inductive sat : mdl -> config -> asrt -> Prop :=
(*simple*)
| sat_exp   : forall M σ e, M en σ ⊢ e ↪ ev_true ->
                       M en σ ⊨ a_exp e

| sat_class : forall M σ e C α o, M en σ ⊢ e ↪ (ev_addr α) ->
                             map σ α = Some o -> 
                             o.(cname) = C ->
                             M en σ ⊨ (a_class e C)

| sat_set   : forall M σ e Σ α As, M en σ ⊢ e ↪ (ev_addr α) ->
                              ⌊ Σ ⌋ σ ≜′ As ->
                              In α As ->
                              M en σ ⊨ (a_set e (s_bind Σ))

(*connectives*)
| sat_and   : forall M σ A1 A2, M en σ ⊨ A1 ->
                           M en σ ⊨ A2 ->
                           M en σ ⊨ (a_and A1 A2)
                               
| sat_or1   : forall M σ A1 A2, M en σ ⊨ A1 ->
                           M en σ ⊨ (a_or A1 A2)
                               
| sat_or2   : forall M σ A1 A2, M en σ ⊨ A2 ->
                           M en σ ⊨ (a_or A1 A2)

| sat_arr1  : forall M σ A1 A2, M en σ ⊨ A2 ->
                           M en σ ⊨ (a_arr A1 A2)

| sat_arr2  : forall M σ A1 A2, M en σ ⊭ A1 ->
                           M en σ ⊨ (a_arr A1 A2)
                             
| sat_not   : forall M σ A, M en σ ⊭ A ->
                       M en σ ⊨ (a_neg A)

(*quantifiers*)
| sat_all_x : forall M σ A, (forall α z, exists (o : obj),
                             map σ α = Some o ->
                             fresh_x z σ A ->
                             M en (updateσ σ z α) ⊨ ([z /s 0]A)) ->
                       M en σ ⊨ (a_all_x A)

| sat_ex_x  : forall M σ A z α, (exists (o : obj), map σ α = Some o) ->
                           M en (updateσ σ z α) ⊨ ([z /s 0] A) ->
                           M en σ ⊨ (a_all_x A)

(*viewpoint*)
| sat_extrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                             map σ α = Some o ->
                             o.(cname) = C ->
                             M C = None ->
                             M en σ ⊨ a_extrn (bind x)

| sat_intrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                             map σ α = Some o ->
                             o.(cname) = C ->
                             (exists CDef, M C = Some CDef) ->
                             M en σ ⊨ a_intrn (bind x)

| sat_in    : forall M σ A Σ σ', σ ↓ Σ ≜ σ' ->
                            M en σ' ⊨ A ->
                            M en σ ⊨ A

where "M 'en' σ '⊨' A" := (sat M σ A)

with
nsat : mdl -> config -> asrt -> Prop :=
(*simple*)
| nsat_exp : forall M σ e v, M en σ ⊢ e ↪ v ->
                        v <> ev_true ->
                        M en σ ⊭ (a_exp e)

| nsat_class : forall M σ e C C' α o, M en σ ⊢ e ↪ (ev_addr α) ->
                                 map σ α = Some o -> 
                                 o.(cname) = C' ->
                                 C <> C' ->
                                 M en σ ⊭ (a_class e C)

| nsat_set   : forall M σ e Σ As, ⌊ Σ ⌋ σ ≜′ As ->
                             (forall α, M en σ ⊢ e ↪ (ev_addr α) -> ~ In α As) ->
                             M en σ ⊭ (a_set e (s_bind Σ))

(*connectives*)
| nsat_and1  : forall M σ A1 A2, M en σ ⊭ A1 ->
                            M en σ ⊭ (a_and A1 A2)
                        
| nsat_and2  : forall M σ A1 A2, M en σ ⊭ A2 ->
                            M en σ ⊭ (a_and A1 A2)
                        
| nsat_or    : forall M σ A1 A2, M en σ ⊭ A1 ->
                            M en σ ⊭ A2 ->
                            M en σ ⊭ (a_or A1 A2)

| nsat_arr   : forall M σ A1 A2, M en σ ⊨ A1 ->
                            M en σ ⊭ A2 ->
                            M en σ ⊭ (a_arr A1 A2)
                              
| nsat_not   : forall M σ A, M en σ ⊨ A ->
                        M en σ ⊭ (a_neg A)

(*quantifiers*)
| nsat_all_x : forall M σ A α, (exists y, map σ y = Some α) ->
                          M en (fst σ, snd σ) ⊭ A ->
                          M en σ ⊭ (a_all_x A) (*this is wrong: it needs to be for all addresses, and 
                                                      some mapping for z needs to be added to the config: σ[z ↦ α]*)

| nsat_ex_x : forall M σ A, (forall y α, map σ y = Some α ->
                               M en σ ⊭ ([y /s 0] A)) ->
                       M en σ ⊭ (a_ex_x A)

(*viewpoint*) (* well-formeness? This is important!!!!*)
(*| nsat_extrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_extrn (bind x)

| nsat_extrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_extrn (bind x)*) 

| nsat_extrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                              map σ α = Some o ->
                              o.(cname) = C ->
                              (exists CDef, M C = Some CDef) ->
                              M en σ ⊭ a_extrn (bind x)

(*| nsat_intrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_intrn (bind x)

| nsat_intrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_intrn (bind x)*) (*not needed. In the case where x or α are not defined, then we can't satisfy A*)

| nsat_intrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                              map σ α = Some o ->
                              o.(cname) = C ->
                              M C = None ->
                              M en σ ⊭ a_intrn (bind x)

| nsat_in    : forall M σ A Σ σ', σ ↓ Σ ≜ σ' ->
                             M en σ' ⊭ A ->
                             M en σ ⊭ A

where "M 'en' σ '⊭' A" := (nsat M σ A).

  
(*
  assertions:
     expressions:
        * e                      // what's going on here? is "x" a valid assertion?
        * e = e
        * e : ClassId
        * e elem S               // could this be x elem S? can an unevaluated expression 
                                 // really be in S?

     references:
        * forall x. A
        * forall S. A
        * exists x. A
        * exists S. A
        * x access y
        * <x calls x.m(x, ...)>  // correction: these do not need to be the same 
                                 // are these the same x's? the syntax does not seem consistent here
                                 // x access y uses different metavariables for the variables used
                                 // but A -> A uses the same metavariables ...?

        * <S in A>               // space: should be <A in S>
                                 // should this be A in S? x in S?
                                 // usage ex.: <(exists o. <o access a4>) in S>
                                 // ex. matches A in S, but surely the "in" refers to "o"
                                 // other examples use "A in S"
                                 // I understand this to mean something like A holds given the
                                 // state S

        * <external x>           // external refers implicitly to the module being specified
        * <changes e>            // encoded using other assertions

     operators:
        * A -> A
        * A /\ A
        * A \/ A
        * ~ A
        * next<A>
        * will<A>
        * prev<A>
        * was<A>

*)