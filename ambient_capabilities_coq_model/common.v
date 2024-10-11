Require Export Arith.
Require Import List.

Require Import CpdtTactics.

Class Eq (A : Type) :=
  {eqb : A -> A -> bool;
   eqb_refl : forall a, eqb a a = true;
   eqb_sym : forall a1 a2, eqb a1 a2 = eqb a2 a1;
   eqb_eqp : forall a1 a2, eqb a1 a2 = true ->
                      a1 = a2;
   eqb_neq : forall a1 a2, eqb a1 a2 = false ->
                      a1 <> a2;
   neq_eqb : forall a1 a2, a1 <> a2 ->
                      eqb a1 a2 = false;
   eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}}.

#[global] Hint Resolve eqb_refl eqb_sym eqb_eqp eqb_neq neq_eqb eq_dec : eq_db.

#[global] Program Instance nat_Eq : Eq nat :=
  {eqb n m := n =? m;
   eqb_refl := Nat.eqb_refl;
   eqb_sym := Nat.eqb_sym;
   eq_dec := Nat.eq_dec}.
Next Obligation.
  auto using beq_nat_eq.
Defined.
Next Obligation.
  apply Nat.eqb_neq; auto.
Defined.
Next Obligation.
  apply Nat.eqb_neq; auto.
Defined.

Definition total_map (A B : Type) `{Eq A} := A -> B.

Definition t_empty {A B : Type} `{Eq A} (b : B) : total_map A B := (fun _ => b).

Definition t_update {A B : Type} `{Eq A} (map : total_map A B) (a : A)(b : B) :=
  fun x => if (eqb x a) then b else map x.

Definition partial_map (A : Type)`{Eq A}(B : Type) := total_map A (option B).

Definition empty {A B : Type} `{Eq A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eq A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).

Notation "'⟦' a '↦' b '⟧' m" := (update a b m)(at level 41, right associativity).
Notation "'⟦' x '↦' y '⟧_∈' m" := (m x = Some y)(at level 41).
Notation "'∅'" := empty(at level 41).

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  {
    ret : forall {t : Type@{d}}, t -> m t;
    bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
  }.

Notation "f1 '∘' f2" := (fun x => bind (f2 x) f1)(at level 40).

#[global] Instance optionMonad : Monad option :=
  {
    ret T x :=
      Some x ;
    bind :=
      fun T U m f =>
        match m with
        | None => None
        | Some x => f x
        end
  }.

Fixpoint concat {A : Type}(l1 l2 : list A) :=
  match l1 with
  | nil => l2
  | h :: t => h :: concat t l2
  end.

#[global] Instance listMonad : Monad list :=
  {
    ret T x := x :: nil;
    bind :=
      fix bind' T U m f :=
        match m with
        | nil => nil
        | x :: m' => concat (f x) (bind' T U m' f)
        end
  }.

Class Functor (f : Type -> Type) : Type :=
  {
    fmap : forall {a b : Type}, (a -> b) -> f a -> f b
  }.

#[global] Instance list_functor : Functor list :=
  {
    fmap := map
  }.

(*)Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {

    pure : forall a : Type, a -> f a;
    ap   : forall a b : Type, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g)
  }.

#[global] Instance list_app : Applicative list :=
  {
    pure 
  }*)


(*Definition compose
           {A B C : Type} `{Eq A} `{Eq B}
           (map1 : partial_map A B)
           (map2 : partial_map B C) : partial_map A C :=
  fun a => match map1 a with
        | None => None
        | Some b => map2 b
        end.*)

(*Fixpoint compose
         {A B C : Set} `{Eq A} `{Eq B}
         (m1 : partial_map A B)(m2 : partial_map B C) : partial_map A C :=
  match m1 with
  | empty _ _ => empty _ _
  | update a b m => match (pmap m2 b) with
                   | None => compose m m2
                   | Some c => update a c (compose m m2)
                   end
  end.*)


Definition extend {A B : Type} `{Eq A} (M1 M2 : partial_map A B) : partial_map A B :=
  fun a =>
    match M1 a with
    | None => M2 a
    | _ => M1 a
    end.

Notation "f1 '∪' f2" := (extend f1 f2)(at level 40).

Inductive finite {A B : Type}`{Eq A} : partial_map A B -> Prop :=
| fin_empty : finite empty
| fin_update : forall a b m, finite m ->
                        finite (update a b m).

#[global] Hint Constructors finite : map_db.

Create HintDb closed_db.


(** Law of the Excluded Middle: *)
Parameter excluded_middle : forall P, {P} + {~P}.

Definition maps_into {A B C : Type}`{Eq A}`{Eq B}(f : partial_map A B)(g : partial_map B C) :=
  (forall a b, f a = Some b -> exists c, g b = Some c).

Definition maps_from {A B C : Type}`{Eq A}`{Eq B}(g : partial_map B C)(f : partial_map A B) :=
  (forall b c, g b = Some c -> exists a, f a = Some b).

Definition onto {A B C : Type}`{Eq A}`{Eq B}(f : partial_map A B)(g : partial_map B C) :=
  (maps_into f g) /\ (maps_from g f).

Definition disjoint_dom {A B C : Type}`{Eq A}(f : partial_map A B)(g : partial_map A C) :=
  (forall a b, f a = Some b -> g a = None).

Definition same_dom {A B C : Type}`{Eq A}(f : partial_map A B)(g : partial_map A C) :=
  (forall a b, f a = Some b -> exists c, g a = Some c) /\
  (forall a c, g a = Some c -> exists b, f a = Some b).

Definition subset {A B : Type}`{Eq A}(f : partial_map A B)(f g : partial_map A B) :=
  forall a b, f a = Some b -> g a = Some b.

Definition fresh_in_map {A B : Type}`{Eq A} (a : A) (m : partial_map A B) : Prop :=
  m a = None.

Notation "a '∈' m" := (exists b, m a = Some b)(at level 40).
Notation "a '∉' m" := (fresh_in_map a m)(at level 40).

(** Tactics *)

Ltac disj_split :=
  match goal with
  | [H : _ \/ _ |- _ ] =>
    destruct H
  end.

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
