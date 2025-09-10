Require Export Arith.
Require Import List.

Require Import CpdtTactics.

Inductive var : Type :=
| bnd : nat -> var.

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

Hint Resolve eqb_refl eqb_sym eqb_eqp eqb_neq neq_eqb eq_dec : eq_db.

Program Instance nat_Eq : Eq nat :=
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

Program Instance var_Eq : Eq var :=
  {eqb x y :=
     match x, y with
     | bnd n, bnd m => n =? m
     end}.
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


Definition total_map (A B : Type) `{Eq A} := A -> B.

Definition t_empty {A B : Type} `{Eq A} (b : B) : total_map A B := (fun _ => b).

Definition t_update {A B : Type} `{Eq A} (map : total_map A B) (a : A)(b : B) :=
  fun x => if (eqb x a) then b else map x.

Definition partial_map (A : Type)`{Eq A}(B : Type) := total_map A (option B).

Definition empty {A B : Type} `{Eq A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eq A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).


Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  {
    ret : forall {t : Type@{d}}, t -> m t;
    bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
  }.

Instance optionMonad : Monad option :=
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

(*
This feels monadish
Would be nice to do top level binds
Not actually possible because we only 

Instance partial_map_Monad {A : Type}`{Eq A} : Monad (partial_map A) :=
  {
    ret T x := ???
  }.*)

Notation "f1 '∘' f2" := (fun x => bind (f1 x) f2)(at level 40).

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

Hint Constructors finite : map_db.

Class Mappable (A B C : Type) :=
  mapp : A -> B -> C.

Notation "'⟦' b '↦' c '⟧' ∈ a" := (mapp a b = Some c)(at level 40).

Class PropFoldable (A B : Type) :=
  {
    foldAnd : A -> (B -> nat -> Prop) -> nat -> Prop -> Prop;
    foldOr  : A -> (B -> nat -> Prop) -> nat -> Prop -> Prop
  }.

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

Create HintDb closed_db.

Inductive varSet : Type :=
| s_hole : nat -> varSet
| s_bind : list var -> varSet.

Definition InΣ (x : var)(Σ : varSet) :=
  match Σ with
  | s_hole _ => False
  | s_bind l => In x l
  end.



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

Definition fresh_in_map {A : Type} (x : var) (m : partial_map var A) : Prop :=
  m x = None.
