Require Export Arith.
Require Import CpdtTactics.
Require Import List.

Inductive var : Type :=
| bind : nat -> var.

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

Instance nat_Eq : Eq nat :=
  {eqb n m := n =? m;
   eqb_refl := Nat.eqb_refl;
   eqb_sym := Nat.eqb_sym;
   eq_dec := Nat.eq_dec}.
Proof.
  intros; apply beq_nat_eq; auto.
  apply Nat.eqb_neq.
  apply Nat.eqb_neq.
Defined.

Instance var_Eq : Eq var :=
  {eqb x y :=
     match x, y with
     | bind n, bind m => n =? m
     end}.
Proof.
  intros; destruct a; apply Nat.eqb_refl.
  intros; destruct a1; destruct a2; apply Nat.eqb_sym.
  intros;
    destruct a1;
    destruct a2;
    symmetry in H;
    apply beq_nat_eq in H;
    subst; auto.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq;
    crush.
  intros x y;
    destruct x as [n];
    destruct y as [m];
    destruct (Nat.eq_dec n m) as [Heq|Hneq];
    subst;
    auto;
    right;
    crush.
Defined.

(*Section partial_maps.

  Set Implicit Arguments.

  Variables A B : Set.
           
  Inductive partial_map : Set :=
  | empty : partial_map
  | update : A -> B -> partial_map -> partial_map.

  Fixpoint pmap `{Eq A} (m : partial_map)(a : A) : option B :=
    match m with
    | empty => None
    | update a' b m' => if (eqb a a')
                       then Some b
                       else pmap m' a
    end.
  Unset Implicit Arguments.

End partial_maps.*)

Definition total_map (A B : Type) `{Eq A} := A -> B.

Definition t_empty {A B : Type} `{Eq A} (b : B) : total_map A B := (fun _ => b).

Definition t_update {A B : Type} `{Eq A} (map : total_map A B) (a : A)(b : B) :=
  fun x => if (eqb x a) then b else map x.

(*Definition t_compose {A B C : Type} `{Eq A} (map1 map2 : total_map)*)

Definition partial_map (A B : Type) `{Eq A} := total_map A (option B).

Definition empty {A B : Type} `{Eq A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eq A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).

Definition compose
           {A B C : Type} `{Eq A} `{Eq B}
           (map1 : partial_map A B)
           (map2 : partial_map B C) : partial_map A C :=
  fun a => match map1 a with
        | None => None
        | Some b => map2 b
        end.

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

Inductive finite {A B : Type}`{Eq A} : partial_map A B -> Prop :=
| fin_empty : finite empty
| fin_update : forall a b m, finite m ->
                        finite (update a b m).

Hint Constructors finite.

Class Mappable (A B C : Type) :=
  map : A -> B -> C.

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