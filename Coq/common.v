Require Export Arith.
Require Import CpdtTactics.
Require Import List.

Inductive var : Type :=
| bind : nat -> var.

Class Eqb (A : Type) :=
  {eqb : A -> A -> bool}.

Instance nat_Eqb : Eqb nat :=
  {eqb n m := n =? m}.

Instance id_Eqb : Eqb var :=
  {eqb x y :=
     match x, y with
     | bind n, bind m => n =? m
     end}.

Definition total_map (A B : Type) `{Eqb A} := A -> B.

Definition t_empty {A B : Type} `{Eqb A} (b : B) : total_map A B := (fun _ => b).

Definition t_update {A B : Type} `{Eqb A} (map : total_map A B) (a : A)(b : B) :=
  fun x => if (eqb x a) then b else map x.

(*Definition t_compose {A B C : Type} `{Eq A} (map1 map2 : total_map)*)

Definition partial_map (A B : Type) `{Eqb A} := total_map A (option B).

Definition empty {A B : Type} `{Eqb A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eqb A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).

Definition compose
           {A B C : Type} `{Eqb A} `{Eqb B}
           (map1 : partial_map A B)
           (map2 : partial_map B C) : partial_map A C :=
  fun a => match map1 a with
        | None => None
        | Some b => map2 b
        end.

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
| s_bind : list nat -> varSet.

Definition InΣ (n : nat)(Σ : varSet) :=
  match Σ with
  | s_hole _ => False
  | s_bind l => In n l
  end.