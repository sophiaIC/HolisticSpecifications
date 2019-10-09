Require Export Arith.
Require Import CpdtTactics.
Require Import List.

Inductive var : Type :=
| bind : nat -> var.

Class Eqb (A : Type) :=
  {eqb : A -> A -> bool;
   eqb_refl : forall a, eqb a a = true;
   eqb_sym : forall a1 a2, eqb a1 a2 = eqb a2 a1;
   eqb_eq : forall a1 a2, eqb a1 a2 = true ->
                     a1 = a2;
   neq_eqb : forall a1 a2, a1 <> a2 ->
                      eqb a1 a2 = false;
   eqb_neq : forall a1 a2, eqb a1 a2 = false ->
                      a1 <> a2}.

Instance nat_Eqb : Eqb nat :=
  {eqb n m := n =? m;
   eqb_refl := Nat.eqb_refl;
   eqb_sym := Nat.eqb_sym}.
Proof.
  intros; apply beq_nat_eq; auto.
  apply Nat.eqb_neq.
  apply Nat.eqb_neq.
Defined.

Instance var_Eqb : Eqb var :=
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
    rewrite Nat.eqb_neq;
    crush.
  intros;
    destruct a1;
    destruct a2;
    rewrite Nat.eqb_neq in H;
    crush.
Defined.

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
| s_bind : list var -> varSet.

Definition InΣ (x : var)(Σ : varSet) :=
  match Σ with
  | s_hole _ => False
  | s_bind l => In x l
  end.