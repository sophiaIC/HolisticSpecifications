Require Export Arith.
Require Import CpdtTactics.
Require Import List.

Inductive var : Type :=
| hole : nat -> var
| bind : nat -> var.

Class Eqb (A : Type) :=
  {eqb : A -> A -> bool}.

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

Definition InΣ (n : nat)(Σ : varSet) :=
  match Σ with
  | s_hole _ => False
  | s_bind l => In n l
  end.