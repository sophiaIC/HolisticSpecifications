Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import fundamental_properties.
Require Import classical_properties.
Require Import rename_equality.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** #<h3># Expose example: #</h3># *)
(** ---------------------------------------------------- *)
(** #<code># >MyModule = { #</code># *)
(** #<code># >  Inside = {} #</code># *)
(** #<code># >  Boundary = { #</code># *)
(** #<code># >    field inside : Inside #</code># *)
(** #<code># >    meth expose() = {return this.inside} #</code># *)
(** #<code># >  } #</code># *)
(** #<code># >} #</code># *)
(** --------------------------------------------------- *)
(** #<code># we want to prove: #</code># *)
(**  *)
(** #<code># >MyModule ⊨  #</code># *)
(** #<code># >(∀ b, b : Boundary, ∀ i, (b.inside = i ∧ (∀ x, x access i ⇒ x = b)) #</code># *)
(** #<code># >             ⇒ (∀ p, will⟨ p access i ⟩ #</code># *)
(** #<code># >               ⇒ (∃ o, will⟨ o calls b.expose() ⟩))) #</code># *)
(**  *)
(**  *)

Definition InsideID := classID 6.

Definition Boundary := classID 7.

Definition InsideDef := clazz InsideID
                              nil
                              empty
                              empty.

Definition inside := fieldID 0.

Definition expose := methID 0.

Definition x := bnd 10.

Definition exposeBody := s_stmts (s_asgn (r_var x) (r_fld this inside))
                                 (s_rtrn x).

Definition BoundaryDef := clazz Boundary
                                (inside :: nil)
                                (update
                                   expose (nil, exposeBody)
                                   empty)
                                empty.

Definition MyModule := (update
                          Boundary BoundaryDef
                          (update
                             InsideID InsideDef
                             empty)).

Ltac sat_destruct :=
  match goal with
  | [Hand : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply and_iff in Hand;
                                       destruct Hand
  end.

Ltac frsh_auto :=
  match goal with
  | [Hfrsh : fresh_x _ _ (_ ∧ _) |- _] => apply fresh_and_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (_ ⇒ _) |- _] => apply fresh_arr_elim in Hfrsh; andDestruct
  | [Hfrsh : fresh_x _ _ (∀x∙ _) |- _] => apply fresh_all_elim in Hfrsh
  | [ |- fresh_x _ _ (_ ∧ _)] => apply fresh_and_intro
  | [ |- fresh_x _ _ (_ ⇒ _)] => apply fresh_arr_intro
  | [ |- fresh_x _ _ (∀x∙_)] => apply fresh_all_intro
  | [ Hfrsh : fresh_x ?x ?σ _ |- fresh_x ?x ?σ _] => auto; try (eapply fresh_notin; eauto)
  end.

Ltac a_intro :=
  match goal with
  | [|- _ ⦂ _ ◎ _ ⊨ (∀x∙ _)] => apply sat_all_x; intros; simpl
  | [|- _ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] => apply arr_prop1; intros; simpl
  end.

Ltac a_intros :=
  repeat a_intro.

Ltac a_prop :=
  repeat match goal with
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> and_iff in H;
                                           destruct H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ∧ _) |- _] => apply -> or_iff in H
         | [H : _ ⦂ _ ◎ _ ⊨ (_ ⇒ _) |- _] => rewrite -> arr_prop in H
         | [H : context[_ ⦂ _ ◎ _ ⊨ (_ ⇒ _)] |- _] => rewrite -> arr_prop in H
         | [H : _ ⦂ _ ◎ _ ⊨ (∀x∙_) |- _] => rewrite all_x_prop in H; simpl in H
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∧ _)] => apply sat_and
         | [|- _ ⦂ _ ◎ _ ⊨ (_ ∨ _)] => apply <- or_iff
         end.

Lemma expose_example :
  entails (∀x∙∀x∙
            ((a_class (e_hole 1) Boundary)
             ∧
             (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
            ∧
            (∀x∙((a_hole 0) access (a_hole 1) ⇒ (a_eq (e_hole 0) (e_hole 2)))))
          (∀x∙∀x∙
            ((a_class (e_hole 1) Boundary)
             ∧
             (a_eq (e_acc_f (e_hole 1) inside) (e_hole 0)))
            ∧(¬ ∃x∙(((a_hole 0) access (a_hole 1)) ∧ ¬(a_class (e_hole 0) Boundary)))).
Proof.
  auto.
  apply ent;
    intros.
  a_intros.
  repeat (a_prop;
          a_intros;
          auto).

  - unfold mapp, configMapStack in *;
      simpl in *.
    unfold mapp in *.
    apply sat_class with (α:=).

Qed.