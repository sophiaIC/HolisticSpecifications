Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import specw.
Require Import List.
Require Export Coq.Lists.ListSet.

Module SpecWTactics(L : LanguageDef).

  Import L.
  Module L_SpecW := SpecW(L).
  Export L_SpecW.

  Open Scope specw_scope.
  Declare Scope specw_tactics_scope.

  Lemma aval_subst :
    forall x n v, ([x /s n](av_ v)) = (av_ v).
    auto.
  Qed.

  Lemma val_subst :
    forall x n v, ([x /s n] (e_val v)) = (e_val v).
    auto.
  Qed.

  Lemma var_subst :
    forall x n y, ([x /s n] (e_var y)) = (e_var y).
    auto.
  Qed.

  Lemma ehole_subst :
    forall v n, ([v /s n] (e_hole n)) = (e_val v).
    intros; simpl;
      rewrite <- beq_nat_refl;
      auto.
  Qed.

  Lemma ehole_neq_subst :
    forall v n m, n <> m -> ([v /s n] (e_hole m)) = (e_hole m).
    intros; simpl.
    apply <- Nat.eqb_neq in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma ahole_subst :
    forall v n, ([v /s n] (a♢ n)) = (av_ v).
    intros; simpl;
      rewrite <- beq_nat_refl;
      auto.
  Qed.

  Lemma ahole_neq_subst :
    forall v n m, n <> m -> ([v /s n] (a♢ m)) = (a♢ m).
    intros; simpl.
    apply <- Nat.eqb_neq in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma eq_subst :
    forall x n e1 e2, ([x /s n] (e_eq e1 e2)) =
                 (e_eq ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma lt_subst :
    forall x n e1 e2, ([x /s n] (e_lt e1 e2)) =
                 (e_lt ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma plus_subst :
    forall x n e1 e2, ([x /s n] (e_plus e1 e2)) =
                 (e_plus ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma minus_subst :
    forall x n e1 e2, ([x /s n] (e_minus e1 e2)) =
                 (e_minus ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma mult_subst :
    forall x n e1 e2, ([x /s n] (e_mult e1 e2)) =
                 (e_mult ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma div_subst :
    forall x n e1 e2, ([x /s n] (e_div e1 e2)) =
                 (e_div ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma if_subst :
    forall x n e e1 e2, ([x /s n] (e_if e e1 e2)) =
                   (e_if ([x /s n] e) ([x /s n] e1) ([x /s n] e2)).
    auto.
  Qed.

  Lemma fld_subst :
    forall x n e f, ([x /s n] (e_acc_f e f)) =
               (e_acc_f ([x /s n] e) f).
    auto.
  Qed.

  Lemma ghost_subst :
    forall x n e1 g e2, ([x /s n] (e_acc_g e1 g e2)) =
                   (e_acc_g ([x /s n] e1) g ([x /s n] e2)).
    auto.
  Qed.

  Lemma hole_subst :
    forall x n, ([x /s n](e_hole n)) = (e_val x).
    intros;
      simpl.
    rewrite <- beq_nat_refl;
      auto.
  Qed.

  Ltac exp_subst_simpl :=
    match goal with
    | [|- context [[ _ /s _] (e_val ?v')]] =>
      rewrite val_subst with (v:=v')
    | [H : context [[ _ /s _] (e_val ?v')] |- _] =>
      rewrite val_subst with (v:=v') in H

    | [|- context [[ _ /s _] (e_var ?z)]] =>
      rewrite var_subst with (y:=z)
    | [H : context [[ _ /s _] (e_var ?z)] |- _] =>
      rewrite var_subst with (y:=z) in H

    | [|- context [[ _ /s _] (e_eq ?e ?e')]] =>
      rewrite eq_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_eq ?e ?e')] |- _] =>
      rewrite eq_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_plus ?e ?e')]] =>
      rewrite plus_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_plus ?e ?e')] |- _] =>
      rewrite plus_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_minus ?e ?e')]] =>
      rewrite minus_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_minus ?e ?e')] |- _] =>
      rewrite minus_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_mult ?e ?e')]] =>
      rewrite mult_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_mult ?e ?e')] |- _] =>
      rewrite mult_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_div ?e ?e')]] =>
      rewrite div_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_div ?e ?e')] |- _] =>
      rewrite div_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_lt ?e ?e')]] =>
      rewrite lt_subst with (e1:=e)(e2:=e')
    | [H : context [[ _ /s _] (e_lt ?e ?e')] |- _] =>
      rewrite lt_subst with (e1:=e)(e2:=e') in H

    | [|- context [[ _ /s _] (e_if ?ea ?eb ?ec)]] =>
      rewrite if_subst with (e:=ea)(e1:=eb)(e2:=ec)
    | [H : context [[ _ /s _] (e_if ?ea ?eb ?ec)] |- _] =>
      rewrite if_subst with (e:=ea)(e1:=eb)(e2:=ec) in H

    | [|- context [[ _ /s _] (e_acc_f ?e' ?f')]] =>
      rewrite fld_subst with (e:=e')(f:=f')
    | [H : context [[ _ /s _] (e_acc_f ?e' ?f')] |- _] =>
      rewrite fld_subst with (e:=e')(f:=f') in H

    | [|- context [[ _ /s _] (e_acc_g ?e ?g' ?e')]] =>
      rewrite ghost_subst with (e1:=e)(e2:=e')(g:=g')
    | [H : context [[ _ /s _] (e_acc_g ?e ?g' ?e')] |- _] =>
      rewrite ghost_subst with (e1:=e)(e2:=e')(g:=g') in H

    | [|- context[[_ /s ?m] (e_hole ?m)]] =>
      rewrite ehole_subst
    | [H : context[[_ /s ?m] (e_hole ?m)] |- _] =>
      rewrite ehole_subst in H

    | [|- context[[_ /s _] (e_hole _)]] =>
      rewrite ehole_neq_subst;
      [|solve[auto]]
    | [H : context[[_ /s _] (e_hole _)] |- _] =>
      rewrite ehole_neq_subst in H;
      [|solve[auto]]
    end.

  Axiom functional_extensionality :
    forall {A B : Type} (f g : A -> B), (forall x, f x = g x) ->
           f = g.

  Lemma update_subst :
    forall {A B C D : Type}`{Eq A}`{Subst B C D}
      (f : partial_map A B) (a : A) (b : B) (c : C) (d : D),
      ([d /s c](⟦ a ↦ b ⟧ f)) =
      (⟦ a ↦ ([d /s c] b) ⟧ ([d /s c] f)).
    intros.
    apply functional_extensionality;
      intros;
      simpl.
    repeat map_rewrite.
    destruct (eqb x a);
      auto.
  Qed.

  Lemma a_val_update_subst :
    forall (f : partial_map name a_val) a  b c d,
      ([d /s c](⟦ a ↦ b ⟧ f)) =
      (⟦ a ↦ ([d /s c] b) ⟧ ([d /s c] f)).
    apply (update_subst).
  Qed.

  Lemma empty_subst :
    forall {A B C D}{HEq : Eq A}`{Subst B C D} (a : A)(b : B)(c : C)(d : D),
      ([d /s c] (@empty A B HEq)) = (@empty A B HEq).
    auto.
  Qed.

  Lemma a_val_empty_subst :
    forall c d,
      ([d /s c](@empty name a_val eqbName)) = (@empty name a_val eqbName).
    apply (empty_subst).
    * apply (n_ 0).
    * apply (av_ (v_true)).
  Qed.

  Ltac map_subst_simpl :=
    match goal with
    | [ |- context[[?v' /s ?n'] (⟦ ?x ↦ ?a' ⟧ ?β')]] =>
      rewrite update_subst with (v:=v')(a:=a')(n:=n')(β:=β')
    | [H : context[[?v' /s ?n'] (⟦ ?x ↦ ?a' ⟧ ?β')] |- _] =>
      rewrite update_subst with (v:=v')(a:=a')(n:=n')(β:=β') in H

    | [ |- context[[?v' /s ?n'] empty]] =>
      rewrite empty_subst with (v:=v')(n:=n')
    | [H : context[[?v' /s ?n'] empty] |- _] =>
      rewrite empty_subst with (v:=v')(n:=n') in H

    (* not sure why this doesn't follow immediately from the case for update_subst,
       but it seems to have issues with unification. maybe it can't find the Subst instance?
       not sure. This works for now
       TODO: Must look into this.
     *)
    | [ |- context[[?v' /s ?n'] (⟦ ?x ↦ ?a' ⟧ ?β')]] =>
      rewrite a_val_update_subst
    | [H : context[[?v' /s ?n'] (⟦ ?x ↦ ?a' ⟧ ?β')] |- _] =>
      rewrite a_val_update_subst in H

    | [ |- context[[?v' /s ?n'] empty]] =>
      rewrite a_val_empty_subst
    | [H : context[[?v' /s ?n'] empty] |- _] =>
      rewrite a_val_empty_subst in H
    end.

  Lemma and_subst :
    forall x n A1 A2, ([x /s n] A1 ∧ A2) = ([x /s n] A1) ∧ ([x /s n] A2).
    auto.
  Qed.

  Lemma or_subst :
    forall x n A1 A2, ([x /s n] A1 ∨ A2) = ([x /s n] A1) ∨ ([x /s n] A2).
    auto.
  Qed.

  Lemma all_subst :
    forall x n A, ([x /s n] ∀x.[A]) = ∀x.[([x /s S n] A)].
    auto.
  Qed.

  Lemma ex_subst :
    forall x n A, ([x /s n] ∃x.[A]) = ∃x.[([x /s S n] A)].
    auto.
  Qed.

  Lemma arr_subst :
    forall x n A1 A2, ([x /s n] A1 ⟶ A2) = ([x /s n] A1) ⟶ ([x /s n] A2).
    auto.
  Qed.

  Lemma exp_subst :
    forall x n e, ([x /s n] (a_exp e)) = a_exp ([x /s n] e).
    auto.
  Qed.

  Lemma access_subst :
    forall x n y z, ([x /s n] (y access z)) = ([x /s n] y) access ([x /s n] z).
    auto.
  Qed.

  Lemma calls_subst :
    forall x n y z m β, ([x /s n] (y calls z ◌ m ⟨ β ⟩)) =
                   ([x /s n] y) calls ([x /s n] z) ◌ m ⟨ [x /s n] β ⟩.
    auto.
  Qed.

  Lemma internal_subst :
    forall x n y, ([x /s n] (y internal)) =
             ([x /s n] y) internal.
    auto.
  Qed.

  Lemma external_subst :
    forall x n y, ([x /s n] (y external)) =
             ([x /s n] y) external.
    auto.
  Qed.

  Lemma class_subst :
    forall x n e C, ([x /s n] (a_class e C)) =
               a_class ([x /s n] e) C.
    auto.
  Qed.

  Lemma neg_subst :
    forall x n A, ([x /s n] (¬ A)) =
             ¬ ([x /s n] A).
    auto.
  Qed.

  Ltac asrt_subst_simpl :=
    match goal with
    | [|- context[[_ /s _] ?A ∧ ?A']] =>
      rewrite and_subst with (A1:=A)(A2:=A')
    | [H : context[[_ /s _] ?A ∧ ?A'] |- _] =>
      rewrite and_subst with (A1:=A)(A2:=A') in H

    | [|- context[[_ /s _] ?A ∨ ?A']] =>
      rewrite or_subst with (A1:=A)(A2:=A')
    | [H : context[[_ /s _] ?A ∨ ?A'] |- _] =>
      rewrite or_subst with (A1:=A)(A2:=A') in H

    | [|- context[[_ /s _] ?A ⟶ ?A']] =>
      rewrite arr_subst with (A1:=A)(A2:=A')
    | [H : context[[_ /s _] ?A ⟶ ?A'] |- _] =>
      rewrite arr_subst with (A1:=A)(A2:=A') in H

    | [|- context[[_ /s _] (∀x.[?A'])]] =>
      rewrite all_subst with (A:=A')
    | [H : context[[_ /s _] (∀x.[?A'])] |- _] =>
      rewrite all_subst with (A:=A') in H

    | [|- context[[_ /s _] (∃x.[?A'])]] =>
      rewrite ex_subst with (A:=A')
    | [H : context[[_ /s _] (∃x.[?A'])] |- _] =>
      rewrite ex_subst with (A:=A') in H

    | [|- context[[_ /s _] (¬ ?A')]] =>
      rewrite neg_subst with (A:=A')
    | [H : context[[_ /s _] (¬ ?A')] |- _] =>
      rewrite neg_subst with (A:=A') in H

    | [|- context[[_ /s _] (a_exp ?e')]] =>
      rewrite exp_subst with (e:=e')
    | [H : context[[_ /s _] (a_exp ?e')] |- _] =>
      rewrite exp_subst with (e:=e') in H

    | [|- context[[_ /s _] (a_class ?e' ?C')]] =>
      rewrite class_subst with (e:=e')
    | [H : context[[_ /s _] (a_class ?e' ?C')] |- _] =>
      rewrite class_subst with (e:=e')(C:=C') in H

    | [|- context[[_ /s _] (?y' access ?z')]] =>
      rewrite access_subst with (y:=y')(z:=z')
    | [H : context[[_ /s _] (?y' access ?z')] |- _] =>
      rewrite access_subst with (y:=y')(z:=z') in H

    | [|- context[[_ /s _] (?y' calls ?z' ◌ ?m' ⟨ ?β' ⟩)]] =>
      rewrite calls_subst with (y:=y')(z:=z')(m:=m')(β:=β')
    | [H : context[[_ /s _] (?y' calls ?z' ◌ ?m' ⟨ ?β' ⟩)] |- _] =>
      rewrite calls_subst with (y:=y')(z:=z')(m:=m')(β:=β') in H

    | [|- context[[_ /s _] (?y' internal)]] =>
      rewrite internal_subst with (y:=y')
    | [H : context[[_ /s _] (?y' internal)] |- _] =>
      rewrite internal_subst with (y:=y') in H

    | [|- context[[_ /s _] (?y' external)]] =>
      rewrite external_subst with (y:=y')
    | [H : context[[_ /s _] (?y' external)] |- _] =>
      rewrite external_subst with (y:=y') in H

    | [|- context [[ _ /s _] (e_acc_g ?e ?g' ?e')]] =>
      rewrite ghost_subst with (e1:=e)(e2:=e')(g:=g')
    | [H : context [[ _ /s _] (e_acc_g ?e ?g' ?e')] |- _] =>
      rewrite ghost_subst with (e1:=e)(e2:=e')(g:=g') in H

    | [|- context[[_ /s ?m] (a♢ ?m)]] =>
      rewrite ahole_subst
    | [H : context[[_ /s ?m] (a♢ ?m)] |- _] =>
      rewrite ahole_subst in H

    | [|- context[[_ /s _] (a♢ _)]] =>
      rewrite ahole_neq_subst;
      [|solve[auto]]
    | [H : context[[_ /s _] (a♢ _)] |- _] =>
      rewrite ahole_neq_subst in H;
      [|solve[auto]]

    | [|- context[[_ /s _] (av_ _)]] =>
      rewrite aval_subst
    | [H : context[[_ /s _] (av_ _)] |- _] =>
      rewrite aval_subst in H
    end.

  Lemma wrapped_subst :
    forall x n y, ([x /s n] (wrapped y)) = wrapped ([x /s S n] y).
  Proof.
    intros.
    unfold wrapped.
    repeat asrt_subst_simpl.
    auto.
  Qed.

  Ltac wrapped_subst_simpl :=
    match goal with
    | [|- context[([_ /s _] (wrapped _))]] =>
      rewrite wrapped_subst
    | [H : context[([_ /s _] (wrapped _))] |- _] =>
      rewrite wrapped_subst in H
    end.

  Ltac subst_simpl :=
    repeat (repeat (try (exp_subst_simpl));
            repeat  (try (asrt_subst_simpl));
            repeat (try (wrapped_subst_simpl));
            repeat (try (map_subst_simpl))).

  Lemma val_hole_subst :
    forall v n, ([v /s n] a♢ n) = (av_ v).
    intros; simpl.
    rewrite <- beq_nat_refl; auto.
  Qed.

  Lemma val_exp_hole_subst :
    forall v n, ([v /s n] e♢ n) = (e_val v).
    intros;
      simpl;
      rewrite <- beq_nat_refl; auto.
  Qed.

  Lemma aval_other_subst :
    forall x n v, ([x /s n] [v /s S n](a♢ S n)) = (av_ v).
    intros; simpl; rewrite <- beq_nat_refl;
      auto.
  Qed.

  Lemma eval_other_subst :
    forall x n v, ([x /s n] [v /s S n](e♢ S n)) = (e_val v).
    intros; simpl; rewrite <- beq_nat_refl;
      auto.
  Qed.

  Lemma ahole_other_subst :
    forall x n m, n <> m ->
             ([x /s n] (a♢ m)) = (a♢ m).
    intros x n m H;
      simpl.
    apply <- Nat.eqb_neq in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma subst_rewrite :
    forall{A B C: Type}`{Subst C B A} (a : A)(b : B)(c1 c2 : C),
      c1 = ([a /s b] c2) ->
      exists c3, c1 = ([a /s b] c3).
    intros; eauto.
  Qed.

  Lemma stupid_rename :
    forall {A : Type} (a : A), exists a', a' = a.
    eauto.
  Qed.

  Lemma stupid_rename_subst :
    forall {A B C}`{Subst C B A} (a : A) (b : B) (c : C),
    exists c', c = c' /\ (([a /s b] c) = ([a /s b] c')).
    eauto.
  Qed.

  Ltac extract_from_val v' n' :=
    match goal with
    | [|- context[av_ v']] =>
      rewrite <- val_hole_subst with (v:=v')(n:=n');
      let a := fresh "a" in
      remember (av_ v') as a
    | [|- context[e_val v']] =>
      rewrite <- val_exp_hole_subst with (v:=v')(n:=n');
      let e := fresh "e" in
      remember (e_val v') as e
    end.

  Ltac extract_other_vals v' n' :=
    match goal with
    | [|- context[av_ ?v'']] =>
      rewrite <- (aval_subst v' n' v'');
      let a := fresh "a" in
      remember (av_ v'') as a
    | [|- context[e_val ?v'']] =>
      rewrite <- (val_subst v' n' v'');
      let e := fresh "e" in
      remember (e_val v'') as e
    | [|- context[a♢ ?m']] =>
      rewrite <- (ahole_other_subst v' n' m');
      [|solve[auto]];
      let a := fresh "a" in
      let Ha := fresh "H" in
      destruct (stupid_rename (a♢ m')) as [a Ha];
      rewrite <-  Ha
    end.

  Ltac extract_vals v' n' :=
    repeat extract_from_val v' n';
    repeat extract_other_vals v' n'.

  Ltac extract_from_exp v' :=
    match goal with
    | [|- context[([v' /s ?n'] ?e1') ⩵ ([v' /s ?n'] ?e2')]] =>
      rewrite <- eq_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_plus ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2')]] =>
      rewrite <- plus_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_minus ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2')]] =>
      rewrite <- minus_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_mult ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2')]] =>
      rewrite <- mult_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_div ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2')]] =>
      rewrite <- div_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_lt ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2')]] =>
      rewrite <- lt_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')

    | [|- context[e_if ([v' /s ?n'] ?e1') ([v' /s ?n'] ?e2') ([v' /s ?n'] ?e3')]] =>
      rewrite <- if_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')(e3:=e3')

    | [|- context[e_acc_f ([v' /s ?n'] ?e') ?f']] =>
      rewrite <- fld_subst with (x:=v')(n:=n')(e:=e')(f:=f')

    | [|- context[e_acc_g ([v' /s ?n'] ?e1') ?g' ([v' /s ?n'] ?e2')]] =>
      rewrite <- ghost_subst with (x:=v')(n:=n')(e1:=e1')(e2:=e2')(g:=g')
    end.

  Ltac extract_from_map v' n' :=
    match goal with
    | [|-context[⟦ ?y ↦ [v' /s n'] ?v'' ⟧ ([v' /s n'] ?β')]] =>
      rewrite <- update_subst(*) with (v:=v')(a:=v'')(n:=n')(x:=y)(β:=β')*)
    | [|-context[empty]] =>
      rewrite <- empty_subst with (v:=v')(n:=n');
      let β'' := fresh "β" in
      remember empty as β''

    | [|-context[⟦ ?y ↦ [v' /s n'] ?v'' ⟧ ([v' /s n'] ?β')]] =>
      rewrite <- a_val_update_subst
    | [|-context[empty]] =>
      rewrite <- a_val_empty_subst with (c:=n')(d:=v');
      let β'' := fresh "β" in
      remember empty as β''
    end.

  Ltac extract_from_asrt v' :=
    match goal with
    | [|- context[a_exp ([v' /s ?n'] ?e')]] =>
      rewrite <- exp_subst (*)with (x:=v')(n:=n')(e:=e')*)

    | [|- context[(a_class ([v' /s ?n'] _) _)]] =>
      rewrite <- class_subst (*)with (x:=v')(n:=n')(A1:=A1')(A2:=A2')*)

    | [|- context[([v' /s ?n'] ?A1') ∧ ([v' /s ?n'] ?A2')]] =>
      rewrite <- and_subst (*)with (x:=v')(n:=n')(A1:=A1')(A2:=A2')*)

    | [|- context[([v' /s ?n'] ?A1') ∨ ([v' /s ?n'] ?A2')]] =>
      rewrite <- or_subst (*)with (x:=v')(n:=n')(A1:=A1')(A2:=A2')*)

    | [|- context[∀x.[([v' /s ?n'] ?A')]]] =>
      rewrite <- all_subst (*)with (x:=v')(n:=n')(A:=A')*)

    | [|- context[∃x.[([v' /s ?n'] ?A')]]] =>
      rewrite <- ex_subst (*)with (x:=v')(n:=n')(A:=A')*)

    | [|- context[[v' /s ?n']?A']] =>
      rewrite <- neg_subst (*)with (x:=v')(n:=n')(A:=A')*)

    | [|- context[([v' /s ?n']?y') internal]] =>
      rewrite <- internal_subst (*)with (x:=v')(n:=n')(y:=y')*)

    | [|- context[([v' /s ?n']?y') external]] =>
      rewrite <- external_subst (*)with (x:=v')(n:=n')(y:=y')*)

    | [|- context[([v' /s ?n'] ?y') access ([v' /s ?n'] ?z')]] =>
      rewrite <- access_subst (*)with (x:=v')(n:=n')(y:=y')(z:=z')*)

    | [|- context[([v' /s ?n'] ?y') calls ([v' /s ?n'] ?z') ◌ ?m' ⟨ [v' /s ?n'] ?β' ⟩]] =>
      rewrite <- calls_subst (*)with (x:=v')(n:=n')(y:=y')(z:=z')(m:=m')(β:=β')*)
    end.

  Ltac extract_from_wrapped v':=
    match goal with
    | [|- context[wrapped ([v' /s _] _)]] =>
      rewrite <- wrapped_subst
    | [H : context[wrapped ([v' /s _] _)] |- _] =>
      rewrite <- wrapped_subst in H
    end.

  Ltac subst_vals :=
    match goal with
    | [|- context[[?v' /s ?n'] (a♢ ?n)]] =>
      rewrite ahole_subst with (v:=v')(n:=n')
    | [|- context[[?v' /s ?n'] (e_hole ?n)]] =>
      rewrite hole_subst with (x:=v')(n:=n')
    end.

  Ltac extract v' n' :=
    repeat extract_vals v' n';
    repeat extract_other_vals v' n';
    repeat extract_from_exp v';
    repeat extract_from_map v' n';
    repeat (repeat extract_from_asrt v';
            repeat extract_from_wrapped v').

  (** Raise Simpl **)

  Lemma aval_raise :
    forall v n, ((av_ v) ↑ n) = (av_ v).
    auto.
  Qed.

  Lemma val_raise :
    forall v n, ((e_val v) ↑ n) = (e_val v).
    auto.
  Qed.

  Lemma var_raise :
    forall y n, ((e_var y) ↑ n) = (e_var y).
    auto.
  Qed.

  Lemma ehole_raise_le :
    forall n m, m <= n -> ((e_hole n) ↑ m) = (e_hole (S n)).
    intros; simpl.
    apply leb_correct in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma ehole_raise_gt :
    forall n m, m > n -> ((e_hole n) ↑ m) = (e_hole n).
    intros; simpl.
    apply <- Nat.leb_gt in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma ahole_raise_le :
    forall n m, m <= n -> ((a♢ n) ↑ m) = (a♢ S n).
    intros; simpl.
    apply leb_correct in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma ahole_raise_gt :
    forall n m,  m > n -> ((a♢ n) ↑ m) = (a♢ n).
    intros; simpl.
    apply <- Nat.leb_gt in H;
      rewrite H;
      reflexivity.
  Qed.

  Lemma eq_raise :
    forall n e1 e2, ((e_eq e1 e2) ↑ n) =
               (e_eq (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma lt_raise :
    forall n e1 e2, ((e_lt e1 e2) ↑ n) =
               (e_lt (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma plus_raise :
    forall n e1 e2, ((e_plus e1 e2) ↑ n) =
               (e_plus (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma minus_raise :
    forall n e1 e2, ((e_minus e1 e2) ↑ n) =
               (e_minus (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma mult_raise :
    forall n e1 e2, ((e_mult e1 e2) ↑ n) =
               (e_mult (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma div_raise :
    forall n e1 e2, ((e_div e1 e2) ↑ n) =
               (e_div (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma if_raise :
    forall n e e1 e2, ((e_if e e1 e2) ↑ n) =
                 (e_if (e ↑ n) (e1 ↑ n) (e2 ↑ n)).
    auto.
  Qed.

  Lemma fld_raise :
    forall n e f, ((e_acc_f e f) ↑ n) =
             (e_acc_f (e ↑ n) f).
    auto.
  Qed.

  Lemma ghost_raise :
    forall n e1 g e2, ((e_acc_g e1 g e2) ↑ n) =
                 (e_acc_g (e1 ↑ n) g (e2 ↑ n)).
    auto.
  Qed.

  Ltac exp_raise_simpl :=
    match goal with
    | [|- context [(e_val ?v') ↑ ?n]] =>
      rewrite val_raise
    | [H : context [(e_val ?v') ↑ ?n] |- _] =>
      rewrite val_raise in H

    | [|- context [(e_var ?z) ↑ _]] =>
      rewrite var_raise
    | [H : context [(e_var ?z) ↑ _] |- _] =>
      rewrite var_raise in H

    | [|- context [(e_eq ?e ?e') ↑ _ ]] =>
      rewrite eq_raise
    | [H : context [(e_eq ?e ?e') ↑ _ ] |- _] =>
      rewrite eq_raise in H

    | [|- context [(e_plus ?e ?e') ↑ _]] =>
      rewrite plus_raise
    | [H : context [(e_plus ?e ?e') ↑ _] |- _] =>
      rewrite plus_raise in H

    | [|- context [(e_minus ?e ?e') ↑ _]] =>
      rewrite minus_raise
    | [H : context [(e_minus ?e ?e') ↑ _] |- _] =>
      rewrite minus_raise in H

    | [|- context [(e_mult ?e ?e') ↑ _]] =>
      rewrite mult_raise
    | [H : context [(e_mult ?e ?e') ↑ _] |- _] =>
      rewrite mult_raise in H

    | [|- context [(e_div ?e ?e') ↑ _]] =>
      rewrite div_raise
    | [H : context [(e_div ?e ?e') ↑ _] |- _] =>
      rewrite div_raise in H

    | [|- context [(e_lt ?e ?e') ↑ _]] =>
      rewrite lt_raise
    | [H : context [(e_lt ?e ?e') ↑ _] |- _] =>
      rewrite lt_raise in H

    | [|- context [(e_if ?ea ?eb ?ec) ↑ _]] =>
      rewrite if_raise
    | [H : context [(e_if ?ea ?eb ?ec) ↑ _] |- _] =>
      rewrite if_raise in H

    | [|- context [(e_acc_f ?e' ?f') ↑ _]] =>
      rewrite fld_raise
    | [H : context [(e_acc_f ?e' ?f') ↑ _] |- _] =>
      rewrite fld_raise in H

    | [|- context [(e_acc_g ?e ?g' ?e') ↑ _]] =>
      rewrite ghost_raise
    | [H : context [(e_acc_g ?e ?g' ?e') ↑ _] |- _] =>
      rewrite ghost_raise in H

    | [Hle : ?m <= ?n |- context[(e_hole ?n) ↑ ?m]] =>
      rewrite (ehole_raise_le n m Hle)
    | [Hle : ?m <= ?n,
             H : context[(e_hole ?n) ↑ ?m] |- _] =>
      rewrite (ehole_raise_le n m Hle) in H

    | [Hgt : ?m > ?n |- context[(e_hole ?n) ↑ ?m]] =>
      rewrite (ehole_raise_gt n m Hgt)
    | [Hgt : ?m > ?n,
             H : context[(e_hole ?n) ↑ ?m] |- _] =>
      rewrite (ehole_raise_gt n m Hgt)
    end.

  Lemma update_raise :
    forall n x a (β : partial_map name a_val),
      ((⟦ x ↦ a ⟧ β)) ↑ n =
      (⟦ x ↦ (a ↑ n) ⟧ (β ↑ n)).
    intros.
    apply functional_extensionality;
      intros;
      simpl.
    repeat map_rewrite.
    destruct (eqb x0 x);
      auto.
  Qed.

  Lemma empty_raise :
    forall n, (empty ↑ n) = empty.
    auto.
  Qed.

  Ltac map_raise_simpl :=
    match goal with
    | [ |- context[(⟦ ?x ↦ ?a' ⟧ ?β') ↑ _]] =>
      rewrite update_raise
    | [H : context[(⟦ ?x ↦ ?a' ⟧ ?β') ↑ _] |- _] =>
      rewrite update_raise in H

    | [ |- context[empty ↑ _ ]] =>
      rewrite empty_raise
    | [H : context[empty ↑ _] |- _] =>
      rewrite empty_raise in H
    end.

  Lemma and_raise :
    forall n A1 A2, ((A1 ∧ A2) ↑ n) = (A1 ↑ n) ∧ (A2 ↑ n).
    auto.
  Qed.

  Lemma or_raise :
    forall n A1 A2, ((A1 ∨ A2) ↑ n) = (A1 ↑ n) ∨ (A2 ↑ n).
    auto.
  Qed.

  Lemma all_raise :
    forall n A, (∀x.[A] ↑ n) = ∀x.[A ↑ S n].
    auto.
  Qed.

  Lemma ex_raise :
    forall n A, (∃x.[A] ↑ n) = ∃x.[A ↑ S n].
    auto.
  Qed.

  Lemma arr_raise :
    forall n A1 A2, ((A1 ⟶ A2) ↑ n) = (A1 ↑ n) ⟶ (A2 ↑ n).
    auto.
  Qed.

  Lemma exp_raise :
    forall n e, ((a_exp e) ↑ n) = a_exp (e ↑ n).
    auto.
  Qed.

  Lemma access_raise :
    forall n x y, ((x access y) ↑ n) = (x ↑ n) access (y ↑ n).
    auto.
  Qed.

  Lemma calls_raise :
    forall n x y m β, ((x calls y ◌ m ⟨ β ⟩) ↑ n) =
                   (x ↑ n) calls (y ↑ n) ◌ m ⟨ β ↑ n ⟩.
    auto.
  Qed.

  Lemma internal_raise :
    forall x n, ((x internal) ↑ n) =
           (x ↑ n) internal.
    auto.
  Qed.

  Lemma external_raise :
    forall x n, ((x external) ↑ n) =
             (x ↑ n) external.
    auto.
  Qed.

  Lemma class_raise :
    forall n e C, ((a_class e C) ↑ n) =
             a_class (e ↑ n) C.
    auto.
  Qed.

  Lemma neg_raise :
    forall n A, ((¬ A) ↑ n) =
           ¬ (A ↑ n).
    auto.
  Qed.

  Ltac asrt_raise_simpl :=
    match goal with
    | [|- context[(?A ∧ ?A') ↑ _]] =>
      rewrite and_raise
    | [H : context[(?A ∧ ?A') ↑ _] |- _] =>
      rewrite and_raise in H

    | [|- context[(?A ∨ ?A') ↑ _ ]] =>
      rewrite or_raise
    | [H : context[(_ ∨ _) ↑ _] |- _] =>
      rewrite or_raise in H

    | [|- context[(?A ⟶ ?A') ↑ _ ]] =>
      rewrite arr_raise
    | [H : context[(_ ⟶ _) ↑ _] |- _] =>
      rewrite arr_raise in H

    | [|- context[(∀x.[?A']) ↑ _ ]] =>
      rewrite all_raise
    | [H : context[(∀x.[?A']) ↑ _] |- _] =>
      rewrite all_raise in H

    | [|- context[(∃x.[?A']) ↑ _]] =>
      rewrite ex_raise
    | [H : context[(∃x.[?A']) ↑ _] |- _] =>
      rewrite ex_raise in H

    | [|- context[(¬ ?A') ↑ _]] =>
      rewrite neg_raise
    | [H : context[(¬ ?A') ↑ _] |- _] =>
      rewrite neg_raise in H

    | [|- context[(a_exp ?e') ↑ _]] =>
      rewrite exp_raise
    | [H : context[(a_exp ?e') ↑ _ ] |- _] =>
      rewrite exp_raise in H

    | [|- context[(a_class ?e' ?C') ↑ _ ]] =>
      rewrite class_raise
    | [H : context[(a_class ?e' ?C') ↑ _ ] |- _] =>
      rewrite class_raise in H

    | [|- context[(?y' access ?z') ↑ _ ]] =>
      rewrite access_raise
    | [H : context[(?y' access ?z') ↑ _] |- _] =>
      rewrite access_raise in H

    | [|- context[(?y' calls ?z' ◌ ?m' ⟨ ?β' ⟩) ↑ _ ]] =>
      rewrite calls_raise
    | [H : context[(?y' calls ?z' ◌ ?m' ⟨ ?β' ⟩) ↑ _ ] |- _] =>
      rewrite calls_raise in H

    | [|- context[(?y' internal) ↑ _ ]] =>
      rewrite internal_raise
    | [H : context[(?y' internal) ↑ _ ] |- _] =>
      rewrite internal_raise in H

    | [|- context[(?y' external) ↑ _ ]] =>
      rewrite external_raise
    | [H : context[(?y' external) ↑ _ ] |- _] =>
      rewrite external_raise in H

    | [|- context [(e_acc_g ?e ?g' ?e') ↑ _ ]] =>
      rewrite ghost_raise
    | [H : context [(e_acc_g ?e ?g' ?e') ↑ _ ] |- _] =>
      rewrite ghost_raise  in H

    | [Hle : ?m <= ?n |- context[(a♢ ?n) ↑ ?m]] =>
      rewrite (ahole_raise_le n m Hle)
    | [Hle : ?m <= ?n,
             H : context[(a♢ ?n) ↑ ?m] |- _] =>
      rewrite (ahole_raise_le n m Hle) in H

    | [Hgt : ?m > ?n |- context[(a♢ ?n) ↑ ?m]] =>
      rewrite (ahole_raise_gt n m Hgt)
    | [Hgt : ?m > ?n,
             H : context[(a♢ ?n) ↑ ?m] |- _] =>
      rewrite (ahole_raise_gt n m Hgt) in H

    | [|- context[(av_ _) ↑ _ ]] =>
      rewrite aval_raise
    | [H : context[(av_ _) ↑ _] |- _] =>
      rewrite aval_raise in H
    end.

  Lemma wrapped_raise :
    forall n y, ((wrapped y) ↑ n) = wrapped (y ↑ S n).
  Proof.
    intros.
    unfold wrapped.
    repeat asrt_raise_simpl.
    auto.
  Qed.

  Ltac wrapped_raise_simpl :=
    match goal with
    | [|- context[((wrapped _) ↑ _ )]] =>
      rewrite wrapped_raise
    | [H : context[((wrapped _) ↑ _)] |- _] =>
      rewrite wrapped_raise in H
    end.

  Ltac raise_simpl :=
    repeat (repeat (try (exp_raise_simpl));
            repeat  (try (asrt_raise_simpl));
            repeat (try (wrapped_raise_simpl));
            repeat (try (map_raise_simpl))).

  Lemma exp_subst_raise_lt :
    forall (e : exp) v n m, n < m -> ([v /s n] (e ↑ m)) = (([v /s n] e) ↑ m).
  Proof.
    intro e;
      induction e;
      intros;
      repeat (subst_simpl;
              raise_simpl);
      auto;
      try solve [try (rewrite IHe1);
                 try (rewrite IHe2);
                 try (rewrite IHe3);
                 try (rewrite IHe);
                 auto].

    * destruct (le_lt_dec m n);
        raise_simpl.
      ** assert (n0 <> S n /\ n0 <> n);
           [crush|andDestruct].
         subst_simpl;
           raise_simpl;
           auto.
      ** rewrite ehole_raise_gt;
           auto.
         destruct (eq_dec n n0);
           subst.
         *** subst_simpl;
               raise_simpl;
               auto.
         *** subst_simpl.
             rewrite ehole_raise_gt;
               auto.

  Qed.

End SpecWTactics.
