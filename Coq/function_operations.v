Require Import common.
Require Import loo_def.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac destruct_exists :=
  match goal with
  | [H : exists _, _ |- _] => destruct H
  end.

Ltac map_rewrite :=
  match goal with
  | [H : context[mapp _ _] |-_] => unfold mapp in H
  | [|- context[mapp _ _]] => unfold mapp
  | [H : context[update_σ_map _ _] |-_] => unfold update_σ_map in H
  | [|- context[update_σ_map _ _]] => unfold update_σ_map
  | [H : context[update_ψ_map _ _] |-_] => unfold update_ψ_map in H
  | [|- context[update_ψ_map _ _]] => unfold update_ψ_map
  | [H : context[configMapStack _ _] |-_] => unfold configMapStack in H
  | [|- context[configMapStack _ _]] => unfold configMapStack
  | [H : context[stackMap _ _] |-_] => unfold stackMap in H
  | [|- context[stackMap _ _]] => unfold stackMap
  | [H : context[update _ _] |-_] => unfold update in H
  | [|- context[update _ _]] => unfold update
  | [H : context[t_update _ _] |-_] => unfold t_update in H
  | [|- context[t_update _ _]] => unfold t_update
  | [H : context[empty] |-_] => unfold empty in H
  | [|- context[empty]] => unfold empty
  | [H : context[t_empty] |-_] => unfold t_empty in H
  | [|- context[t_empty]] => unfold t_empty
  end.

Ltac eq_auto :=
  match goal with
  | [Heq : ?a1 <> ?a2, Heqb : context[eqb ?a1 ?a2]|- _] => rewrite neq_eqb in Heqb; auto
  | [Heq : ?a1 <> ?a2, Heqb : context[eqb ?a2 ?a1]|- _] => rewrite eqb_sym in Heqb;
                                                        rewrite neq_eqb in Heqb; auto
  | [Heq : ?a1 <> ?a2 |- context[eqb ?a1 ?a2]] => rewrite neq_eqb; auto
  | [Heq : ?a1 <> ?a2 |- context[eqb ?a2 ?a1]] => rewrite eqb_sym;
                                               rewrite neq_eqb; auto

  | [Heqb : context[eqb ?a ?a]|- _] => rewrite eqb_refl in Heqb; auto
  | [|- context[eqb ?a ?a]] => rewrite eqb_refl; auto
  | [H : eqb ?a1 ?a2 = true |- _] =>
    let Hnew := fresh in
    assert (Hnew : a1 = a2);
    [eapply eqb_eqp in H; auto|subst; auto]
  | [H : eqb ?a1 ?a2 = false |- _] =>
    let Hnew := fresh in
    assert (Hnew : a1 <> a2);
    [eapply eqb_neq in H; auto|auto]

  | [H : Some ?a1 <> Some ?a2 |- _] =>
    notHyp (a1 <> a2);
    assert (a1 <> a2);
    [intro Hcontra; subst; crush|auto]
  end.

Ltac empty_auto :=
  match goal with
  | [H : context [empty _] |- _] => unfold empty, t_empty in H; crush
  | [|- context [empty _]] => unfold empty, t_empty; crush
  end.

Ltac update_auto :=
  match goal with
  | [H : (update ?a _ _) ?a = Some ?b' |- _] => unfold update, t_update in H;
                                              subst; rewrite eqb_refl in H;
                                              inversion H; subst
  | [Hneq : ?a <> ?a', H : (update ?a _ _) ?a' = Some _ |- _] => unfold update, t_update in H;
                                                              apply neq_eqb in Hneq;
                                                              rewrite Hneq in H
  | [Hneq : ?a' <> ?a, H : (update ?a _ _) ?a' = Some _ |- _] => unfold update, t_update in H;
                                                              apply neq_eqb in Hneq;
                                                              rewrite Hneq in H
  | [H : (update ?a _ _) ?a' = Some ?b' |- _] => unfold update, t_update in H;
                                               let Heq := fresh "Heq" in
                                               let Hneq := fresh "Hneq" in
                                               destruct (eq_dec a' a) as [Heq|Hneq];
                                               [subst; rewrite eqb_refl in H;
                                                inversion H; subst
                                               |apply neq_eqb in Hneq;
                                                rewrite Hneq in H]

  | [H : context[(update ?a _ _) ?a]  |- _] => unfold update, t_update in H;
                                             subst; rewrite eqb_refl in H
  | [Hneq : ?a <> ?a', H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                                               apply neq_eqb in Hneq;
                                                               rewrite Hneq in H
  | [Hneq : ?a' <> ?a, H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                                               apply neq_eqb in Hneq;
                                                               rewrite Hneq in H
  | [H : context[(update ?a _ _) ?a']  |- _] => unfold update, t_update in H;
                                              let Heq := fresh "Heq" in
                                              let Hneq := fresh "Hneq" in
                                              destruct (eq_dec a' a) as [Heq|Hneq];
                                              [subst; rewrite eqb_refl in H
                                              |apply neq_eqb in Hneq;
                                               rewrite Hneq in H]
                                                     
  | [|- (update ?a _ _) ?a = Some _] => unfold update, t_update;
                                      subst; rewrite eqb_refl
  | [Hneq : ?a <> ?a' |- (update ?a _ _) ?a' = Some _] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [Hneq : ?a' <> ?a |- (update ?a _ _) ?a' = Some _] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [|- (update ?a _ _) ?a' = Some ?b'] => unfold update, t_update;
                                         let Heq := fresh "Heq" in
                                         let Hneq := fresh "Hneq" in
                                         destruct (eq_dec a' a) as [Heq|Hneq];
                                         [subst; rewrite eqb_refl
                                         |apply neq_eqb in Hneq;
                                          rewrite Hneq]
                                                
  | [|- context[(update ?a _ _) ?a]] => unfold update, t_update;
                                      subst; rewrite eqb_refl
  | [Hneq : ?a <> ?a' |- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [Hneq : ?a' <> ?a |- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                                       apply neq_eqb in Hneq;
                                                       rewrite Hneq
  | [|- context[(update ?a _ _) ?a']] => unfold update, t_update;
                                       let Heq := fresh "Heq" in
                                       let Hneq := fresh "Hneq" in
                                       destruct (eq_dec a' a) as [Heq|Hneq];
                                       [subst; rewrite eqb_refl
                                       |apply neq_eqb in Hneq;
                                        rewrite Hneq]

  | [H : context[empty _]|-_] => unfold empty, t_empty in H
  | [|- context[empty _]] => unfold empty, t_empty
  end;
  auto.

Ltac pmap_simpl :=
  repeat (try empty_auto;
          try update_auto).

Definition one_to_one {A B : Type} `{Eq A} (f : partial_map A B) :=
  forall a1 a2 b, f a1 = Some b ->
             f a2 = Some b ->
             a1 = a2.

Instance optionEq {A : Type}`{Eq A} : Eq (option A) :=
  {
    eqb o1 o2 := match o1, o2 with
                 | Some b1, Some b2 => eqb b1 b2
                 | None, None => true
                 | _, _ => false
                 end
  }.
Proof.
  - intros.
    match goal with
    | [A : Type,
           a : option A |- _] => destruct a; eauto
    end.

  - intros.
    match goal with
    | [A : Type,
           a1 : option A,
                a2 : option A |- _] => destruct a1; destruct a2; eauto
    end.

  - intros;
      match goal with
      | [A : Type,
             a1 : option A,
                  a2 : option A |- _] => destruct a1; destruct a2; auto
      end;
      try solve [eq_auto];
      try solve [crush].

  - intros;
      match goal with
      | [A : Type,
             a1 : option A,
                  a2 : option A |- _] => destruct a1; destruct a2; auto
      end;
      try eq_auto;
      try solve [crush].

  - intros;
      match goal with
      | [A : Type,
             a1 : option A,
                  a2 : option A |- _] => destruct a1; destruct a2; auto
      end;
      try solve [eq_auto];
      try solve [crush].

  - intros;
      match goal with
      | [A : Type,
             a1 : option A,
                  a2 : option A |- _] => destruct a1; destruct a2; auto
      end;
      try solve [right; crush].
    destruct (eq_dec a a0);
      [subst; auto|right]; crush.
Defined.

Lemma partial_map_dec :
  forall {A B : Type} `{Eq A} a (m : partial_map A B), {exists b, m a = Some b} + {m a = None}.
Proof.
  intros.
  destruct (m a) as [b|]; [left; exists b|]; crush.
Qed.

Lemma not_some_implies_none :
  forall {A B : Type} `{Eq A} (f : partial_map A B) a,
    (forall b, ~ f a = Some b) ->
    f a = None.
Proof.
  intros.
  destruct (partial_map_dec a f); auto.
  destruct_exists.
  crush.
Qed.

Lemma not_none_implies_some :
  forall {A : Type} `{Eq A}(B : Type) (f : partial_map A B) a,
    f a <> None ->
    exists b, f a = Some b.
Proof.
  intros.
  destruct (partial_map_dec a f); auto; crush.
Qed.

Hint Rewrite not_none_implies_some.
Hint Resolve not_none_implies_some.

Lemma in_map_implies_in_dom :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a b, m a = Some b ->
           In a d.
Proof.
  intros A B HeqClass m d Hdom;
    induction Hdom;
    intros;
    try solve [pmap_simpl; crush; eauto].
Qed.

Lemma in_dom_implies_in_map :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a, In a d ->
    exists b, m a = Some b.
Proof.
  intros.
  unfold dom in *.
  andDestruct.
  auto.
Qed.

Lemma not_in_map_implies_not_in_dom :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a, m a = None ->
           ~ In a d.
Proof.
  intros;
    intros Hcontra.
  unfold dom in *;
    andDestruct.
  match goal with
  | [Hin : In ?a ?d,
           Hmap : ?m ?a = None,
                  H : forall a', In a' ?d -> exists b, ?m a' = Some b |- _] =>
    apply H in Hin;
      destruct_exists;
      crush
  end.
Qed.

Lemma not_in_dom_implies_not_in_map :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    forall a, ~ In a d ->
         m a = None.
Proof.
  intros.
  apply not_some_implies_none;
    intros;
    intro Hcontra.
  eapply in_map_implies_in_dom in Hcontra; eauto.
Qed.

Lemma exists_dom_finite :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    exists d, dom m d.
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    [exists nil;
       unfold dom;
       split;
       [|split];
       intros;
       auto;
       repeat map_rewrite;
       crush
      |].

  destruct IHHfinite as [d Hdom].
  destruct (excluded_middle (In a d)) as [Hin|Hnin];
    [exists d|exists (a::d)];
    auto;
    unfold dom;
    split;
    try split;
    intros;
    repeat map_rewrite;
    auto;
    try solve [destruct (eq_dec a0 a);
               subst;
               eq_auto;
               unfold dom in *;
               andDestruct;
               eauto];
    try solve [unfold dom in *;
               andDestruct;
               auto].
  destruct (eq_dec a0 a) as [|Hneq];
    subst;
    eq_auto;
    [apply in_eq|apply in_cons].
  unfold dom in *;
    andDestruct;
    eauto.
  match goal with
  | [H1 : In ?a0 (?a::?d),
          H2 : ~ In ?a ?d |- _] => inversion H1; subst
  end.
  eq_auto; eexists; eauto.
  destruct (eq_dec a0 a) as [|Hneq];
    subst;
    eq_auto; [crush|].
  unfold dom in *;
    andDestruct;
    eauto.
Qed.

Lemma update_neq_empty :
  forall {A B : Type}`{Eq A} (a : A)(b : B) m,
    update a b m <> empty.
Proof.
  intros; intros Hcontra.
  assert (Heq : update a b m a = None);
    [rewrite Hcontra; pmap_simpl|pmap_simpl].
  crush.
Qed.

Ltac update_empty_contra :=
  match goal with
  | [H : update ?a ?b ?m = empty |- _] => contradiction (update_neq_empty a b m)
  | [H : empty = update ?a ?b ?m |- _] => symmetry in H; contradiction (update_neq_empty a b m)
  end.

Lemma dom_empty_is_nil :
  forall {A B : Type}`{Eq A} (m : partial_map A B) d,
    dom m d ->
    m = empty ->
    d = nil.
Proof.
  intros A B HeqClass m d H;
    intros;
    subst;
    unfold dom in *;
    andDestruct.
  destruct d as [|a d'];
    auto.
  assert (exists b : B, empty a = Some b);
    [apply Ha0, in_eq|].
  destruct_exists.
  repeat map_rewrite; crush.
Qed.

Ltac finite_auto :=
  repeat match goal with
         | [H : context[finite_σ _] |- _] => unfold finite_σ in H
         | [H : context[finite_ψ _] |- _] => unfold finite_ψ in H
         | [H : context[finite_ϕ _] |- _] => unfold finite_ϕ in H
         | [|- context[finite_σ _]] => unfold finite_σ
         | [|- context[finite_ψ _]] => unfold finite_ψ
         | [|- context[finite_ϕ _]] => unfold finite_ϕ
         end.

Ltac not_stuck_auto :=
  repeat match goal with
         | [H : context[not_stuck_σ _] |- _] => unfold not_stuck_σ in H
         | [H : context[not_stuck_ϕ _] |- _] => unfold not_stuck_ϕ in H
         | [|- context[not_stuck_σ _]] => unfold not_stuck_σ
         | [|- context[not_stuck_ϕ _]] => unfold not_stuck_ϕ
         end.

Ltac waiting_auto :=
  repeat match goal with
         | [H : context[waiting_σ _] |- _] => unfold waiting_σ in H
         | [H : context[waiting_ψ _] |- _] => unfold waiting_ψ in H
         | [H : context[waiting_ϕ _] |- _] => unfold waiting_ϕ in H
         | [|- context[waiting_σ _]] => unfold waiting_σ
         | [|- context[waiting_ψ _]] => unfold waiting_ψ
         | [|- context[waiting_ϕ _]] => unfold waiting_ϕ
         end.

Lemma dom_unique :
  forall {A B : Type} `{Eq A} (m : partial_map A B) d,
    dom m d ->
    unique d.
Proof.
  intros A B HeqClass m d Hdom;
    unfold dom in *;
    andDestruct;
    auto.
Qed.

Inductive finite_normal_form {A B : Type} `{Eq A} : partial_map A B -> Prop :=
| norm_empty : finite_normal_form empty
| norm_update : forall a b m, finite_normal_form m ->
                         m a = None ->
                         finite_normal_form (update a b m).

Hint Constructors finite_normal_form.

Lemma compose_normal_form :
  forall {A B : Type}`{Eq A}`{Eq B} (m1 : partial_map A B),
    finite_normal_form m1 ->
    forall {C : Type} (m2 : partial_map B C),
    exists m3, finite_normal_form m3 /\ m3 = m1 ∘ m2.
Proof.
  intros A B HeqClassA HeqClassB m1 Hnorm;
    induction Hnorm;
    intros;
    auto.

  exists empty; auto.

  destruct (IHHnorm C m2) as [m3 IH];
    destruct IH as [IH1 IH2].
  destruct (partial_map_dec b m2)
    as [HSome|HNone];
    [destruct HSome as [c HSome]|].
  exists (update a c m3);
    split;
    [apply norm_update;
     subst m3; [auto|crush]|].
  apply functional_extensionality;
    intros a';
    pmap_simpl;
    crush.
  exists m3;
    split;
    auto.
  subst; auto.
  apply functional_extensionality;
    intros c;
    pmap_simpl;
    crush.
Qed.

Lemma update_finite_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite_normal_form m ->
    forall a b, exists m', finite_normal_form m' /\ m' = (update a b m).
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    intros;
    [exists (update a b empty); auto|].

  destruct (IHHfinite a0 b0) as [m' Hnorm];
    destruct Hnorm as [Hnorm Heqm'].

  destruct (eq_dec a0 a) as [Heq|Hneq];
    [subst a0
    |].

  exists m'; split; auto;
    apply functional_extensionality;
    intros a';
    subst;
    pmap_simpl.

  exists (update a b m');
    split.

  destruct (partial_map_dec a m') as [HSome|HNone];
    [destruct HSome as [b' HSome]; subst; pmap_simpl; crush
    |apply norm_update; auto].

  apply functional_extensionality; intros a'; pmap_simpl; subst.
  rewrite neq_eqb; auto.
  destruct (eq_dec a' a0) as [Heqa'|Hneqa'];
    [subst; pmap_simpl|pmap_simpl].
Qed.

Lemma finite_exists_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    exists m', finite_normal_form m' /\ m' = m.
Proof.
  intros A B HeqClass m Hfinite;
    induction Hfinite;
    [exists empty; auto|].

  apply update_finite_normal_form; crush.
Qed.

Lemma finite_normal_form_implies_finite :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite_normal_form m ->
    finite m.
Proof.
  intros A B HeqClass m Hnorm;
    induction Hnorm;
    auto.
Qed.

Lemma finite_implies_normal_form :
  forall {A B : Type} `{Eq A} (m : partial_map A B),
    finite m ->
    finite_normal_form m.
Proof.
  intros.
  destruct (finite_exists_normal_form m);
    andDestruct;
    subst;
    auto.
Qed.

Hint Resolve finite_implies_normal_form finite_exists_normal_form finite_normal_form_implies_finite
     compose_normal_form.

Lemma finite_map_composition :
  forall {A B : Type}`{Eq A}`{Eq B} (m1 : partial_map A B),
    finite m1 ->
    forall {C : Type} (m2 : partial_map B C),
      finite (m1 ∘ m2).
Proof.
  intros.
  destruct (compose_normal_form m1 (finite_implies_normal_form m1 H1) m2); eauto.
  andDestruct; subst.
  apply finite_normal_form_implies_finite; auto.
Qed.

Lemma one_to_one_f_nequal :
  forall {A B : Type}`{Eq A} (f : partial_map A B),
    one_to_one f ->
    forall a1 a2, a1 <> a2 ->
             (exists b, f a1 = Some b) ->
             f a1 <> f a2.
Proof.
  intros A B H f H1t1 a1 a2 Hneq Hex Hcontra.
  destruct (partial_map_dec a1 f) as [Hsome1|Hnone1];
    [destruct_exists|].
  - destruct (partial_map_dec a2 f) as [Hsome2|Hnone2];
      [destruct_exists|crush].
    + rewrite Hcontra in H0;
        rewrite H0 in H1;
        inversion H1;
        subst.
      assert (a1 = a2);
        [unfold one_to_one in H1t1; apply H1t1 with (b:=x0)|];
        crush.
  - destruct (partial_map_dec a2 f) as [Hsome2|Hnone2];
      [crush|].
    destruct_exists; crush.
Qed.

Lemma bind_compose_application :
  forall {A B : Type}`{Eq A}`{Eq B}(C : Type) (f1 f2 : partial_map A B)(g : partial_map B C),
    f1 ∘ g = f2 ∘ g <->
    forall a, bind (f1 a) g = bind (f2 a) g.
Proof.
  intros; auto; split; intros; auto.
  - match goal with
    | [H : ?f1 ∘ ?g = ?f2 ∘ ?g |- bind (?f1 ?a) ?g = bind (?f2 ?a) ?g] =>
      apply equal_f with (x:=a) in H; auto
    end.
  - apply functional_extensionality; auto.
Qed.

Hint Resolve bind_compose_application.
Hint Rewrite bind_compose_application.

Lemma one_to_one_bind_f_nequal :
  forall {A B : Type}`{Eq A} (f : partial_map A B),
    one_to_one f ->
    forall a1 a2, a1 <> a2 ->
             (exists b, bind a1 f = Some b) ->
             bind a1 f <> bind a2 f.
Proof.
  intros A B H f H1t1 a1 a2 Hneq Hex Hcontra.

  destruct (a1);
    destruct (a2); auto;
      destruct_exists;
      crush.
  contradiction Hneq.
  erewrite H1t1 with (a1:=a)(a2:=a0); eauto; crush.
Qed.

Ltac maps_into_from_auto :=
  match goal with
  | [Ha : maps_into ?f ?g,
          Hb : ?f ?a = Some ?b |- _] =>
    match goal with
    | [Hex : g b = Some _ |- _] => fail 1
    | _ => destruct (Ha a b); auto
    end
  | [Ha : maps_from ?g ?f,
          Hb : ?g ?b = Some ?c |- _] =>
    match goal with
    | [Hex : f _ = Some b |- _] => fail 1
    | _ => destruct (Ha b c); auto
    end
  end.

Ltac eq_explode :=
  match goal with
  | [Heq : Eq ?A,
           a1 : ?A,
                a2 : ?A |- _] =>
    notHyp (a1 <> a2);
    notHyp (a2 <> a1);
    let Hneq := fresh "Hneq" in
    destruct (eq_dec a1 a2) as [|Hneq];
    subst
  end.

Ltac option_crush :=
  match goal with
  | [H : Some _ = None |- _] => crush
  | [H : None = Some _ |- _] => crush

  | [Ha : ?x = Some _,
          Hb : ?x = None |- _] => crush
  | [Ha : ?x = Some _,
          Hb : None = ?x |- _] => crush
  | [Ha : Some _ = ?x,
          Hb : ?x = None |- _] => crush
  | [Ha : Some _ = ?x,
          Hb : None = ?x |- _] => crush

  | [H : Some _ = Some _ |- _] => inversion H; subst; clear H
  | [Ha : ?x = Some _,
          Hb : ?x = Some _ |- _] => rewrite Ha in Hb;
                                  inversion Hb; subst
  end.

Ltac auto_specialize :=
  match goal with
  | [H : ?P -> ?Q,
         H' : ?P |- _ ] => specialize (H H')
  end.

Definition inv {A B : Type}`{Eq A}`{Eq B}(f : partial_map A B)(f' : partial_map B A) :=
  (forall a b, f a = Some b ->
          f' b = Some a) /\
  (forall a b, f' b = Some a ->
          f a = Some b).

Lemma inv_empty :
  forall{A B : Type}{HeqA : Eq A}{HeqB : Eq B},
    @inv A B HeqA HeqB empty empty.
Proof.
  intros;
    unfold inv;
    split;
    intros;
    repeat map_rewrite;
    crush.
Qed.

Hint Resolve inv_empty.

Ltac inv_auto :=
  match goal with
  | [Hinv : inv ?f ?f',
            H : ?f ?a = Some ?b |- _] =>
    notHyp (f' b = Some a);
    assert (f' b = Some a);
    [unfold inv in Hinv; andDestruct; crush|]
  | [Hinv : inv ?f ?f',
            H : ?f' ?a = Some ?b |- _] =>
    notHyp (f b = Some a);
    assert (f b = Some a);
    [unfold inv in Hinv; andDestruct; crush|]
  end.

Lemma inv_one_to_one_1 :
  forall {A B : Type}`{Eq A}`{Eq B}
    (f : partial_map A B) (f' : partial_map B A),
    inv f f' ->
    one_to_one f.
Proof.
  intros A B HeqA HeqB f f' Hinv;
    unfold one_to_one; intros.
  repeat inv_auto;
    repeat option_crush;
    auto.
Qed.

Lemma inv_one_to_one_2 :
  forall {A B : Type}`{Eq A}`{Eq B}
    (f : partial_map A B) (f' : partial_map B A),
    inv f f' ->
    one_to_one f'.
Proof.
  intros A B HeqA HeqB f f' Hinv.

  unfold one_to_one; intros.
  unfold inv in *.
  andDestruct.
  match goal with
  | [H : forall a b, ?f' b = Some a -> ?f a = Some b,
       Ha : ?f' ?a1 = Some ?b',
       Hb : ?f' ?a2 = Some ?b' |-_] =>
    apply H in Ha;
      apply H in Hb;
      rewrite Hb in Ha;
      crush
  end.
Qed.

Lemma one_to_one_empty :
  forall {A B : Type}{Heq : Eq A},
    @one_to_one A B Heq empty.
Proof.
  intros;
    unfold one_to_one;
    intros;
    repeat map_rewrite;
    crush.
Qed.

Hint Resolve one_to_one_empty.

Lemma one_to_one_fnf_update :
  forall {A B : Type}`{Eq A} (f : partial_map A B),
    finite_normal_form f ->
    forall a b, (one_to_one (update a b f)) ->
           f a = None ->
           one_to_one f.
Proof.
  intros A B HeqA f Hfin;
    induction Hfin;
    intros;
    auto.
  unfold one_to_one;
    intros.
  repeat map_rewrite.
  repeat eq_explode;
    repeat eq_auto;
    auto;
    repeat option_crush.

  - match goal with
    | [H : one_to_one (fun _ => if _ then _ else if _ then Some ?b' else _) |- ?a1 = ?a2] =>
      apply H with (b:=b')
    end;
      repeat eq_auto.

  - match goal with
    | [H : one_to_one (fun _ => if _ then _ else if _ then Some ?b' else _) |- ?a1 = ?a2] =>
      apply H with (b:=b')
    end;
      repeat eq_auto.

  - match goal with
    | [H : one_to_one (fun x => if _ then _ else if _ then _ else ?m x),
           Ha : ?m ?a1 = Some ?b',
                Hb : ?m ?a2 = Some ?b' |- ?a1 = ?a2] =>
      apply H with (b1:=b')
    end;
      repeat eq_auto.
Qed.

Lemma inv_update :
  forall {A B}`{Eq A}`{Eq B} (f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    forall a b,
      f' b = None ->
      f a = None ->
      inv (update a b f) (update b a f').
Proof.
  intros;
    unfold inv.
  
  split;
    intros;
    repeat eq_explode;
    repeat map_rewrite;
    repeat eq_auto;
    repeat inv_auto;
    repeat option_crush;
    crush.

Qed.

Lemma one_to_one_update_none :
  forall {A B : Type}`{Eq A}`{Eq B} (f : partial_map A B) a b,
    one_to_one (update a b f) ->
    forall a', f a' = Some b -> a' = a.
Proof.
  intros A B HeqA HeqB f a b Hone2one a' Hmap.
  unfold one_to_one in *.
  eq_explode; auto.
  apply Hone2one with (b0:=b);
    repeat map_rewrite;
    repeat eq_auto.
Qed.

Ltac one_to_one_auto :=
  match goal with
  | [H : one_to_one ?f,
         Ha : ?f ?a1 = Some ?b,
              Hb : ?f ?a2 = Some ?b |- _] =>
    let Htmp := fresh in
    assert (Htmp : a1 = a2);
    [apply (H a1 a2 b Ha Hb)|subst a1]
  | [Ha : finite_normal_form ?f,
          Hb : one_to_one (update ?a ?b ?f),
               Hc : ?f ?a = None |- _] =>
    notHyp (one_to_one f);
    assert (one_to_one f);
    [apply one_to_one_fnf_update in Hb; auto|]
  end.

Lemma one_to_one_exists_inv_fnf :
  forall (A B : Type)`{Eq A}`{Eq B} (f : partial_map A B),
    finite_normal_form f ->
    one_to_one f ->
    exists f', inv f f'.
Proof.
  intros A B HeqA Heqb f Hfin;
    induction Hfin;
    intros.

  - exists empty; auto.

  - one_to_one_auto.
    auto_specialize.
    destruct_exists.
    eexists.
    apply inv_update; eauto.
    assert (forall a', m a' = Some b -> a' = a);
      [apply one_to_one_update_none; auto|].
    apply not_some_implies_none.
    intros a' Hcontra.
    repeat inv_auto.
    match goal with
    | [_ : ?m ?a' = Some ?b,
           H : forall a'', ?m a'' = Some ?b -> a'' = ?a |- _] =>
      assert (a' = a);
        [apply H3; auto|subst]
    end.
    option_crush.
Qed.

Lemma one_to_one_exists_inv_fin :
  forall (A B : Type)`{Eq A}`{Eq B} (f : partial_map A B),
    finite f ->
    one_to_one f ->
    exists f', inv f f'.
Proof.
  intros; apply one_to_one_exists_inv_fnf; auto.
Qed.

Parameter one_to_one_exists_inv:
  forall (A B : Type)`{Eq A}`{Eq B} (f : partial_map A B),
    one_to_one f ->
    exists f', inv f f'.

Lemma inv_symmetry :
  forall {A B : Type}`{Eq A}`{Eq B}
    (f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    inv f' f.
Proof.
  intros;
    unfold inv in *;
    andDestruct;
    split;
    intros;
    auto.
Qed.

Lemma inverse_maps_into :
  forall {A B : Type}`{Eq A}`{Eq B}(f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    maps_into f f'.
Proof.
  intros.
  unfold inv in *;
    andDestruct.
  unfold maps_into;
    intros.
  match goal with
  | [Ha : forall a b, ?f a = Some b -> ?f' b = Some a,
       Hb : ?f ?a' = Some ?b' |- exists c, ?f' ?b' = Some c ] =>
    apply Ha in Hb;
      eexists;
      eauto
  end.
Qed.

Lemma inverse_maps_from :
  forall {A B : Type}`{Eq A}`{Eq B}(f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    maps_from f' f.
Proof.
  intros.
  unfold inv in *;
    andDestruct.
  unfold maps_from;
    intros.
  match goal with
  | [Ha : forall a b, ?f' b = Some a -> ?f a = Some b,
       Hb : ?f' ?b' = Some ?c' |- exists a, ?f a = Some ?b' ] =>
    apply Ha in Hb;
      eexists;
      eauto
  end.
Qed.

Hint Resolve inverse_maps_from inverse_maps_into.

Lemma inverse_compose_right :
  forall {A B C : Type}`{Eq A}`{Eq B}`{Eq C}(m : partial_map A B)(f : partial_map B C)(f' : partial_map C B),
    inv f f' ->
    maps_into m f ->
    m ∘ f ∘ f' = m.
Proof.
  intros.
  apply functional_extensionality;
    intros a; unfold id; simpl.
  destruct (partial_map_dec a m) as [|Hnone];
    [destruct_exists|crush];
    repeat maps_into_from_auto;
    repeat inv_auto;
    crush.
Qed.

Lemma inverse_compose_left :
  forall {A B C : Type}`{Eq A}`{Eq B}(m : partial_map A C)(f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    maps_from m f' ->
    f ∘ f' ∘ m = m.
Proof.
  intros.
  apply functional_extensionality;
    intros a; unfold id; simpl.
  destruct (partial_map_dec a f) as [|Hnone];
    [destruct_exists|rewrite Hnone].

  - repeat maps_into_from_auto;
      repeat inv_auto;
      crush.
  - symmetry; apply not_some_implies_none;
      intros b Hcontra.
    maps_into_from_auto.
    inv_auto.
    crush.
Qed.

Lemma compose_assoc :
  forall {A B C D : Type}`{Eq A}`{Eq B}`{Eq C}
    (f : partial_map A B)(g : partial_map B C)(h : partial_map C D),
    (f ∘ g) ∘ h = f ∘ (g ∘ h).
Proof.
  intros A B C D HeqA HeqB HeqC  f g h.
  apply functional_extensionality;
    intros a; simpl; auto.
  destruct (f a); auto.
Qed.

(*Lemma bind_inverse_right :
  forall {A B C : Type}`{Eq A}`{Eq B}`{Eq C}
    (f : partial_map B C)(f' : partial_map C B),
    inv f f' ->
    forall (m : partial_map A B),
      (forall a b, m a = Some b -> exists c, f b = Some c) ->
      (fun x => bind (bind (m x) f) f') = m.
Proof.
  intros.
  unfold bind; simpl.
  apply functional_extensionality;
    intros a.
  match goal with
  | [|- _ = ?m ?a] =>
    destruct (partial_map_dec a m) as [Hsome|Hnone];
      [destruct_exists|rewrite Hnone; auto]
  end.
  match goal with
  | [H : ?m ?a = Some ?b,
         Hmap : forall a' b', ?m a' = Some b' -> _ |- _ = ?m ?a] =>
    rewrite H; apply Hmap in H;
      destruct_exists
  end.
  unfold inv in *;
    andDestruct.
  crush.
Qed.

Lemma bind_inverse_left :
  forall {A B C : Type}`{Eq A}`{Eq B}
    (f : partial_map A B)(f' : partial_map B A),
    inv f f' ->
    forall (m : partial_map B C),
      (forall a b, f a = Some b -> exists c, m b = Some c) ->
      (forall b c, m b = Some c -> exists a, f a = Some b) ->
      (fun x  => bind (f' x) (fun y => bind (f y) m)) = m.
Proof.
  intros.
  unfold bind; simpl.
  apply functional_extensionality;
    intros b.
  match goal with
  | [_ : inv ?f ?f' |- context[?f' ?b]] =>
    destruct (partial_map_dec b f') as [Hsome|Hnone];
      [destruct_exists|rewrite Hnone; auto]
  end.

  - match goal with
    | [H : ?f' ?b = Some ?a |- context[?f' ?b]] =>
      rewrite H
    end.
    unfold inv in *;
      andDestruct.
    match goal with
    | [Hmap : ?f' ?b = Some ?a,
              Ha : forall a' b', ?f' b' = Some a' -> _ |- _ ] =>
      apply Ha in Hmap
    end.
    crush.

  - match goal with
    | [|- None = ?m ?b] =>
      destruct (partial_map_dec b m) as [Hsome'|Hnone'];
        auto
    end.
    destruct_exists.
    match goal with
    | [H : ?m ?b = Some _,
           Ha : forall b' c', ?m b' = Some c' -> _ |- _ = ?m ?b] =>
      apply Ha in H; destruct_exists
    end.
    unfold inv in *;
      andDestruct.
    match goal with
    | [H : ?f ?a = Some ?b,
           Ha : ?f' ?b = None,
           Hb : forall a' b', ?f a' = Some b' -> ?f' b' = Some a' |- _] =>
      apply Hb in H
    end.
    crush.
Qed.*)

Lemma compose_one_to_one_eq :
  forall {A B C: Type} `{Eq A}`{Eq B} (f1 f2 : partial_map A B) (g : partial_map B C),
    one_to_one g ->
    maps_into f1 g ->
    maps_into f2 g ->
    f1 ∘ g = f2 ∘ g ->
    f1 = f2.
Proof.
  intros.
  apply functional_extensionality;
    intros a.

  match goal with
  | [H : ?m1 ∘ ?f = ?m2 ∘ ?f |- ?m1 ?y = ?m2 ?y ] => apply equal_f with (x:=y) in H
  end.

  match goal with
  | [|- ?n = ?m] =>
    destruct (eq_dec n m);
    simpl in *;
    auto
  end.
  match goal with
  | [H : one_to_one ?g,
     Hneq : ?f1 ?a <> ?f2 ?a |- ?f1 ?a = ?f2 ?a] =>
    apply (one_to_one_bind_f_nequal g H (f1 a) (f2 a)) in Hneq;
      [destruct (f1 a);
       destruct (f2 a);
       simpl in *;
       eauto|]
  end.
  
  destruct (partial_map_dec a f1) as [Hsome1|Hnone1];
    [destruct_exists|rewrite Hnone1 in *].
  - match goal with
    | [H : ?f ?a = Some ?x |-_] => rewrite H in *; simpl in *
    end.
    destruct (partial_map_dec a f2) as [Hsome2|Hnone2];
      [destruct_exists|eauto].
    + match goal with
      | [H : ?f ?a = Some ?x |-_] => rewrite H in *; simpl in *
      end.
      repeat maps_into_from_auto.
      match goal with
      | [H : ?g _ = ?g _ |- _] => rewrite H in *
      end.
      match goal with
      | [H : ?g _ = Some _ |- _] => rewrite H in *
      end.
      one_to_one_auto.
      crush.

  - assert (Hneq : f2 a <> None);
      [crush
      |apply not_none_implies_some in Hneq;
       destruct_exists].
    repeat maps_into_from_auto.
    crush; eexists; eauto.
Qed.

Lemma compose_one_to_one :
  forall {A B C : Type}`{Eq A}`{Eq B} (f : partial_map A B)(g : partial_map B C),
    one_to_one f ->
    one_to_one g ->
    one_to_one (f ∘ g).
Proof.
  intros; unfold one_to_one; intros.
  unfold bind in *; simpl in *.
  destruct (partial_map_dec a1 f) as [Hsome1|Hnone1];
    destruct (partial_map_dec a2 f) as [Hsome2|Hnone2];    
    try rewrite Hnone1 in *;
    try rewrite Hnone2 in *;
    repeat destruct_exists;
    try match goal with
        | [H : None = Some _ |- _] => inversion H
        end.

  - repeat match goal with
           | [H : ?f ?a = Some _ |- _] => rewrite H in *
           end.
    repeat one_to_one_auto;
      auto.
Qed.

Lemma extend_some_1 :
  forall {A B : Type}`{Eq A}(f g : partial_map A B) a b,
    f a = Some b ->
    (f ∪ g) a = Some b.
Proof.
  intros; unfold extend; crush.
Qed.

Lemma extend_application :
  forall {A B : Type}`{Eq A}(f g : partial_map A B) a b,
    (f ∪ g) a = Some b ->
    f a = Some b \/ (f a = None /\ g a = Some b).
Proof.
  intros.
  unfold extend in *.
  destruct (f a); auto.
Qed.

(* TODO : need to figure this out *)
(* specialize universal quantification for all possible terms *)
Ltac broken :=
  match goal with
  | [H : forall (_ : ?A), _,
       a : ?A |- _] =>
    notHyp (H a);
    let H' := fresh in
    assert (H' := H);
    specialize (H a)
    end.

Lemma disjoint_dom_symmetry :
  forall {A B C : Type}`{Eq A}(f : partial_map A B)(g : partial_map A C),
    disjoint_dom f g ->
    disjoint_dom g f.
Proof.
  intros;
    unfold disjoint_dom in *;
    intros.
  apply not_some_implies_none;
    intros b' Hcontra.
  specialize (H0 a b');
    auto_specialize;
    crush.
Qed.

Hint Resolve disjoint_dom_symmetry.

Ltac disjoint_dom_sym_auto :=
  match goal with
  | [H : disjoint_dom ?f ?g |- _] =>
    notHyp (disjoint_dom g f);
    assert (disjoint_dom g f);
    [apply disjoint_dom_symmetry; auto|]
  end.

Lemma extend_some_2 :
  forall {A B : Type}`{Eq A}(f g : partial_map A B) a b,
    g a = Some b ->
    disjoint_dom f g ->
    (f ∪ g) a = Some b.
Proof.
  intros; unfold extend.
  disjoint_dom_sym_auto;
    unfold disjoint_dom in *.
  match goal with
  | [Ha : forall a b, ?g a = Some b -> ?f a = None,
       Hb : ?g ?a = Some ?b |- context[?f ?a]] =>
    rewrite (Ha a b);
      auto
  end.

Qed.

Lemma extend_into :
  forall {A B C : Type}`{Eq A}`{Eq B}(f g : partial_map A B)(h : partial_map B C),
    maps_into (f ∪ g) h ->
    maps_into f h.
Proof.
  intros.
  unfold maps_into in *; intros; auto.
  match goal with
  | [H : ?f ?a = Some ?b |- _] => eapply extend_some_1 in H; eauto
  end.
Qed.

Hint Resolve extend_into.

Lemma extend_into_disjoint :
  forall {A B C : Type}`{Eq A}`{Eq B}(f g : partial_map A B)(h : partial_map B C),
    maps_into (f ∪ g) h ->
    disjoint_dom f g ->
    maps_into f h /\ maps_into g h.
Proof.
  intros; split; eauto.
  disjoint_dom_sym_auto.
  unfold maps_into in *; intros.
  unfold disjoint_dom in *.
  match goal with
  | [Ha : forall a' b', _ -> exists c', ?h b' = Some c',
       Hb : ?g ?a = Some ?b |- exists c, ?h ?b = Some c] => eapply (Ha a)
  end.
  apply extend_some_2; auto.
Qed.
  

Lemma into_extend :
  forall {A B C : Type}`{Eq A}`{Eq B}(f g : partial_map A B)(h : partial_map B C),
    maps_into f h ->
    maps_into g h ->
    maps_into (f ∪ g) h.
Proof.
  intros.
  unfold maps_into in *;
    intros;
    eauto.
  destruct (extend_application f g a b); auto;
    [|andDestruct]; eauto.
Qed.

Ltac maps_into_ext_decompose :=
  match goal with
  | [Ha : maps_into (?f ∪ ?g) ?h,
          Hb : disjoint_dom ?f ?g |- _] =>
    assert (maps_into f h /\ maps_into g h);
    [eapply extend_into_disjoint; eauto|]
  | [H : maps_into (?f ∪ ?g) ?h |- _] =>
    assert (maps_into f h);
    [eapply extend_into; eauto|]
  end.

Lemma extend_compose_distr :
  forall {A B C : Type}`{Eq A}`{Eq B}(f g : partial_map A B)(h : partial_map B C),
    maps_into (f ∪ g) h ->
    (f ∪ g) ∘ h = (f ∘ h) ∪ (g ∘ h).
Proof.
  intros; maps_into_ext_decompose.
  apply functional_extensionality;
    intros a.
  simpl.
  unfold extend.
  destruct (partial_map_dec a f) as [|Hnone];
    [destruct_exists|rewrite Hnone; auto].
  maps_into_from_auto.
  crush.
Qed.

Lemma empty_maps_into :
  forall {A B C : Type}{HeqA : Eq A}{HeqB : Eq B} (f : partial_map B C),
    maps_into (@empty A B HeqA) f.
Proof.
  intros;
    unfold maps_into;
    intros;
    repeat map_rewrite;
    crush.
Qed.

Hint Resolve empty_maps_into.

Lemma empty_maps_from :
  forall {A B C : Type}`{Eq A}{HeqB : Eq B} (f : partial_map A B),
    maps_from (@empty B C HeqB) f.
Proof.
  intros;
    unfold maps_from;
    intros;
    repeat map_rewrite;
    crush.
Qed.

Hint Resolve empty_maps_from.

Lemma empty_onto_empty :
  forall {A B C : Type}{HeqA : Eq A}{HeqB : Eq B},
    onto (@empty A B HeqA) (@empty B C HeqB).
Proof.
  intros.
  split;
    auto.
Qed.

Hint Resolve empty_onto_empty.

(* Disjointedness *)

Lemma empty_disjoint_1 :
  forall {A B C : Type}{HeqA : Eq A}(f : partial_map A B),
    disjoint_dom f (@empty A C HeqA).
Proof.
  intros.
  unfold disjoint_dom; intros; auto.
Qed.

Hint Resolve empty_disjoint_1.

Lemma empty_disjoint_2 :
  forall {A B C : Type}{HeqA : Eq A}(f : partial_map A B),
    disjoint_dom (@empty A C HeqA) f.
Proof.
  intros.  eapply disjoint_dom_symmetry; eauto.
Qed.

Hint Resolve empty_disjoint_2.
      
Lemma disjointedness_for_finite_variable_maps :
  forall {A B : Type}(f : partial_map var A),
    finite_normal_form f ->
    forall (g : partial_map var B),
      finite_normal_form g ->
      forall s, exists (h : partial_map var var),
          disjoint_dom f h /\
          disjoint_dom g h /\
          onto h g /\
          one_to_one h /\
          (forall x y, h x = Some y -> ~ in_stmt x s).
Proof.
  intros A B f Hfin1;
    induction Hfin1;
    intros g Hfin2;
    induction Hfin2;
    intros s.

  - exists empty;
      repeat split;
      auto;
      intros;
      repeat map_rewrite;
      crush.

  - induction s.
    
Admitted.

Lemma disjoint_composition :
  forall {A B C : Type}`{Eq A}`{Eq C}(f : partial_map A B)(g : partial_map A C),
    disjoint_dom f g ->
    forall {D : Type} (h : partial_map C D),
      disjoint_dom f (g ∘ h).
Proof.
  intros.
  unfold disjoint_dom in *; intros.
  unfold bind; crush.
  match goal with
  | [Ha : forall a' b', ?f a' = Some b' -> _,
       Hb : ?f ?a = Some ?b |- _] => specialize (Ha a b Hb)
  end.
  crush.
Qed.

Hint Resolve disjoint_composition.