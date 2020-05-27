Require Import common.
Require Import loo_def.
Require Import function_operations.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(** #<h1># Basic Arithmetic Assertions: #</h1># *)

Ltac simpl_crush :=
  match goal with
  | [ H : (_, _) = (_, _) |- _] =>
    inversion H; subst;
    clear H
  | [ H : _::_ = _::_ |- _] =>
    inversion H; subst;
    clear H
  | [ H : Some _ = Some _ |- _] =>
    inversion H; subst;
    clear H
  | [ H : v_addr _ = v_addr _ |- _] =>
    inversion H; subst;
    clear H
  | [ H : r_exp _ = r_exp _ |- _] =>
    inversion H; subst;
    clear H
  | [ H : _ ◌ _ = _ ◌ _ |- _] =>
    inversion H; subst;
    clear H
  | [ Ha : contn ?ϕ = _, Hb : contn ?ϕ = _ |- _] =>
    rewrite Ha in Hb;
    inversion Hb;
    subst;
    clear Hb
  | [Ha : ?m ?a = _, Hb : ?m ?a = _ |- _] =>
    rewrite Ha in Hb;
    inversion Hb;
    subst;
    clear Hb
  end.

Lemma prop_not_and_distr :
  forall A B, ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros.
  destruct (excluded_middle A);
    destruct (excluded_middle B);
    crush.
Qed.

Lemma prop_implies_not :
  forall (A B : Prop), (A -> ~B) -> (B -> ~A).
Proof.
  crush.
Qed.

Lemma forall_exists_neg :
  forall {A : Type} P, (forall (x : A), ~ P) ->
                  ~ (exists (a : A), P).
Proof.
  intros; crush.
Qed.

Lemma exists_neg_forall :
  forall {A : Type} (P : A -> Prop),
    ~ (exists (a : A), P a) ->
    (forall (a : A), ~ P a).
Proof.
  intros; intros Hcontra.
  contradiction H.
  exists a; auto.
Qed.

Lemma linking_unique :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             forall M', M1 ⋄ M2 ≜ M' ->
                   M' = M.
Proof.
  intros M1 M2 M Hlink1 M' Hlink2;
    inversion Hlink1; inversion Hlink2;
      subst;
      auto.
Qed.

Ltac link_unique_auto :=
  match goal with
  | [H1 : ?M1 ⋄ ?M2 ≜ ?M, H2 : ?M1 ⋄ ?M2 ≜ ?M' |-_] =>
    assert (M' = M);
    [eapply linking_unique;
     eauto|subst M']
  end.

Lemma M_wf_ObjectDefn :
  forall M, M_wf M ->
       M Object = Some ObjectDefn.
Proof.
  intros M Hwf; inversion Hwf; crush.
Qed.

Ltac obj_defn_rewrite :=
  match goal with
  | [H : M_wf ?M |- context[?M Object]] => rewrite (M_wf_ObjectDefn M H)
  end.

Lemma linked_wf :
  forall M1 M2 M, M1 ⋄ M2 ≜ M ->
             M_wf M1 ->
             M_wf M2 ->
             M_wf M.
Proof.
  intros M1 M2 M Hlink Hwf1 Hwf2;
    inversion Hlink; subst;
      inversion Hwf1; subst;
        inversion Hwf2; subst.
  apply module_wf;
    auto; intros.
  unfold extend;
    destruct (M1 Object); auto.
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush.
  unfold extend in H7.
  remember (M1 C) as x.
  destruct x; crush; eauto.
Qed.

Ltac linking_wf :=
  match goal with
  | [H1 : M_wf ?M1, H2 : M_wf ?M2, Hlink : ?M1 ⋄ ?M2 ≜ ?M |- M_wf ?M] => eapply linked_wf; eauto
  end.

Lemma le_le_addr :
  forall α1 α2, le_α α1 α2 ->
           le_α α2 α1 ->
           α1 = α2.
Proof.
  intros α1 α2 Hle1 Hle2.
  inversion Hle1;
    inversion Hle2;
    crush.
Qed.

Hint Resolve le_le_addr : loo_db.
Hint Rewrite le_le_addr : loo_db.

Lemma heap_max_unique :
  forall (χ : heap) α, max_χ χ α ->
         forall α', max_χ χ α' ->
               α' = α.
Proof.
  intros χ α Hmax1 α' Hmax2.
  inversion Hmax1; inversion Hmax2;
    subst.
  crush.
  eauto with loo_db.
Qed.

Hint Resolve heap_max_unique : loo_db.
Hint Rewrite heap_max_unique : loo_db.

Lemma fresh_heap_unique :
  forall χ α1 α2, fresh_χ χ α1 ->
             fresh_χ χ α2 ->
             α1 = α2.
Proof.
  intros χ α1 α2 Hfrsh1 Hfrsh2;
    inversion Hfrsh1;
    inversion Hfrsh2;
    subst.
  match goal with
  | [H1 : max_χ ?χ ?α1,
          H2 : max_χ ?χ ?α2 |- _] => apply heap_max_unique with (α:=α2) in H1; subst; auto
  end.
Qed.

Hint Resolve fresh_heap_unique : loo_db.
Hint Rewrite fresh_heap_unique : loo_db.

Lemma fresh_heap_none :
  forall χ α, fresh_χ χ α ->
         χ α = None.
Proof.
  intros χ α Hfrsh;
    inversion Hfrsh;
    subst.
  inversion H; subst.
  apply not_some_implies_none;
    intros;
    intro Hcontra.
  apply H1 in Hcontra.
  inversion Hcontra; subst; simpl in *.
  crush.
Qed.

Hint Resolve fresh_heap_none : loo_db.
Hint Rewrite fresh_heap_none : loo_db.

Lemma fresh_heap_some_contradict :
  forall χ α, fresh_χ χ α ->
         forall o, ~ χ α = Some o.
Proof.
  intros χ α Hfrsh; intros; intro Hcontra.
  apply fresh_heap_none in Hfrsh; crush.  
Qed.

Hint Resolve fresh_heap_some_contradict : loo_db.

Lemma fresh_heap_some_contradiction :
  forall χ α, fresh_χ χ α ->
         forall o, χ α = Some o ->
              forall P, P.
Proof.
  intros χ α Hfrsh o; intros.
  apply fresh_heap_some_contradict with (o:=o) in Hfrsh;
    crush.
Qed.

Lemma fresh_in_empty :
  forall {A : Type} x, @fresh_in_map A x empty.
Proof.
  unfold fresh_in_map;
    intros.
  pmap_simpl.
Qed.

Hint Resolve fresh_in_empty : loo_db.

Lemma fresh_in_map_not_in_dom :
  forall {A : Type} (m : partial_map var A) d,
    dom m d ->
    forall x, fresh_in_map x m <-> ~ In x d.
Proof.
  intros A m d Hdom x;
    split;
    intros.

  - eapply not_in_map_implies_not_in_dom; eauto.

  - eapply not_in_dom_implies_not_in_map; eauto.
Qed.

Inductive lt_map {A : Type} : nat -> partial_map var A -> Prop :=
| lt_empty : lt_map 0 empty
| lt_update1 : forall n b m n', lt_map n' m ->
                           n < n' ->
                           lt_map n' (update (bnd n) b m)
| lt_update2 : forall n b m n', lt_map n' m ->
                           n' <= n ->
                           lt_map (S n) (update (bnd n) b m).

Hint Constructors lt_map : loo_db.

Lemma exists_limit_for_finite_map :
  forall {A : Type} (m : partial_map var A),
    finite m ->
    exists n, lt_map n m.
Proof.
  intros A m Hfinite;
    induction Hfinite;
    [exists 0; auto with loo_db|destruct IHHfinite as [n]].
  
  destruct a as [n'].
  destruct (le_lt_dec n n') as [Hle|Hlt];
    [exists (S n'); eapply lt_update2|exists n; apply lt_update1]; eauto.
Qed.

Lemma lt_map_implies_var_lt :
  forall {A : Type} n (m : partial_map var A),
    lt_map n m ->
    forall n' b, m (bnd n') = Some b ->
            n' < n.
Proof.
  intros A n m Hlt;
    induction Hlt;
    intros;
    pmap_simpl.
  destruct (eq_dec n'0 n);
    [subst|];
    pmap_simpl.
  unfold update, t_update in H0;
    rewrite neq_eqb in H0; [eauto|crush].
  destruct (eq_dec n'0 n);
    [subst|];
    pmap_simpl.
  unfold update, t_update in H0;
    rewrite neq_eqb in H0; [eauto|crush].
  apply IHHlt in H0; crush.
Qed.

Lemma lt_fresh_in_map :
  forall {A : Type} n (m : partial_map var A),
    lt_map n m -> forall n', n <= n' -> fresh_in_map (bnd n') m.
Proof.
  intros A n m Hlt;
    induction Hlt;
    auto with loo_db;
    unfold fresh_in_map in *;    
    intros.

  - repeat map_rewrite;
      simpl.
    match goal with
    | [Ha : ?n2 < ?n3,
            Hb : ?n3 <= ?n1 |-context[?n1 =? ?n2]] =>
      let Hneq := fresh in
      assert (Hneq : n1 <> n2);
        [crush
        |apply Nat.eqb_neq in Hneq;
         rewrite Hneq; eauto]
    end.

  - repeat map_rewrite;
      simpl.
    match goal with
    | [Ha : S ?n2 <= ?n1 |-context[?n1 =? ?n2]] =>
      let Hneq := fresh in
      assert (Hneq : n1 <> n2);
        [crush
        |apply Nat.eqb_neq in Hneq;
         rewrite Hneq]
    end.
    crush.
Qed.

Lemma fresh_var_finite :
  forall {A : Type} (m : partial_map var A),
    finite m ->
    exists x, fresh_in_map x m.
Proof.
  intros;
    destruct (exists_limit_for_finite_map m) as [n];
    auto;
    exists (bnd n);
    eapply lt_fresh_in_map;
    eauto.
Qed.

Lemma fresh_var_finite2 :
  forall {A : Type} (m1 : partial_map var A),
    finite m1 ->
    forall (m2 : partial_map var A), finite m2 ->
                                exists x, fresh_in_map x m1 /\
                                     fresh_in_map x m2.
Proof.
  intros.
  destruct (exists_limit_for_finite_map m1) as [n1];
    destruct (exists_limit_for_finite_map m2) as [n2];
    auto.
  destruct (le_lt_dec n1 n2) as [Hle|Hlt];
    [exists (bnd n2)|exists (bnd n1)];
    split;
    eapply lt_fresh_in_map;
    eauto;
    crush.
Qed.

Inductive lt_var : nat -> var -> Prop :=
| lt_bind : forall n n', n' < n ->
                    lt_var n (bnd n').

Hint Constructors lt_var : loo_db.

Lemma exists_limit_var :
  forall x, exists n, lt_var n x.
Proof.
  intros x;
    destruct x as [n'];
    exists (S n');
    crush.
Qed.

Lemma exists_limit_for_list :
  forall l, exists n, forall x, In x l ->
                 lt_var n x.
Proof.
  intros l;
    induction l as [|x l'];
    [exists 0; crush|destruct x as [n']].
  destruct IHl' as [n Hltx].
  destruct (le_lt_dec n n') as [Hle|Hlt];
    [exists (S n')|exists n];
    intros.
  inversion H; subst; crush.
  apply Hltx in H0.
  inversion H0; subst; crush.
  crush.
Qed.

Lemma fresh_var_finite3 :
  forall {A : Type} (m1 : partial_map var A),
    finite m1 ->
    forall (m2 : partial_map var A), finite m2 ->
                                forall d, exists x, fresh_in_map x m1 /\
                                          fresh_in_map x m2 /\
                                          ~ In x d.
Proof.
  intros.
  destruct (exists_limit_for_finite_map m1) as [n1];
    destruct (exists_limit_for_finite_map m2) as [n2];
    destruct (exists_limit_for_list d) as [n3];
    auto.
  destruct (le_lt_dec n1 n2) as [Hle1|Hlt1].
  destruct (le_lt_dec n1 n3) as [Hle2|Hlt2].
  
  destruct (le_lt_dec n3 n2) as [Hle3|Hlt3];

    try solve [exists (bnd n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n3 n2) as [Hle3|Hlt3];

    try solve [exists (bnd n2); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
  
  destruct (le_lt_dec n1 n3) as [Hle2|Hlt2];

    try solve [exists (bnd n1); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush];

    try solve [exists (bnd n3); split; [|split];
                 try solve [eapply lt_fresh_in_map; eauto; crush];
                 intro Hcontra;
                 apply H3 in Hcontra;
                 inversion Hcontra; crush].
Qed.

Lemma dom_finite :
  forall {A B : Type} `{Eq A} D (ps : partial_map A B),
    dom ps D ->
    finite ps.
Proof.
  intros A B HeqA D;
    induction D as [|a D'];
    intros ps Hdom;
    [unfold dom in *;
     andDestruct
    |].

  assert (ps = empty);
    [|subst; auto with map_db].
  apply functional_extensionality;
    intros a;
    repeat map_rewrite.
  apply not_some_implies_none;
    intros b.
  intro Hcontra.
  match goal with
  | [Hmap : ?m ?a = Some ?b,
            H : forall a' b', ?m a' = Some b' -> In a' nil  |- _] => apply H in Hmap; crush
  end.

  unfold dom in Hdom;
    andDestruct.
  destruct (Ha0 a (in_eq a D')) as [b Hmap].

  assert (Hps : ps = update a b (t_update ps a None));
    [apply functional_extensionality;
     intros a';
     repeat map_rewrite|subst].
  destruct (eq_dec a' a) as [|Hneq];
    subst;
    eq_auto.
  rewrite Hps.
  apply fin_update.
  apply IHD'; unfold dom;
    repeat split; intros;
      try solve [match goal with
                 | [Huniq : unique (_::?D) |- unique ?D] => inversion Huniq; auto with map_db
                 end];
      repeat map_rewrite.
  destruct (eq_dec a0 a) as [|Hneq];
    subst;
    eq_auto;
    [crush|].
  match goal with
  | [H : forall a' b', ?m a' = Some b' -> In a' (?a::?D),
       Hmap : ?m ?a0 = Some ?b,
       Hneq : ?a0 <> ?a |- _] => apply H in Hmap; inversion Hmap; crush
  end.

  match goal with
  | [Hin : In ?a0 ?D,
           H : forall a', In a' (?a::?D) ->
                     exists b', ?m a' = Some b',
       Huniq : unique (?a::?D)
                           |- _] =>
    let b := fresh "b" in
    destruct (H a0 (in_cons a a0 D Hin)) as [b];
      destruct (eq_dec a a0);
      subst;
      eq_auto;
      [inversion Huniq; crush|crush]
  end.
Qed.

Hint Resolve dom_finite : loo_db.

Lemma has_self_update_ϕ :
  forall χ ϕ, has_self_ϕ χ ϕ ->
       forall x v, x <> this ->
              has_self_ϕ χ (update_ϕ_map ϕ x v).
Proof.
  intros χ ϕ Hself;
    inversion Hself;
    intros;
    subst.
  destruct H as [α Ha];
    destruct Ha as [o Ha];
    andDestruct.
  apply self_frm.
  exists α, o; simpl;
    unfold update, t_update;
    rewrite neq_eqb;
    auto.
Qed.

Lemma has_self_update_σ :
  forall σ, has_self_σ σ ->
       forall x v, x <> this ->
              has_self_σ (update_σ_map σ x v).
Proof.
  intros σ Hself;
    inversion Hself;
    intros;
    subst.
  apply self_config;
    intros;
    simpl in *.
  unfold update_ψ_map in H0;
    destruct ψ as [|ϕ' ψ'];
    [crush|inversion H0; subst].
  apply has_self_update_ϕ;
    auto.
  apply H, in_eq.

  apply H, in_cons; auto.
Qed.

Lemma has_self_update_ϕ_contn :
  forall χ ϕ, has_self_ϕ χ ϕ ->
       forall c, has_self_ϕ χ (update_ϕ_contn ϕ c).
Proof.
  intros.
  inversion H;
    subst.
  destruct H0 as [α Ha];
    destruct Ha as [o];
    andDestruct.
  apply self_frm;
  exists α, o; simpl; auto.
Qed.

Lemma has_self_update_σ_contn :
  forall σ, has_self_σ σ ->
       forall c, has_self_σ (update_σ_contn σ c).
Proof.
  intros σ Hself;
    inversion Hself;
    intros;
    subst.
  apply self_config;
    intros;
    simpl in *.
  
  unfold update_ψ_contn in H0;
    destruct ψ as [|ϕ' ψ'];
    [crush|inversion H0; subst].
  apply has_self_update_ϕ_contn.
  apply H, in_eq.
  apply H, in_cons;
    auto.
Qed.

Lemma config_head_wf :
  forall σ, σ_wf σ ->
       forall χ ϕ ψ, σ = (χ, ϕ::ψ) ->
                σ_wf (χ, ϕ::nil).
Proof.
  intros;
    subst.
  inversion H;
    subst;
    apply config_wf;
    finite_auto; not_stuck_auto; waiting_auto;
      try solve [crush].
  apply self_config;
    intros ϕ' Hin;
    inversion Hin;
    subst;
    inversion H0;
    subst.
  apply H5, in_eq.
  inversion H4.
  
  exists ϕ, nil; split; auto; crush.
  exists ϕ, nil; split; auto; crush.
Qed.

Hint Resolve config_head_wf : loo_db.

Lemma config_wf_decompose :
  forall σ, σ_wf σ ->
       exists χ ϕ ψ, σ = (χ, ϕ::ψ).
Proof.
  intros σ Hwf;
    inversion Hwf;
    subst;
    not_stuck_auto.
  destruct H1 as [ϕ Hns];
    destruct Hns as [ψ];
    andDestruct.
  exists (fst σ), ϕ, ψ; destruct σ; crush.
Qed.

Lemma limited_config_wf :
  forall χ ϕ ψ, σ_wf (χ, ϕ::ψ) ->
           σ_wf (χ, ϕ::nil).
Proof.
  intros.
  inversion H;
    subst.
  apply config_wf.
  
  apply self_config;
    intros.
  inversion H0;
    subst.
  inversion H4;
    subst;
    [|crush].
  apply H6, in_eq.

  finite_auto;
    simpl;
    intros.
  inversion H4;
    subst;
    [|crush].
  apply H1;
    simpl;
    auto.

  not_stuck_auto.
  destruct H2 as [ϕ' Ha];
    destruct Ha as [ψ'];
    andDestruct;
    simpl in *.
  inversion Ha;
    subst.
  exists ϕ', nil;
    split;
    auto.
  
  waiting_auto.
  destruct H3 as [ϕ' Ha];
    destruct Ha as [ψ'];
    andDestruct;
    simpl in *;
    inversion Ha;
    subst.
  repeat eexists; eauto; intros.
  crush.

Qed.

Hint Resolve limited_config_wf : loo_db.

Lemma waiting_update_σ_map :
  forall σ, waiting_σ σ ->
       forall x v, waiting_σ (update_σ_map σ x v).
Proof.
  intros.
  waiting_auto;
    simpl in *.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ];
    andDestruct.
  rewrite Ha.
  exists (update_ϕ_map ϕ x v), ψ;
    split;
    unfold update_ψ_map; simpl;
    auto.
Qed.

Hint Resolve waiting_update_σ_map : loo_db.

Lemma not_stuck_update_σ_map :
  forall σ, not_stuck_σ σ ->
       forall x v, not_stuck_σ (update_σ_map σ x v).
Proof.
  intros.
  not_stuck_auto;
    simpl in *.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ];
    andDestruct.
  rewrite Ha.
  exists (update_ϕ_map ϕ x v), ψ;
    split;
    unfold update_ψ_map; simpl;
    auto.
Qed.

Hint Resolve not_stuck_update_σ_map : loo_db.

Lemma finite_update_ϕ_map :
  forall ϕ, finite_ϕ ϕ ->
       forall x v, finite_ϕ (update_ϕ_map ϕ x v).
Proof.
  intros.
  finite_auto.

  apply fin_update;
    auto.
  
Qed.

Hint Resolve finite_update_ϕ_map : loo_db.

Lemma finite_update_σ_map :
  forall σ, finite_σ σ ->
       forall x v, finite_σ (update_σ_map σ x v).
Proof.
  intros.
  destruct σ as [χ ψ].
  unfold finite_σ, finite_ψ.
  simpl.
  unfold update_ψ_map.
  destruct ψ as [|ϕ ψ'];
    intros;
    [crush|].
  inversion H0;
    subst.
  apply finite_update_ϕ_map.
  finite_auto.
  apply H;
    simpl;
    auto.

  finite_auto.
  apply H;
    simpl;
    auto.
Qed.

Hint Resolve finite_update_σ_map : loo_db.

Lemma unique_interpretation_x :
  forall x σ v1, ⌊ x ⌋ σ ≜ v1 ->
            forall v2, ⌊ x ⌋ σ ≜ v2 ->
                  v2 = v1.
Proof.
  intros x σ v1 Hint1 v2 Hint2;
    inversion Hint1;
    inversion Hint2;
    subst.
  crush.
Qed.

Lemma unique_interpretation_Σ :
  forall Σ σ αs1, ⌊ Σ ⌋ σ ≜′ αs1 ->
            forall αs2, ⌊ Σ ⌋ σ ≜′ αs2 ->
                   αs2 = αs1.
Proof.
  intros x σ α1 Hint1;
    induction Hint1;
    intros αs2 Hint2;
    inversion Hint2;
    subst;
    auto.
  eapply (unique_interpretation_x x σ α) in H2;
    subst;
    eauto.
  rewrite (IHHint1 αs0); auto.
Qed.

Lemma mapp_x_append :
  forall (x : var)(v : value)(χ : heap)(ψ1 ψ2 : stack),
    ⟦ x ↦ v ⟧ ∈ (χ, ψ1) ->
    ⟦ x ↦ v ⟧ ∈ (χ, ψ1 ++ ψ2).
Proof.
  intros x v χ ψ1;
    induction ψ1;
    intros;
    repeat map_rewrite;
    crush.
Qed.

Lemma interpretation_x_append :
  forall x χ ψ v ψ', ⌊ x ⌋ (χ, ψ) ≜ v ->
                ⌊ x ⌋ (χ, ψ ++ ψ') ≜ v.
Proof.
  intros x χ ψ v ψ';
    intros Hint;
    inversion Hint;
    subst;
    simpl in *;
    subst;
    simpl in *.
  apply int_x, mapp_x_append; auto.
Qed.

Lemma interpretation_x_cons :
  forall x χ ϕ ψ v, ⌊ x ⌋ (χ, ϕ::ψ) ≜ v <->
               ⌊ x ⌋ (χ, ϕ::nil) ≜ v.
Proof.
  intros x χ ϕ ψ v; split.

  - intros Hint;
    inversion Hint;
    subst;
    simpl in *.
    apply int_x.
    crush.

  - intros Hint;
    inversion Hint;
    subst;
    simpl in *.
    apply int_x;
      crush.
Qed.

Ltac interpretation_rewrite :=
  repeat match goal with
         | [H1 : ⌊ ?x ⌋ ?σ ≜ ?v1, H2 : ⌊ ?x ⌋ ?σ ≜ ?v2 |- _] =>
           eapply (unique_interpretation_x x σ v1 H1) in H2;
           eauto;
           subst
         | [H1 : ⌊ ?Σ ⌋ ?σ ≜′ ?αs1, H2 : ⌊ ?Σ ⌋ ?σ ≜′ ?αs2 |- _] =>
           eapply (unique_interpretation_Σ Σ σ αs1 H1) in H2;
           eauto;
           subst
         end.

Lemma wf_σ_explode :
  forall σ, σ_wf σ ->
       exists χ ψ ϕ, σ = (χ, ϕ::ψ) /\
                finite (vMap ϕ) /\
                (forall ϕ', In ϕ' ψ ->
                       finite (vMap ϕ')) /\
                not_stuck (contn ϕ) /\
                (forall ϕ', In ϕ' ψ ->
                       waiting (contn ϕ')).
Proof.
  intros σ Hwf;
    inversion Hwf;
    subst;
    destruct σ as [χ ψ];
    finite_auto;
    not_stuck_auto;
    waiting_auto;
    crush;
    eexists;
    eexists;
    eexists;
    split;
    eauto;
    split;
    eauto.
Qed.

Ltac config_wf_destruct :=
  match goal with
  | [H : σ_wf ?σ |-_] =>
    apply wf_σ_explode in H;
    let χ := fresh "χ" in
    let ψ := fresh "ψ" in
    let ϕ := fresh "ϕ" in
    let Hwf := fresh "Hwf" in
    destruct H as [χ Hwf];
    destruct Hwf as [ψ Hwf];
    destruct Hwf as [ϕ Hwf];
    let Htmp := fresh "Htmp" in
    let Hfiniteϕ := fresh "Hfiniteϕ" in
    let Hfiniteψ := fresh "Hfiniteψ" in
    let Hnot_stuck := fresh "Hnot_stuck" in
    let Hwaiting := fresh "Hwaiting" in
    destruct Hwf as [Htmp Hwf];
    destruct Hwf as [Hfiniteϕ Hwf];
    destruct Hwf as [Hfiniteψ Hwf];
    destruct Hwf as [Hnot_stuck Hwaiting];
    subst σ
  end.

(** TODO: *)
Parameter function_neq_exists_neq_mapping  :
    forall {A B : Type} (f1 f2 : A -> B),
      f1 <> f2 ->
      exists a, f1 a <> f2 a.

(* update map *)

Lemma map_update_σ :
  forall σ z v, (exists ϕ ψ, snd σ = ϕ :: ψ) ->
           mapp (update_σ_map σ z v) z = Some v.
Proof.
  intros.
  unfold mapp, configMapStack, mapp, stackMap.
  destruct σ as [χ ψ];
    destruct ψ as [|ϕ ψ];
    simpl.
  destruct H as [ϕ Ha];
    destruct Ha as [ψ Ha];
    crush.
  unfold update, t_update;
    rewrite eqb_refl;
    auto.
Qed.


(* need to change definition of restriction *)
Parameter unique_restriction :
  forall σ Σ σ1, σ ↓ Σ ≜ σ1 ->
            forall σ2, σ ↓ Σ ≜ σ2 ->
                  σ2 = σ1.

Ltac restriction_rewrite :=
  repeat match goal with
         | [H1 : ?σ ↓ ?Σ ≜ ?σ1, H2 : ?σ ↓ ?Σ ≜ ?σ2 |- _] =>
           eapply (unique_restriction σ Σ σ1 H1) in H2;
           eauto;
           subst
         end.
