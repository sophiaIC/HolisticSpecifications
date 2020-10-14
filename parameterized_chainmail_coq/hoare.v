Require Import common.
Require Import defs.
Require Import partial_maps.
Require Import L_def.
Require Import exp.
Require Import exp_properties.
Require Import operational_semantics.
Require Import chainmail.
Require Import List.
Require Import String.
Open Scope string_scope.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Module Hoare(L : LanguageDef).

  Import L.
  Module L_Semantics := AbstractOperationalSemantics(L).
  Import L_Semantics.
  Module L_Chainmail := Chainmail(L).
  Import L_Chainmail.

  Open Scope reduce_scope.
  Open Scope chainmail_scope.

  Reserved Notation "M '∙' '{pre:' P '}' σ '{post:' Q '}'" (at level 40).
  Reserved Notation "M '∙' '{pre:' P '}' σ1 '⤳⋆' σ2 '{post:' Q '}'" (at level 40).
  Reserved Notation "M1 '⦂' M2 '⦿' '{pre:' P '}' σ '{post:' Q '}'" (at level 40).

  Inductive hoare_triple : mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
  | ht_r : forall M σ (P Q : config -> Prop), (forall σ', P σ ->
                                            M ∙ σ ⤳ σ' ->
                                            Q σ') ->
                                     M ∙ {pre: P} σ {post: Q}

  where "M '∙' '{pre:' P '}' σ '{post:' Q '}'"
          := (hoare_triple M P σ Q).

  Inductive hoare_triples : mdl -> (config -> Prop) -> config -> config -> (config -> Prop) -> Prop :=
  | ht_single : forall M P σ1 σ2 Q, M ∙ σ1 ⤳ σ2 ->
                               M ∙ {pre: P} σ1 {post: Q} ->
                               M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q}
  | ht_trans : forall M P σ1 σ σ2 P' Q, M ∙ σ1 ⤳ σ ->
                                   M ∙ {pre: P} σ1 {post: P'} ->
                                   M ∙ {pre: P'} σ ⤳⋆ σ2 {post: Q} ->
                                   M ∙ {pre: P} σ1 ⤳⋆ σ2 {post: Q}

  where "M '∙' '{pre:' P '}' σ1 '⤳⋆' σ2 '{post:' Q '}'" := (hoare_triples M P σ1 σ2 Q).

  Inductive hoare_triple_pr : mdl -> mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
  | ht_pr : forall M1 M2 σ (P Q : config -> Prop), (forall σ', P σ ->
                                                 M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                                                 Q σ') ->
                                          M1 ⦂ M2 ⦿ {pre: P } σ {post: Q }

  where "M1 '⦂' M2 '⦿' '{pre:' P '}' σ '{post:' Q '}'"
          := (hoare_triple_pr M1 M2 P σ Q).

  Hint Constructors hoare_triple hoare_triples hoare_triple_pr : hoare_db.

  Notation "M1 '⦂' M2 '◎' σ0 '…' '̱' '⊨' '{pre:' A1 '}' σ '{post:' A2 '}'" :=
    (M1 ⦂ M2 ⦿ {pre: fun σ => M1 ⦂ M2 ◎ σ0 … σ ⊨ A1} σ {post: fun σ' => M1 ⦂ M2 ◎ σ0 … σ' ⊨ A2})(at level 40).

  Inductive contn_is : continuation -> config -> Prop :=
  | is_stmt : forall self lcl c χ ψ,
      contn_is c (χ, frm self lcl c :: ψ).

  Hint Constructors contn_is : hoare_db.

  Definition is_skip : config -> Prop :=
    fun σ => exists b, contn_is (skip ;; b) σ.

  Definition is_call : config -> Prop :=
    fun σ => exists α m args b, contn_is (call α m args ;; b) σ.

  Definition is_rtrn : config -> Prop :=
    fun σ => (exists v b, contn_is (rtrn v ;; b) σ) \/ (exists v, contn_is (c_rtrn v) σ).

  Definition is_acc : config -> Prop :=
    fun σ => exists v b, contn_is (acc v ;; b) σ.

  Definition is_mut : config -> Prop :=
    fun σ => exists α f v b, contn_is (mut α f v ;; b) σ.

  Definition is_new : config -> Prop :=
    fun σ => exists C args b, contn_is (new C args ;; b) σ.

  Definition ctxUpdated : config ->  var -> value -> config -> Prop :=
    fun σ1 x v σ2 => exists ϕ1 ϕ2 ψ, snd σ1 = ϕ1 :: ψ /\
                             snd σ2 = ϕ2 :: ψ /\
                             vMap ϕ2 = update x v (vMap ϕ1).

  Definition heapUpdated : config -> addr -> obj -> config -> Prop :=
    fun σ1 α o σ2 => fst σ2 = (update α o (fst σ1)).

  Definition fieldHeapUpdated : config -> addr -> fld -> value -> config -> Prop :=
    fun σ1 α f v σ2 => exists o' v', ⟦ α ↦ o' ⟧ ∈ σ1 /\
                             flds o' f = Some v' /\
                             heapUpdated σ1 α (new (cname o') (update f v (flds o'))) σ2.

  Definition fieldUpdated : config -> var -> fld -> var -> config -> Prop :=
    fun σ1 x f y σ2 => exists α v, ⌊ x ⌋ σ1 ≜ (v_addr α) /\
                           ⌊ y ⌋ σ2 ≜ v /\
                           fieldHeapUpdated σ1 α f v σ2.

  Definition fieldUpdatedValue : config -> var -> fld -> value -> config -> Prop :=
    fun σ1 x f v σ2 => exists α, ⌊ x ⌋ σ1 ≜ (v_addr α) /\
                         fieldHeapUpdated σ1 α f v σ2.

  Definition fieldMapsTo : config -> var -> fld -> value -> Prop :=
    fun σ x f v => exists α o, ⌊ x ⌋ σ ≜ (v_addr α) /\
                       ⟦ α ↦ o ⟧ ∈ σ /\
                       flds o f = Some v.

  Definition new_object_created : config -> var -> cls -> partial_map fld var -> config -> Prop :=
    fun σ x C ps σ' =>  exists χ ϕ ψ α s, σ = (χ, ϕ :: ψ) /\
                                  contn ϕ = c_stmt (s_new x C ps ;; s) /\
                                  fresh_χ χ α /\
                                  heapUpdated σ α (new C (ps ∘ (vMap ϕ))) σ' /\
                                  ctxUpdated σ x (v_addr α) σ'.

  Definition heapUnchanged : config -> config -> Prop :=
    fun σ1 σ2 => fst σ1 = fst σ2.

  Definition ctxUnchanged : config -> config -> Prop :=
    fun σ1 σ2 => exists ϕ1 ϕ2 ψ, snd σ1 = ϕ1 :: ψ /\
                         snd σ2 = ϕ2 :: ψ /\
                         vMap ϕ1 = vMap ϕ2.

  Close Scope chainamil_scope.
  Close Scope reduce_scope.
End Hoare.
