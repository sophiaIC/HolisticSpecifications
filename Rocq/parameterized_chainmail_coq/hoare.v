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

  Reserved Notation "M '∙' '[pre:' P ']' σ '[post:' Q ']'" (at level 40).
  Reserved Notation "M1 '⦂' M2 '⦿' '[pre:' P ']' σ '[post:' Q ']'" (at level 40).

  Inductive necessary_triple : mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
  | nt_r : forall M σ (P Q : config -> Prop), (forall σ', Q σ' ->
                                            M ∙ σ ⤳ σ' ->
                                            P σ) ->
                                     M ∙ [pre: P] σ [post: Q]

  where "M '∙' '[pre:' P ']' σ '[post:' Q ']'"
          := (necessary_triple M P σ Q).

  Inductive necessary_triple_pr : mdl -> mdl -> (config -> Prop) -> config -> (config -> Prop) -> Prop :=
  | nt_pr : forall M1 M2 σ (P Q : config -> Prop), (forall σ', Q σ' ->
                                                 M1 ⦂ M2 ⦿ σ ⤳ σ' ->
                                                 P σ) ->
                                          M1 ⦂ M2 ⦿ [pre: P ] σ [post: Q]

  where "M1 '⦂' M2 '⦿' '[pre:' P ']' σ '[post:' Q ']'" := (necessary_triple_pr M1 M2 P σ Q).

  Hint Constructors necessary_triple necessary_triple_pr : hoare_db.

  Notation "M1 '⦂' M2 '◎' σ0 '…' '̱' '⊨' '{pre:' A1 '}' σ '{post:' A2 '}'" :=
    (M1 ⦂ M2 ⦿ {pre: fun σ => M1 ⦂ M2 ◎ σ0 … σ ⊨ A1} σ {post: fun σ' => M1 ⦂ M2 ◎ σ0 … σ' ⊨ A2})(at level 40).

  Notation "M1 '⦂' M2 '◎' σ0 '…s' '⊨' '{pre:' A1 '}' s '{post:' A2 '}'" :=
    (forall σ c, contn_is (s ;; c) σ -> (M1 ⦂ M2 ◎ σ0 … ̱ ⊨ {pre: A1 } σ {post: A2 }))(at level 40).

  Definition is_skip : config -> Prop :=
    fun σ => exists b, contn_is (c_ skip ;; b) σ.

  Definition is_call : config -> Prop :=
    fun σ => exists x α m args b, contn_is (c_ call x α m args ;; b) σ.

  Definition is_rtrn : config -> Prop :=
    fun σ => (exists v b, contn_is (c_ rtrn v ;; b) σ) \/ (exists v, contn_is (c_rtrn v) σ).

  Definition is_acc : config -> Prop :=
    fun σ => exists x v b, contn_is (c_ acc x v ;; b) σ.

  Definition is_mut : config -> Prop :=
    fun σ => exists α f v b, contn_is (c_ mut α f v ;; b) σ.

  Definition is_new : config -> Prop :=
    fun σ => exists C args b, contn_is (c_ new C args ;; b) σ.

  Definition empty_condition := (fun (_ : config) => True).
  Notation "∅" := (empty_condition)(at level 40).

  Definition waiting_frame_is :=
    fun (f : config -> Prop) σ => exists ϕ1 ϕ2 ψ, snd σ = ϕ1 :: ϕ2 :: ψ /\
                                                  f (fst σ, ϕ2 :: ψ).

  Definition is_return_to :=
    fun (f : config -> Prop) σ => is_rtrn σ /\
                           waiting_frame_is f σ.

  Definition is_call_to :=
    fun (f : config -> addr -> Prop) σ =>
      exists α, (exists x m args c, contn_is (c_ x ≔m α ▸ m ⟨ args ⟩ ;; c) σ) /\
           f σ α.

  Close Scope chainmail_scope.
  Close Scope reduce_scope.
End Hoare.
