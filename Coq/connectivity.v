Require Import common.
Require Import loo_def.
Require Import loo_properties.
Require Import loo_reduction_properties.
Require Import decoupled_classical_properties.
Require Import decoupling.
Require Import sbst_decoupled.
Require Import function_operations.
Require Import hoare.
Require Import List.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

Definition accss (χ : heap) (ϕ : frame) (α β : addr) : Prop :=
  (exists o f, χ α = Some o /\ flds o f = Some (v_addr β)) \/ ⌊this⌋ (χ, ϕ :: nil) ≜ v_addr α /\ (exists γ, vMap ϕ γ = Some (v_addr β)).

Definition cont (α : addr) (χ : heap) (ϕ : frame) (s : stmt) : Prop :=
  (exists statements, ϕ.(contn) = c_stmt (s;; statements)) /\ ⌊this⌋ (χ, ϕ :: nil) ≜ v_addr α.

Reserved Notation "'⌊' r '⌋' σ '≜◌' v" (at level 40).

Inductive interpret_x_f : ref -> config -> value -> Prop :=
| int_x_f : forall x f σ o α v, mapp σ x = Some (v_addr α) ->
                              fst σ α = Some o ->
                              flds o f = Some v ->
                                                            ⌊ x ◌ f ⌋ σ ≜◌ v
where "'⌊' r '⌋' σ '≜◌' v" := (interpret_x_f r σ v).

Lemma connectivity :
  forall (a b : addr) (M : mdl) (σ σ' : config) ϕ ϕ' ψ ψ' χ χ',
    σ = (χ, ϕ :: ψ) -> σ' = (χ', ϕ' :: ψ') ->
    σ_wf σ ->
    M ∙ σ ⤳ σ' -> 
    accss χ' ϕ' a b ->
      accss χ ϕ a b \/ exists c,
      (exists x y (ys : partial_map var var) m t, ⌊x⌋ σ ≜ v_addr a /\ ⌊y⌋ σ ≜ v_addr b /\ cont c χ ϕ (s_meth t x m ys) /\ exists k, ys k = Some y) \/
      (exists y, ⌊y⌋ σ ≜ v_addr b /\ cont c χ ϕ (s_rtrn y) /\ ⌊this⌋ σ ≜ v_addr a) \/
      (exists f x y, ⌊x⌋ σ ≜ v_addr a /\ ⌊y⌋ σ ≜ v_addr b /\ cont c χ ϕ (x ◌ f ≔ (r_ y))) \/
      (exists f z t,  ⌊z⌋ σ ≜ v_addr c /\ cont a χ ϕ (r_ t ≔ (z ◌ f)) /\ ⌊ z ◌ f ⌋ σ ≜◌ v_addr b)
.
Proof.
  intros.
  inversion H1; inversion H4; inversion H6.
  rewrite H in H10; inversion H10; subst.
  assert (HInϕ : In ϕ (ϕ :: ψ)). { crush. }
  apply H9 in HInϕ as Hself.
  inversion Hself as [χ_ ϕ_ [α_this [o_this Hthis]]]; subst.
  inversion H2; subst; simpl in *.
  - inversion H13; subst χ' ϕ0 ψ0.
    unfold accss in H3. destruct H3 as [ [o_f_b [f_b [Ho_f_b Hf_b]]] | [Hlocal [γ Hγ]]].
    + eauto.
    (* continuation gives you the witnesses, need to excl. middle on whether or no they assign to the right thing though? *)
Abort.