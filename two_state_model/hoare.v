Require Export Arith.
Require Import List.

Require Import CpdtTactics.
Require Import common.
Require Import assert.
Require Export external_state_semantics.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.


Module Hoare.

  Export Assert.

  Inductive 

  Definition hoare_triple (M : module)(P : asrt)(s : stmt)(Q : asrt) :=
    forall χ lcl s' ψ σ1 σ2, reduction M (χ, frm lcl (c_stmt s') ;; ψ) σ2 ->
                        s' = s ->
                        σ1 = (χ, frm lcl (c_stmt s') ;; ψ) ->
                        sat M σ1 P ->
                        sat M σ2 Q.

  Notation "M ⊨ ⦃ P ⦄ s ⦃ Q ⦄" := (hoare_triple M P s Q)(at level 40).

  (* Proof Rules *)

  Inductive hoare : module -> asrt -> stmt -> Q

End Hoare.
