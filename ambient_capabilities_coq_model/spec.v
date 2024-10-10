Require Export Arith.
Require Import List.
Require Import Bool.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert.
Require Export operational_semantics.
Require Import assert_theory.
Require Import hoare.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module SpecSatisfaction.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.

  Declare Scope hoare_scope.
  Open Scope assert_scope.
  Open Scope hoare_scope.

  Inductive spec_sat : module -> l_spec -> Prop :=
  | spec_combine : forall M L1 L2, spec_sat M L1 ->
                              spec_sat M L2 ->
                              spec_sat M (S_and L1 L2)

  (* can I clean the adapt up??
     type class?
     would allow overloading for both lists and single variables ...
   *)

  (*
    question: do we need the public/private qualifiers if we have meth specs on public methods?
   *)
  (*
    do we need to protect A3 from result???
   *)
  | spec_method : forall M C meth A1 A2 A3 CDef m,
      snd M C = Some CDef ->
      c_meths CDef meth = Some m ->
      M ⊢ ⦃ a_typs ((this, t_cls C) :: (params m)) ∧ A1 ⦄
        (body m)
        ⦃ A2 ∧ (adapt A2 (result :: nil)) ⦄ ||
        ⦃ A3 ⦄ ->
      spec_sat M (S_mth C meth (params m) A1 A2 A3)

  | spec_invariant : forall M A xCs,
      (forall C CDef m meth,
          snd M C = Some CDef ->
          c_meths CDef meth = Some m ->
          M ⊢
            ⦃ a_typs ((this, t_cls C) :: (params m)) ∧
                (a_typs (map (fun xC => (fst xC, t_cls (snd xC))) xCs)) ∧ A ⦄
            (body m)
            ⦃ A ∧ (adapt A (result :: nil)) ⦄ || ⦃ A ⦄) ->
      spec_sat M (S_inv xCs A).

End SpecSatisfaction.
