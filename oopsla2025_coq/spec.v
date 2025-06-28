Require Export Arith.
Require Import List.
Require Import Bool.

Require Import language_def.
Require Import hoare.

(** * Specification proof rules - Section 6.3 *)

Module SpecSatisfaction.

  Import LanguageDefinition.
  Import Hoare.

  Declare Scope hoare_scope.
(*  Open Scope assert_scope.*)
  Open Scope hoare_scope.

  Inductive spec_sat : module -> l_spec -> Prop :=
  | spec_combine : forall M L1 L2, spec_sat M L1 ->
                              spec_sat M L2 ->
                              spec_sat M (S_and L1 L2)
  | spec_method : forall M C meth A1 A2 A3 CDef m,
      snd M C = Some CDef ->
      c_meths CDef meth = Some m ->
      M ⊢ ⦃ a_typs ((result, rtrn m)::
                      (this, t_cls C) ::
                      (params m)) ∧
                A1 ∧ (adapt A1 (this :: (map fst (params m))))  ⦄
        (body m)
        ⦃ A2 ∧ (adapt A2 (result :: nil)) ⦄ ||
        ⦃ A3 ⦄ ->
      spec_sat M (S_mth C meth (params m) A1 A2 A3)

  | spec_invariant : forall M A xCs,
      (forall C CDef m meth,
          snd M C = Some CDef ->
          c_meths CDef meth = Some m ->
          vis m = public ->
          M ⊢
            ⦃ a_typs ((result, rtrn m)::
                      (this, t_cls C) ::
                      (params m)) ∧
                (a_typs xCs) ∧
                A ∧ (adapt A (this :: (map fst (params m)))) ⦄
            (body m)
            ⦃ A ∧ (adapt A (result :: nil)) ⦄ || ⦃ A ⦄) ->
      spec_sat M (S_inv xCs A).

End SpecSatisfaction.
