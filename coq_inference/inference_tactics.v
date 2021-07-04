Require Import CpdtTactics.
Require Import common.
Require Import L_def.
Require Import exp.
Require Import defs.
Require Import operational_semantics.
Require Import inference.
Require Import List.
Require Export Coq.Lists.ListSet.

Module InferenceTactics(L : LanguageDef).

  Import L.
  Module L_Inference := Inference(L).
  Export L_Inference.

  Open Scope chainmail_scope.
  Open Scope inference_scope.

  Ltac extract1 v' n' :=
    match goal with
    | [|- ?M ⊢ _ to1 ?A2 onlyIf ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    | [|- ?M ⊢ _ to ?A2 onlyIf ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    | [|- ?M ⊢ _ to ?A2 onlyThrough ?A3] =>
      let A2' := fresh "A" in
      let H2 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A2 as A2'  eqn : H2;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A2' A3'
    end.

  Ltac extract2 v' n' :=
    match goal with
    | [|- ?M ⊢ ?A1 to1 _ onlyIf ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3
    | [|- ?M ⊢ ?A1 to _ onlyIf ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3
    | [|- ?M ⊢ ?A1 to _ onlyThrough ?A3] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A3' := fresh "A" in
      let H3 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A3 as A3'  eqn : H3;
      extract v' n';
      subst A1' A3'
    end.

  Ltac extract3 v' n' :=
    match goal with
    | [|- ?M ⊢ ?A1 to1 ?A2 onlyIf _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst

    | [|- ?M ⊢ ?A1 to ?A2 onlyIf _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst A1' A2'

    | [|- ?M ⊢ ?A1 to ?A2 onlyThrough _] =>
      let A1' := fresh "A" in
      let H1 := fresh in
      let A2' := fresh "A" in
      let H2 := fresh in
      remember A1 as A1'  eqn : H1;
      remember A2 as A2'  eqn : H2;
      extract v' n';
      subst A1' A2'
    end.

End InferenceTactics.

