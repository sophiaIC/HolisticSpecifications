Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.
Require Import loo_def.
Inductive asrt : Type :=
(*simpl*)
| a_exp   : exp -> asrt
| a_eq    : exp -> exp -> asrt (* is this necessary? isn't it a redundant subcase of a_exp? *)
| a_class : exp -> cls -> asrt
| a_set   : exp -> varSet -> asrt

(*connectives*)
| a_arr   : asrt -> asrt -> asrt
| a_and   : asrt -> asrt -> asrt
| a_or    : asrt -> asrt -> asrt
| a_neg   : asrt -> asrt

(*quantifiers*)
| a_all_x : asrt -> asrt
| a_all_Σ : asrt -> asrt
| a_ex_x  : asrt -> asrt
| a_ex_Σ  : asrt -> asrt

(*permission*)
| a_acc   : var -> var -> asrt

(*control*)
| a_call  : var -> var -> mth -> var -> asrt

(*time*)
| a_next  : asrt -> asrt
| a_will  : asrt -> asrt
| a_prev  : asrt -> asrt
| a_was   : asrt -> asrt

(*space*)
| a_in    : asrt -> varSet -> asrt

(*viewpoint*)
| a_extrn : var -> asrt
| a_intrn : var -> asrt.

Instance asrtFoldableVar : PropFoldable asrt var :=
  {
    foldAnd :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => foldAnd e f n P
        | a_eq e1 e2        => foldAnd e1 f n P /\ foldAnd e2 f n P
        | a_class e C       => foldAnd e f n P
        | a_set e Σ         => foldAnd e f n P
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P /\ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => f v1 n /\ f v2 n
        (*control*)
        | a_call v1 v2 m v3 => f v1 n /\ f v2 n /\ f v3 n
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => f v n
        | a_intrn v          => f v n
        end;

    foldOr :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => foldAnd e f n P
        | a_eq e1 e2        => foldAnd e1 f n P /\ foldAnd e2 f n P
        | a_class e C       => foldAnd e f n P
        | a_set e Σ         => foldAnd e f n P
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P \/ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => f v1 n /\ f v2 n
        (*control*)
        | a_call v1 v2 m v3 => f v1 n \/ f v2 n \/ f v3 n
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => f v n
        | a_intrn v          => f v n
        end
  }.

Instance asrtFoldableVarSet : PropFoldable asrt varSet :=
  {
    foldAnd :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => P
        | a_eq e1 e2        => P
        | a_class e C       => P
        | a_set e Σ         => f Σ n
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P /\ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P /\ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f n P
        | a_all_Σ A'      => foldA A' f (S n) P
        | a_ex_x A'       => foldA A' f n P
        | a_ex_Σ A'       => foldA A' f (S n) P
        (*permission*)
        | a_acc v1 v2       => P
        (*control*)
        | a_call v1 v2 m v3 => P
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P /\ f Σ n
        (*viewpoint*)
        | a_extrn v          => P
        | a_intrn v          => P
        end;

    foldOr :=
      fix foldA A f n P :=
        match A with
        | a_exp e           => P
        | a_eq e1 e2        => P
        | a_class e C       => P
        | a_set e Σ         => f Σ n
        (*connectives*)
        | a_arr A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_and A1 A2       => foldA A1 f n P \/ foldA A2 f n P
        | a_or A1 A2        => foldA A1 f n P \/ foldA A2 f n P
        | a_neg A'          => foldA A' f n P
        (*quantifiers*)      
        | a_all_x A'      => foldA A' f (S n) P
        | a_all_Σ A'      => foldA A' f n P
        | a_ex_x A'       => foldA A' f (S n) P
        | a_ex_Σ A'       => foldA A' f n P
        (*permission*)
        | a_acc v1 v2       => P
        (*control*)
        | a_call v1 v2 m v3 => P
        (*time*)
        | a_next A'         => foldA A' f n P
        | a_will A'         => foldA A' f n P
        | a_prev A'         => foldA A' f n P
        | a_was A'          => foldA A' f n P
        (*space*)
        | a_in A' Σ         => foldA A' f n P
        (*viewpoint*)
        | a_extrn v          => P
        | a_intrn v          => P
        end
  }.

Definition closed_A (A : asrt)(n : nat) :=
  foldAnd A
          (fun x n' =>
             match x with
             | hole m => n' <> m
             | _ => True
             end)
          n
          True.

Definition closed_A_set (A : asrt)(n : nat) :=
  foldAnd A
          (fun x n' =>
             match x with
             | s_hole m => n' <> m
             | _ => True
             end)
          n
          True.


(*Inductive closed_A : asrt -> nat -> Prop :=
| cla_exp : forall e n, closed e n ->
                   closed_A (a_exp e) n
| cla_eq  : forall e1 e2 n, closed e1 n ->
                       closed e2 n ->
                       closed_A (a_eq e1 e2) n
| cla_class : forall e C n, closed e n ->
                       closed_A (a_class e C) n
| cla_set : forall e Σ n, closed_A (a_set e Σ) n
| cla_arr : forall A1 A2 n, closed_A A1 n ->
                       closed_A A2 n ->
                       closed_A (a_arr A1 A2) n
| cla_and : forall A1 A2 n, closed_A A1 n ->
                       closed_A A2 n ->
                       closed_A (a_and A1 A2) n
| cla_or : forall A1 A2 n, closed_A A1 n ->
                      closed_A A2 n ->
                      closed_A (a_or A1 A2) n
| cla_neg : forall A n, closed_A A n ->
                   closed_A (a_neg A) n
| cla_all_x : forall A n, closed_A A (S n) ->
                     closed_A (a_all_x A) n
| cla_all_Σ : forall A n, closed_A A n ->
                     closed_A (a_all_Σ A) n
| cla_ex_x : forall A n, closed_A A (S n) ->
                    closed_A (a_ex_x A) n
| cla_ex_Σ : forall A n, closed_A A n ->
                    closed_A (a_ex_Σ A) n
| cla_acc : forall x y n, closed x n ->
                     closed y n ->
                     closed_A (a_acc x y) n
| cla_call : forall x y m z n, closed x n ->
                          closed y n ->
                          closed z n ->
                          closed_A (a_call x y m z) n
| cla_next : forall A n, closed_A A n ->
                    closed_A (a_next A) n
| cla_will : forall A n, closed_A A n ->
                    closed_A (a_will A) n
| cla_prev : forall A n, closed_A A n ->
                    closed_A (a_prev A) n
| cla_was : forall A n, closed_A A n ->
                   closed_A (a_was A) n.*)

Ltac closed_unfold :=
  match goal with
  | [H : closed_e _ _ |- _] => unfold closed_e in H; try solve [crush]
  | [H : closed_A _ _ |- _] => unfold closed_A in H; try solve [crush]
  | [H : closed_A_set _ _ |- _] => unfold closed_A_set in H; try solve [crush]
  end.

Instance substAssertionVar : Subst asrt nat :=
  {sbst :=
     fix subst' A n x :=
       match A with
       | a_exp e           => a_exp (sbst e n (bind x))
       | a_eq e1 e2        => a_eq (sbst e1 n (bind x))
                                  (sbst e2 n (bind x))
       | a_class e C       => a_class (sbst e n (bind x)) C
       | a_set e Σ         => a_set (sbst e  n (bind x)) Σ
       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n x) (subst' A2 n x)
       | a_and A1 A2       => a_and (subst' A1 n x) (subst' A2 n x)
       | a_or A1 A2        => a_or (subst' A1 n x) (subst' A2 n x)
       | a_neg A'          => a_neg (subst' A' n x)
       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' (S n) x)
       | a_all_Σ A'      => a_all_Σ (subst' A' n x)
       | a_ex_x A'       => a_ex_x (subst' A' (S n) x)
       | a_ex_Σ A'       => a_ex_Σ (subst' A' n x)
       (*permission*)
       | a_acc v1 v2       => a_acc (sbst v1 n (bind x)) (sbst v2 n (bind x))
       (*control*)
       | a_call v1 v2 m v3 => a_call ([bind x /s n] v1)
                                    ([bind x /s n] v2) m
                                    ([bind x /s n] v3)
       (*time*)
       | a_next A'         => a_next (subst' A' n x)
       | a_will A'         => a_will (subst' A' n x)
       | a_prev A'         => a_prev (subst' A' n x)
       | a_was A'          => a_was (subst' A' n x)
       (*space*)
       | a_in A' Σ         => a_in (subst' A' n x) Σ
       (*viewpoint*)
       | a_extrn v          => a_extrn ([(bind x) /s n] v)
       | a_intrn v          => a_intrn ([(bind x) /s n] v)
       end;

   closed := closed_A
  }.
Proof.
  intros a;
    induction a;
    intros;
    try solve [repeat rewrite closed_subst; auto];
    auto;
    try solve [repeat rewrite closed_subst; closed_unfold].
Defined.
        
Instance substAssertionVarSet : Subst asrt varSet :=
  {
    sbst :=
     fix subst' A n Σ :=
       match A with
       (*simpl*)
       | a_set e Σ'         => a_set e ([Σ /s n] Σ')

       (*connectives*)
       | a_arr A1 A2       => a_arr (subst' A1 n Σ) (subst' A2 n Σ)
       | a_and A1 A2       => a_and (subst' A1 n Σ) (subst' A2 n Σ)
       | a_or A1 A2        => a_or (subst' A1 n Σ) (subst' A2 n Σ)
       | a_neg A'          => a_neg (subst' A' n Σ)

       (*quantifiers*)      
       | a_all_x A'      => a_all_x (subst' A' n Σ)
       | a_all_Σ A'      => a_all_Σ (subst' A' (S n) Σ)
       | a_ex_x A'       => a_ex_x (subst' A' (n) Σ)
       | a_ex_Σ A'       => a_ex_Σ (subst' A' (S n) Σ)

       (*time*)
       | a_next A'         => a_next (subst' A' n Σ)
       | a_will A'         => a_will (subst' A' n Σ)
       | a_prev A'         => a_prev (subst' A' n Σ)
       | a_was A'          => a_was (subst' A' n Σ)

       (*space*)
       | a_in A' Σ'         => a_in (subst' A' n Σ) ([Σ /s n] Σ')

       | _          => A
       end;

    closed := closed_A_set
  }.
Proof.
  intros a;
    induction a;
    intros;
    try solve [repeat rewrite closed_subst; closed_unfold; auto];
    auto.
Defined.

(*
implication cannot be directly used due to strict positivity requirement of Coq
thus, satisfaction rules are in CNF

Similarly, (¬ A) ≡ (A -> False) which also violates the strict positivity 
requirement of Coq thus we define sat mutually with nsat, the negation of sat

For positivity discussion, see: http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html#lab30
 *)

Inductive fresh_x : nat -> config -> asrt -> Prop :=
| frsh : forall x σ A, map (snd σ) x = None ->
                  closed A x -> 
                  fresh_x x σ A.

Reserved Notation "M '∙' σ '⊨' A"(at level 40).
Reserved Notation "M '∙' σ '⊭' A"(at level 40).

(*
  satisfaction only uses one module at the moment
  this needs to change once the time assetions are
  properly modeled
 *)

Inductive sat : mdl -> config -> asrt -> Prop :=
(*simple*)
| sat_exp   : forall M σ e, M ∙ σ ⊢ e ↪ ev_true ->
                       M ∙ σ ⊨ a_exp e

| sat_class : forall M σ e C α o, M ∙ σ ⊢ e ↪ (ev_addr α) ->
                             map σ α = Some o -> 
                             o.(cname) = C ->
                             M ∙ σ ⊨ (a_class e C)

| sat_set   : forall M σ e Σ α As, M ∙ σ ⊢ e ↪ (ev_addr α) ->
                              ⌊ Σ ⌋ σ ≜′ As ->
                              In α As ->
                              M ∙ σ ⊨ (a_set e (s_bind Σ))

(*connectives*)
| sat_and   : forall M σ A1 A2, M ∙ σ ⊨ A1 ->
                           M ∙ σ ⊨ A2 ->
                           M ∙ σ ⊨ (a_and A1 A2)
                               
| sat_or1   : forall M σ A1 A2, M ∙ σ ⊨ A1 ->
                           M ∙ σ ⊨ (a_or A1 A2)
                               
| sat_or2   : forall M σ A1 A2, M ∙ σ ⊨ A2 ->
                           M ∙ σ ⊨ (a_or A1 A2)

| sat_arr1  : forall M σ A1 A2, M ∙ σ ⊨ A2 ->
                           M ∙ σ ⊨ (a_arr A1 A2)

| sat_arr2  : forall M σ A1 A2, M ∙ σ ⊭ A1 ->
                           M ∙ σ ⊨ (a_arr A1 A2)
                             
| sat_not   : forall M σ A, M ∙ σ ⊭ A ->
                       M ∙ σ ⊨ (a_neg A)

(*quantifiers*)
| sat_all_x : forall M σ A, (forall α z, exists (o : obj),
                             map σ α = Some o ->
                             fresh_x z σ A ->
                             M ∙ (update_σ_map σ z α) ⊨ ([z /s 0]A)) ->
                       M ∙ σ ⊨ (a_all_x A)

| sat_ex_x  : forall M σ A z α, (exists (o : obj), map σ α = Some o) ->
                           M ∙ (update_σ_map σ z α) ⊨ ([z /s 0] A) ->
                           M ∙ σ ⊨ (a_all_x A)

(*viewpoint*)
| sat_extrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                             map σ α = Some o ->
                             o.(cname) = C ->
                             M C = None ->
                             M ∙ σ ⊨ a_extrn (bind x)

| sat_intrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                             map σ α = Some o ->
                             o.(cname) = C ->
                             (exists CDef, M C = Some CDef) ->
                             M ∙ σ ⊨ a_intrn (bind x)

(*space*)
| sat_in    : forall M σ A Σ σ', σ ↓ Σ ≜ σ' ->
                            M ∙ σ' ⊨ A ->
                            M ∙ σ ⊨ A

(*time*)

where "M '∙' σ '⊨' A" := (sat M σ A)

with
nsat : mdl -> config -> asrt -> Prop :=
(*simple*)
| nsat_exp : forall M σ e v, M ∙ σ ⊢ e ↪ v ->
                        v <> ev_true ->
                        M ∙ σ ⊭ (a_exp e)

| nsat_class : forall M σ e C C' α o, M ∙ σ ⊢ e ↪ (ev_addr α) ->
                                 map σ α = Some o -> 
                                 o.(cname) = C' ->
                                 C <> C' ->
                                 M ∙ σ ⊭ (a_class e C)

| nsat_set   : forall M σ e Σ As, ⌊ Σ ⌋ σ ≜′ As ->
                             (forall α, M ∙ σ ⊢ e ↪ (ev_addr α) -> ~ In α As) ->
                             M ∙ σ ⊭ (a_set e (s_bind Σ))

(*connectives*)
| nsat_and1  : forall M σ A1 A2, M ∙ σ ⊭ A1 ->
                            M ∙ σ ⊭ (a_and A1 A2)
                        
| nsat_and2  : forall M σ A1 A2, M ∙ σ ⊭ A2 ->
                            M ∙ σ ⊭ (a_and A1 A2)
                        
| nsat_or    : forall M σ A1 A2, M ∙ σ ⊭ A1 ->
                            M ∙ σ ⊭ A2 ->
                            M ∙ σ ⊭ (a_or A1 A2)

| nsat_arr   : forall M σ A1 A2, M ∙ σ ⊨ A1 ->
                            M ∙ σ ⊭ A2 ->
                            M ∙ σ ⊭ (a_arr A1 A2)
                              
| nsat_not   : forall M σ A, M ∙ σ ⊨ A ->
                        M ∙ σ ⊭ (a_neg A)

(*quantifiers*)
| nsat_all_x : forall M σ A α, (exists y, map σ y = Some α) ->
                          M ∙ (fst σ, snd σ) ⊭ A ->
                          M ∙ σ ⊭ (a_all_x A) (*this is wrong: it needs to be for all addresses, and 
                                                      some mapping for z needs to be added to the config: σ[z ↦ α]*)

| nsat_ex_x : forall M σ A, (forall y α, map σ y = Some α ->
                               M ∙ σ ⊭ ([y /s 0] A)) ->
                       M ∙ σ ⊭ (a_ex_x A)

(*viewpoint*) (* well-formeness? This is important!!!!*)
(*| nsat_extrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_extrn (bind x)

| nsat_extrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_extrn (bind x)*) 

| nsat_extrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                              map σ α = Some o ->
                              o.(cname) = C ->
                              (exists CDef, M C = Some CDef) ->
                              M ∙ σ ⊭ a_extrn (bind x)

(*| nsat_intrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_intrn (bind x)

| nsat_intrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_intrn (bind x)*) (*not needed. In the case where x or α are not defined, then we can't satisfy A*)

| nsat_intrn : forall M σ x α o C, ⌊ x ⌋ σ ≜ α ->
                              map σ α = Some o ->
                              o.(cname) = C ->
                              M C = None ->
                              M ∙ σ ⊭ a_intrn (bind x)

(*space*)
| nsat_in    : forall M σ A Σ σ', σ ↓ Σ ≜ σ' ->
                             M ∙ σ' ⊭ A ->
                             M ∙ σ ⊭ A

where "M '∙' σ '⊭' A" := (nsat M σ A).
