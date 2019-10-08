Require Export Arith.
Require Import CpdtTactics.
Require Import List.
Require Import common.
Require Import loo_def.

(** Assertion Variables *)

Inductive a_var : Type :=
| a_hole : nat -> a_var
| a_bind : var -> a_var.

(** Assertion syntax  *)

Inductive asrt : Type :=
(** Simple: *)
| a_exp   : exp -> asrt
| a_eq    : exp -> exp -> asrt (* is this necessary? isn't it a redundant subcase of a_exp? *)
| a_class : exp -> cls -> asrt
| a_set   : exp -> varSet -> asrt

(** Connectives: *)
| a_arr   : asrt -> asrt -> asrt
| a_and   : asrt -> asrt -> asrt
| a_or    : asrt -> asrt -> asrt
| a_neg   : asrt -> asrt

(** Quantifiers: *)
| a_all_x : asrt -> asrt
| a_all_Σ : asrt -> asrt
| a_ex_x  : asrt -> asrt
| a_ex_Σ  : asrt -> asrt

(** Permission: *)
| a_acc   : a_var -> a_var -> asrt

(** Control: *)
| a_call  : a_var -> a_var -> mth -> partial_map var a_var  -> asrt

(** Time: *)
| a_next  : asrt -> asrt
| a_will  : asrt -> asrt
| a_prev  : asrt -> asrt
| a_was   : asrt -> asrt

(** Space: *)
| a_in    : asrt -> varSet -> asrt

(** Viewpoint: *)
| a_extrn : a_var -> asrt
| a_intrn : a_var -> asrt.

(*Instance asrtFoldableVar : PropFoldable asrt nat :=
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
          True.*)
          

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

(*Ltac closed_unfold :=
  match goal with
  | [H : closed_e _ _ |- _] => unfold closed_e in H; try solve [crush]
  | [H : closed_A _ _ |- _] => unfold closed_A in H; try solve [crush]
  | [H : closed_A_set _ _ |- _] => unfold closed_A_set in H; try solve [crush]
  end.*)

Class Subst (A B C : Type) : Type :=
  {
    sbst : A -> B -> C -> A
  }.

Notation "'[' c '/s' b ']' a" := (sbst a b c)(at level 80).

Instance substExp : Subst exp nat var :=
  {
    sbst :=
      fix subst' e n x :=
        match e with
        | e_hole m => if m =? n
                     then e_var x
                     else e
        | e_eq e1 e2 => e_eq (subst' e1 n x) (subst' e2 n x)
        | e_if e1 e2 e3 => e_if (subst' e1 n x) (subst' e2 n x) (subst' e3 n x)
        | e_acc_f e' f => e_acc_f (subst' e' n x) f
        | e_acc_g e1 g e2 => e_acc_g (subst' e1 n x) g (subst' e2 n x)
        | _ => e
        end
  }.

Instance substAVar : Subst a_var nat var :=
  {
    sbst x n y :=
      match x with
      | a_hole m => if (m =? n)
                   then a_bind y
                   else x
      | _ => x
      end
  }.

Instance substAVarMap : Subst (partial_map var a_var) nat var :=
  {
    sbst avMap n x := fun (y : var) =>
                        match avMap y with
                        | Some z => Some ([x /s n] z)
                        | None => None
                        end
  }.

Instance substAssertionVar : Subst asrt nat var :=
  {sbst :=
     fix subst' A n x :=
       match A with
       | a_exp e           => a_exp (sbst e n x)
       | a_eq e1 e2        => a_eq (sbst e1 n x)
                                  (sbst e2 n x)
       | a_class e C       => a_class (sbst e n x) C
       | a_set e Σ         => a_set (sbst e  n x) Σ
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
       | a_acc v1 v2       => a_acc (sbst v1 n x) (sbst v2 n x)
       (*control*)
       | a_call v1 v2 m avMap => a_call ([x /s n] v1)
                                       ([x /s n] v2) m
                                       ([x /s n] avMap)
       (*time*)
       | a_next A'         => a_next (subst' A' n x)
       | a_will A'         => a_will (subst' A' n x)
       | a_prev A'         => a_prev (subst' A' n x)
       | a_was A'          => a_was (subst' A' n x)
       (*space*)
       | a_in A' Σ         => a_in (subst' A' n x) Σ
       (*viewpoint*)
       | a_extrn v          => a_extrn ([x /s n] v)
       | a_intrn v          => a_intrn ([x /s n] v)
       end
  }.

Instance varSetSubst : Subst varSet nat varSet :=
  {
    sbst :=
      fix subst' Σ1 n Σ2 :=
        match Σ1 with
        | s_hole m => if (m =? n)
                     then Σ2
                     else Σ1
        | _ => Σ1
        end
  }.
        
Instance substAssertionVarSet : Subst asrt nat varSet :=
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
  }.

Inductive  closed_exp : exp -> nat -> Prop :=
| cl_val   : forall v n, closed_exp (e_val v) n
| cl_var   : forall x n, closed_exp (e_var x) n
| cl_hole  : forall m n, n <> m ->
                    closed_exp (e_hole m) n
| cl_eq    : forall e1 e2 n, closed_exp e1 n ->
                        closed_exp e2 n ->
                        closed_exp (e_eq e1 e2) n
| cl_if    : forall e1 e2 e3 n, closed_exp e1 n ->
                           closed_exp e2 n ->
                           closed_exp e3 n ->
                           closed_exp (e_if e1 e2 e3) n
| cl_acc_f : forall e f n, closed_exp e n ->
                      closed_exp (e_acc_f e f) n
| cl_acc_g : forall e f e' n, closed_exp e n ->
                         closed_exp e' n ->
                         closed_exp (e_acc_g e f e') n.

Inductive  notin_exp : exp -> var -> Prop :=
| ni_val   : forall v x, notin_exp (e_val v) x
| ni_var   : forall x y, x <> y ->
                    notin_exp (e_var x) y
| ni_hole  : forall m x, notin_exp (e_hole m) x
| ni_eq    : forall e1 e2 x, notin_exp e1 x ->
                        notin_exp e2 x ->
                        notin_exp (e_eq e1 e2) x
| ni_if    : forall e1 e2 e3 x, notin_exp e1 x ->
                           notin_exp e2 x ->
                           notin_exp e3 x ->
                           notin_exp (e_if e1 e2 e3) x
| ni_acc_f : forall e f x, notin_exp e x ->
                      notin_exp (e_acc_f e f) x
| ni_acc_g : forall e f e' x, notin_exp e x ->
                         notin_exp e' x ->
                         notin_exp (e_acc_g e f e') x.

Definition notin_a_var (x : a_var)(y : var) : Prop :=
  match x with
  | a_bind z => z <> y
  | _ => False
  end.

Definition notin_av_map (avMap : partial_map var a_var)(x : var) : Prop :=
  forall y z, avMap y = Some z ->
         notin_a_var z x.

Inductive notin_Ax  : asrt -> var -> Prop :=

(** Simple *)
| ni_exp : forall e x, notin_exp e x ->
                  notin_Ax (a_exp e) x
| ni_aeq : forall e1 e2 x, notin_exp e1 x ->
                      notin_exp e2 x ->
                      notin_Ax (a_eq e1 e2) x
| ni_class : forall e C x, notin_exp e x ->
                      notin_Ax (a_class e C) x
| ni_set   : forall e Σ x, notin_exp e x ->
                      notin_Ax (a_set e Σ) x

(** Connectives *)
| ni_arr   : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_arr A1 A2) x
| ni_and   : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_and A1 A2) x
| ni_or    : forall A1 A2 x, notin_Ax A1 x ->
                        notin_Ax A2 x ->
                        notin_Ax (a_or A1 A2) x
| ni_neg   : forall A x, notin_Ax A x ->
                    notin_Ax (a_neg A) x

(** Quantifiers *)
| ni_all_x : forall A x, notin_Ax A x ->
                    notin_Ax (a_all_x A) x
| ni_all_Σ : forall A x, notin_Ax A x ->
                    notin_Ax (a_all_Σ A) x
| ni_ex_x  : forall A x, notin_Ax A x ->
                    notin_Ax (a_ex_x A) x
| ni_ex_Σ  : forall A x, notin_Ax A x ->
                    notin_Ax (a_ex_Σ A) x

(** Permission: *)
| ni_acc   : forall x y x', notin_a_var x x' ->
                      notin_a_var y x' ->
                      notin_Ax (a_acc x y) x'

(** Control: *)
| ni_call  : forall x y z avMap m, notin_a_var y x ->
                              notin_a_var z x ->
                              notin_av_map avMap x ->
                              notin_Ax (a_call y z m avMap) x

(** Time: *)
| ni_next  : forall A x, notin_Ax A x ->
                    notin_Ax (a_next A) x
| ni_will  : forall A x, notin_Ax A x ->
                    notin_Ax (a_will A) x
| ni_prev  : forall A x, notin_Ax A x ->
                    notin_Ax (a_prev A) x
| ni_was   : forall A x, notin_Ax A x ->
                    notin_Ax (a_was A) x

(** Space: *)
| ni_in    : forall A Σ x, notin_Ax A x ->
                      notin_Ax (a_in A Σ) x

(** Viewpoint: *)
| ni_extrn : forall x y,  notin_a_var x y ->
                     notin_Ax (a_extrn x) y
| ni_intrn : forall x y, notin_a_var x y ->
                    notin_Ax (a_intrn x) y.

Inductive fresh_x : var -> config -> asrt -> Prop :=
| frsh : forall x σ A, map (snd σ) x = None ->
                  notin_Ax A x ->
                  fresh_x x σ A.

Reserved Notation "σ1 '◁' σ2 '≜' σ3" (at level 40).

Fixpoint rename_s (s : stmt)(xs ys : list var) : option stmt :=
  match xs, ys with
  | nil, nil => Some s
  | x::xs', y::ys' => rename_s (❲x ↦ y❳ s) xs' ys'
  | _, _ => None
  end.

Fixpoint updates {B C : Type} `{Eqb B}
         (bs : list (B * B))
         (map1 : partial_map B C)
         (map2 : partial_map B C) : partial_map B C :=
  match bs with
  | nil => map1
  | (b1, b2)::bs' => fun b => if eqb b b1
                          then map2 b2
                          else (updates bs' map1 map2) b
  end.

Inductive zip {A : Type} : list A -> list A -> list (A * A) -> Prop :=
| z_nil : zip nil nil nil
| z_cons : forall a1 a2 l1 l2 l, zip (a1::l1) (a2::l2) ((a1, a2)::l).

Inductive adaptation : config -> config -> config -> Prop :=
| a_adapt : forall σ σ' ϕ ϕ' ϕ'' contn β β' β'' ψ' χ' zs zs' s s' Zs,
    peek (snd σ) = Some ϕ ->
    σ' = (χ', (ϕ' :: ψ')) ->
    ϕ = frm β contn ->
    ϕ' = frm β' (c_stmt s) ->
    (forall z, In z zs' -> β z = None) ->
    (forall z, In z zs' -> β' z = None) ->
    (forall z, In z zs -> exists y, β z = Some y) ->
    (forall z, ~In z zs -> β z = None) ->
    rename_s s zs zs' = Some s' ->
    zip zs' zs Zs ->
    β'' = updates Zs β β' ->
    ϕ'' = frm β'' (c_stmt s') ->
    σ ◁ σ' ≜ (χ', ϕ'' :: ψ')

where "σ1 '◁' σ2 '≜' σ3" := (adaptation σ1 σ2 σ3).

Reserved Notation "M1 '⦂' M2 '◎' σ '⊨' A"(at level 40).
Reserved Notation "M1 '⦂' M2 '◎' σ '⊭' A"(at level 40).

Inductive in_ref : var -> ref -> Prop :=
| in_r_var : forall x, in_ref x (r_var x)
| in_r_fld : forall x f, in_ref x (r_fld x f).

Inductive in_stmt : var -> stmt -> Prop :=
| in_asgn_1 : forall x y z, in_ref x y ->
                       in_stmt x (s_asgn y z)
| in_asgn_2 : forall x y z, in_ref x z ->
                       in_stmt x (s_asgn y z)
| in_meth_1 : forall x y m ps, in_stmt x (s_meth x y m ps)
| in_meth_2 : forall x y m ps, in_stmt y (s_meth x y m ps)
| in_meth_3 : forall x y z m ps, (exists x', ps x' = Some z) ->
                            in_stmt z (s_meth x y m ps)
| in_new_1 : forall x C ps, in_stmt x (s_new x C ps)
| in_new_2 : forall x y C ps, (exists z, ps z = Some y) ->
                         in_stmt y (s_new x C ps)
| in_stmts_1 : forall x s1 s2, in_stmt x s1 ->
                          in_stmt x (s_stmts s1 s2)
| in_stmts_2 : forall x s1 s2, in_stmt x s2 ->
                          in_stmt x (s_stmts s1 s2)
| in_retrn : forall x, in_stmt x (s_rtrn x).

(*
implication cannot be directly used due to strict positivity requirement of Coq
thus, satisfaction rules are in CNF

Similarly, (¬ A) ≡ (A -> False) which also violates the strict positivity 
requirement of Coq thus we define sat mutually with nsat, the negation of sat

For positivity discussion, see: http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html#lab30
 *)

Inductive sat : mdl -> mdl -> config -> asrt -> Prop :=
(** Simple: *)
| sat_exp   : forall M1 M2 σ e, M1 ∙ σ ⊢ e ↪ v_true ->
                           M1 ⦂ M2 ◎ σ ⊨ a_exp e

| sat_class : forall M1 M2 σ e C α o, M1 ∙ σ ⊢ e ↪ (v_addr α) ->
                                 map σ α = Some o -> 
                                 o.(cname) = C ->
                                 M1 ⦂ M2 ◎ σ ⊨ (a_class e C)

| sat_set   : forall M1 M2 σ e Σ α As, M1 ∙ σ ⊢ e ↪ (v_addr α) ->
                                  ⌊ Σ ⌋ σ ≜′ As ->
                                  In α As ->
                                  M1 ⦂ M2 ◎ σ ⊨ (a_set e (s_bind Σ))

(** Connectives: *)
| sat_and   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_and A1 A2)
                                  
| sat_or1   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_or A1 A2)
                                  
| sat_or2   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_or A1 A2)

| sat_arr1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A2 ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_arr A1 A2)

| sat_arr2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_arr A1 A2)
                                  
| sat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊭ A ->
                           M1 ⦂ M2 ◎ σ ⊨ (a_neg A)

(** Quantifiers: *)
| sat_all_x : forall M1 M2 σ A, (forall α z, exists (o : obj),
                                 map σ α = Some o ->
                                 fresh_x z σ A ->
                                 M1 ⦂ M2 ◎ (update_σ_map σ z (v_addr α)) ⊨ ([z /s 0]A)) ->
                           M1 ⦂ M2 ◎ σ ⊨ (a_all_x A)

| sat_ex_x  : forall M1 M2 σ A z α, (exists (o : obj), map σ α = Some o) ->
                               M1 ⦂ M2 ◎ (update_σ_map σ z (v_addr α)) ⊨ ([z /s 0] A) ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_all_x A)

(** Permission: *)
| sat_access1 : forall M1 M2 σ x y, (exists α, ⌊x⌋ σ ≜ α ->
                                     ⌊y⌋ σ ≜ α) ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_acc (a_bind x) (a_bind y))

| sat_access2 : forall M1 M2 σ x y, (forall α' o, ⌊x⌋ σ ≜ (α') ->
                                        map σ α' = Some o ->
                                        exists f α, (flds o) f = Some (v_addr α) /\
                                               ⌊y⌋ σ ≜ (α)) ->
                               M1 ⦂ M2 ◎ σ ⊨ (a_acc (a_bind x) (a_bind y))

| sat_access3 : forall M1 M2 σ ψ ϕ χ x y z α1 α2 s, ⌊x⌋ σ ≜ α1 ->
                                               ⌊this⌋ σ ≜ α1 ->
                                               ⌊y⌋ σ ≜ α2 ->
                                               ⌊z⌋ σ ≜ α2 ->
                                               σ = (χ, ϕ :: ψ) ->
                                               (contn ϕ) = c_stmt s ->
                                               in_stmt z s ->
                                               M1 ⦂ M2 ◎ σ ⊨ (a_acc (a_bind x) (a_bind y))

(** Viewpoint: *)
| sat_extrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ α ->
                                 map σ α = Some o ->
                                 o.(cname) = C ->
                                 M1 C = None ->
                                 M1 ⦂ M2 ◎ σ ⊨ a_extrn (a_bind x)

| sat_intrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ α ->
                                 map σ α = Some o ->
                                 o.(cname) = C ->
                                 (exists CDef, M1 C = Some CDef) ->
                                 M1 ⦂ M2 ◎ σ ⊨ a_intrn (a_bind x)

(** Control: *)
| sat_access : forall M1 M2 σ ϕ ψ x y m u vMap vMap' α, ⌊ x ⌋ σ ≜ α ->
                                                   ⌊ this ⌋ σ ≜ α ->
                                                   snd σ = ϕ :: ψ ->
                                                   (exists v u s,
                                                       ((contn ϕ) =
                                                        (c_stmt (s_stmts (s_meth v u m vMap') s))) /\
                                                       (forall v', ⌊ u ⌋ σ ≜ v' ->
                                                              ⌊ y ⌋ σ ≜ v') /\
                                                       (forall x' v1, vMap x' = Some v1 ->
                                                                 exists v2, (vMap' x' = Some v2 /\
                                                                        (forall v', ⌊ v1 ⌋ σ ≜ v' ->
                                                                               ⌊ v2 ⌋ σ ≜ v'))) /\
                                                       (forall x' v1, vMap' x' = Some v1 ->
                                                                 exists v2, vMap x' = Some v2)) ->
                                                   M1 ⦂ M2 ◎ σ ⊨ (a_call (a_bind x) (a_bind y) m vMap)

(** Space: *)
| sat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                M1 ⦂ M2 ◎ σ' ⊨ A ->
                                M1 ⦂ M2 ◎ σ ⊨ A

(** Time: *)

| sat_next : forall M1 M2 σ A ϕ ψ χ, σ = (χ, scons ϕ ψ) ->
                                (exists σ' σ'', (M1 ⦂ M2 ⦿ (χ, scons ϕ base) ⤳ σ') /\
                                           (σ ◁ σ' ≜ σ'') /\
                                           M1 ⦂ M2 ◎ σ'' ⊨ A) ->
                                M1 ⦂ M2 ◎ σ ⊨ (a_will A)

| sat_will : forall M1 M2 σ A ϕ ψ χ, σ = (χ, scons ϕ ψ) ->
                                (exists σ' σ'', (M1 ⦂ M2 ⦿ (χ, scons ϕ base) ⤳⋆ σ') /\
                                           (σ ◁ σ' ≜ σ'') /\
                                           M1 ⦂ M2 ◎ σ'' ⊨ A) ->
                                M1 ⦂ M2 ◎ σ ⊨ (a_will A)

where "M1 '⦂' M2 '◎' σ '⊨' A" := (sat M1 M2 σ A)

with
nsat : mdl -> mdl -> config -> asrt -> Prop :=
(*simple*)
| nsat_exp : forall M1 M2 σ e v, M1 ∙ σ ⊢ e ↪ v ->
                            v <> v_true ->
                            M1 ⦂ M2 ◎ σ ⊭ (a_exp e)

| nsat_class : forall M1 M2 σ e C C' α o, M1 ∙ σ ⊢ e ↪ (v_addr α) ->
                                     map σ α = Some o -> 
                                     o.(cname) = C' ->
                                     C <> C' ->
                                     M1 ⦂ M2 ◎ σ ⊭ (a_class e C)

| nsat_set   : forall M1 M2 σ e Σ As, ⌊ Σ ⌋ σ ≜′ As ->
                                 (forall α, M1 ∙ σ ⊢ e ↪ (v_addr α) -> ~ In α As) ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_set e (s_bind Σ))

(*connectives*)
| nsat_and1  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ (a_and A1 A2)
                                   
| nsat_and2  : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (a_and A1 A2)
                                   
| nsat_or    : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊭ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (a_or A1 A2)

| nsat_arr   : forall M1 M2 σ A1 A2, M1 ⦂ M2 ◎ σ ⊨ A1 ->
                                M1 ⦂ M2 ◎ σ ⊭ A2 ->
                                M1 ⦂ M2 ◎ σ ⊭ (a_arr A1 A2)
                                   
| nsat_not   : forall M1 M2 σ A, M1 ⦂ M2 ◎ σ ⊨ A ->
                            M1 ⦂ M2 ◎ σ ⊭ (a_neg A)

(*quantifiers*)
| nsat_all_x : forall M1 M2 σ A α, (exists y, map σ y = Some α) ->
                              M1 ⦂ M2 ◎ (fst σ, snd σ) ⊭ A ->
                              M1 ⦂ M2 ◎ σ ⊭ (a_all_x A) (*this is wrong: it needs to be for all addresses, and 
                                                      some mapping for z needs to be added to the config: σ[z ↦ α]*)

| nsat_ex_x : forall M1 M2 σ A, (forall y α, map σ y = Some α ->
                                   M1 ⦂ M2 ◎ σ ⊭ ([y /s 0] A)) ->
                           M1 ⦂ M2 ◎ σ ⊭ (a_ex_x A)

(** Permission: *)
| nsat_access : forall M1 M2 σ x y, (forall α1 α2, ⌊x⌋ σ ≜ α1 ->
                                         ⌊y⌋ σ ≜ α2 ->
                                         α1 <> α2) ->
                               (forall α1 α2 α3 f o, ⌊x⌋ σ ≜ α1 ->
                                                map σ α1 = Some o ->
                                                (flds o) f = Some (v_addr α2) ->
                                                ⌊y⌋ σ ≜ α3 ->
                                                α1 <> α2) ->
                               ((forall α1 α2, ⌊x⌋ σ ≜ α1 ->
                                          ⌊this⌋ σ ≜ α2 ->
                                          α1 <> α2) \/
                                (forall z α, ⌊y⌋ σ ≜ α ->
                                        ⌊z⌋ σ ≜ α ->
                                        forall ψ ϕ χ s, σ = (χ, scons ϕ ψ) ->
                                                   (contn ϕ) = c_stmt s ->
                                                   ~ in_stmt z s))->
                               M1 ⦂ M2 ◎ σ ⊭ (a_acc (a_bind x) (a_bind y))

(*viewpoint*) (* well-formeness? This is important!!!!*)
(*| nsat_extrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_extrn (bind x)

| nsat_extrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_extrn (bind x)*) 

| nsat_extrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ α ->
                                  map σ α = Some o ->
                                  o.(cname) = C ->
                                  (exists CDef, M1 C = Some CDef) ->
                                  M1 ⦂ M2 ◎ σ ⊭ a_extrn (a_bind x)

(*| nsat_intrn1 : forall M σ x, (forall α, ~ ⌊ x ⌋ σ ≜ α) ->
                         M en σ ⊭ a_intrn (bind x)

| nsat_intrn2 : forall M σ x α, ⌊ x ⌋ σ ≜ α ->
                           map σ α = None ->
                           M en σ ⊭ a_intrn (bind x)*) (*not needed. In the case where x or α are not defined, then we can't satisfy A*)

| nsat_intrn : forall M1 M2 σ x α o C, ⌊ x ⌋ σ ≜ α ->
                                  map σ α = Some o ->
                                  o.(cname) = C ->
                                  M1 C = None ->
                                  M1 ⦂ M2 ◎ σ ⊭ a_intrn (a_bind x)

(*space*)
| nsat_in    : forall M1 M2 σ A Σ σ', σ ↓ Σ ≜ σ' ->
                                 M1 ⦂ M2 ◎ σ' ⊭ A ->
                                 M1 ⦂ M2 ◎ σ ⊭ A

(*time*)

| nsat_next : forall M1 M2 σ A ϕ ψ χ, σ = (χ, scons ϕ ψ) ->
                                 (forall σ' σ'', (M1 ⦂ M2 ⦿ (χ, scons ϕ base) ⤳ σ') /\
                                            (σ ◁ σ' ≜ σ'') /\
                                            M1 ⦂ M2 ◎ σ'' ⊭ A) ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_will A)

| nsat_will : forall M1 M2 σ A ϕ ψ χ, σ = (χ, scons ϕ ψ) ->
                                 (forall σ' σ'', (M1 ⦂ M2 ⦿ (χ, scons ϕ base) ⤳⋆ σ') /\
                                            (σ ◁ σ' ≜ σ'') /\
                                            M1 ⦂ M2 ◎ σ'' ⊭ A) ->
                                 M1 ⦂ M2 ◎ σ ⊭ (a_will A)

where "M1 '⦂' M2 '◎' σ '⊭' A" := (nsat M1 M2 σ A).

Hint Constructors sat nsat.