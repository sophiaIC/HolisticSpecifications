Require Import common.
Require Import loo_def.
Require Import chainmail.
Require Import List.
Require Import CpdtTactics.

(** #<h1># Basic Arithmetic Assertions: #</h1># *)

(** Class Names : 0 -> 49*)
(** Field Names : 50 -> 99*)
(** Ghost Field Names : 100 -> 149*)
(** Method Names : 100 -> 199*)
(** Variables : 200 -> 249*)
(** Heap Locations : 250 -> 399*)

(** #<h3># Class Identifiers: #</h3># *)
Definition Zero := 0.

Definition True_ := 1.

Definition False_ := 2.

Definition String_ := 3.

Definition Client := 4.

(** #<h3># Field Identifiers:#</h3>#  *)

Definition isEven := 50.

(** #<h3># Ghost Field Identifiers:#</h3>#  *)

Definition isEvenG := 100.

(** #<h3># Ghost Field Identifiers:#</h3>#  *)

Definition TrueLoc := 250.

Definition FalseLoc := 251.

Definition ZeroLoc := 252.

Definition StringLoc := 253.

Definition ClientLoc := 254.

(** #<h3># Variable Identifiers:#</h3>#  *)

Definition z := 200.

Definition z_ := r_var z.

Definition t := 201.

Definition t_ := r_var t.

Definition f := 202.

Definition f_ := r_var f.

Definition s := 203.

Definition s_ := r_var s.

Definition client := 204.

Definition client_ := r_var client.

(** #<h3># Class Definitions:#</h3># *)

Definition TrueDef := clazz True_ nil empty empty.

Definition FalseDef := clazz False_ nil empty empty.

Definition ZeroDef := clazz Zero
                            (isEven::nil)
                            empty
                            (update
                               isEvenG (e_acc_f (e_var (bind this)) isEven)
                               empty).

Definition StringDef := clazz String_ nil empty empty.

Definition ClientDef := clazz Client nil empty empty.

(** #<h3># Module Definitions:#</h3>#  *)

Definition ArithMdl := (update False_ FalseDef
                               (update True_ TrueDef
                                       (update Zero ZeroDef
                                               empty))).

Definition StringMdl := (update String_ StringDef empty).

Definition ClientMdl := (update Client ClientDef empty).

(** #<h3># Object Definitions:#</h3>#  *)

Definition TrueObj := new True_ empty empty.

Definition FalseObj := new False_ empty empty.

Definition ZeroObj := new Zero (update isEven TrueLoc empty) empty.

Definition StringObj := new String_ empty empty.

Definition ClientObj := new Client empty empty.

(** #<h3># Configuration Definitions:#</h3>#  *)

Definition myχ : heap := (update
                            StringLoc StringObj
                            (update ZeroLoc ZeroObj
                                    (update FalseLoc FalseObj
                                            (update TrueLoc TrueObj
                                                    (update
                                                       ClientLoc ClientObj
                                                       empty))))).

Definition myMap : state := (update
                               s StringLoc
                               (update
                                  f FalseLoc
                                  (update
                                     t TrueLoc
                                     (update z ZeroLoc
                                             (update
                                                client ClientLoc
                                                (update
                                                   this ClientLoc
                                                   empty)))))).

Definition myϕ : frame := frm myMap (c_stmt (s_rtrn z)).

Definition myψ : stack := scons myϕ base.

Definition myσ : config := (myχ, myψ).

(** ArithMdl ⦂ M ◎ myσ ⊨ true *)
Theorem ArithMdlSatisfiesTrue :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_exp (e_true)).
Proof.
  intros.
  apply sat_exp.
  apply v_true.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ t:True_ *)
Theorem ArithMdlSatisfiesClass :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_class (e_var (bind t)) True_).
Proof.
  intros.
  apply sat_class with (α:=TrueLoc)(o:=TrueObj); auto.
  apply v_var; auto.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ internal⟨t⟩, where t is the variable in σ pointing to TrueObj *)
Theorem ArithMdlSatisfiesInternal :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_intrn (bind t)).
Proof.
  intros.
  apply sat_intrn with (α:=TrueLoc)(o:=TrueObj)(C:=True_);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
  exists TrueDef; auto.
Qed.

(** ArithMdl ⦂ M ◎ myσ ⊨ external⟨s⟩, where s is the variable in σ pointing to StringObj *)
Theorem ArithMdlSatisfiesExternal :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_extrn (bind s)).
Proof.
  intros.
  apply sat_extrn with (α:=StringLoc)(o:=StringObj)(C:=String_);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
Qed.

(** The following is an example of undefined satisfaction: *)
(** external⟨x⟩ can be neither satisfied nor ~satisfied in the case *)
(** that x is not included in the heap. *)
Theorem externalIfNotInternal :
  forall M1 M2 σ x,
    M1 ⦂ M2 ◎ σ ⊭ (a_intrn x) ->
    M1 ⦂ M2 ◎ σ ⊨ (a_extrn x).
Proof.
  intros.
  inversion H; subst.
  apply sat_extrn with (α:=α)(o:=o)(C:=cname o);
    auto.
Abort.

Theorem ClientExternalToArithMdl :
  forall M, ArithMdl ⦂ M ◎ myσ ⊨ (a_extrn (bind client)).
Proof.
  intros.
  apply sat_extrn with (α:=ClientLoc)(o:=ClientObj)(C:=Client);
    auto.
  apply int_x with (ψ:=myψ)(ϕ:=myϕ);
    auto.
Qed.

Theorem ArithMdlSatisfiesAccess :
  forall M, ArithMdl ⦂ M ◎ myσ ⊭ (a_acc (bind client) (bind t)).
Proof.
  intros.
  apply nsat_access; intros.
  
  (** case 1: client and t do not point to the same object in the heap *)
  inversion H; subst;
    inversion H0; subst;
      simpl in *;
      inversion H4; subst;
        inversion H2; subst;
          intro Hcontra; subst;
            simpl in *;
            rewrite <- H3 in H5;
            unfold myMap, update, t_update in H5; simpl in H5;
              inversion H5.

  (** case 2: client does not have a field that has access to t *)
  inversion H; subst; simpl in *.
  inversion H4; subst; simpl in *.
  inversion H5; subst.
  unfold common.map, configMapHeap in H0; simpl in *.
  unfold myχ, update, t_update in H0; simpl in *.
  inversion H0; subst.
  simpl in H1.
  inversion H1.

  (** case 3: client is either not the current object (it is), or t is not in the current continuation*)
  right; intros.
  inversion H; inversion H0; subst; simpl in *.
  inversion H4; inversion H10; subst; simpl in *.
  assert (Heq : z0 = z \/ z0 = client \/ z0 = s \/ z0 = t \/ z0 = f \/ z0 = this).
  
Abort.

(*Definition Int := 1.

Definition pred := 50.

Definition incBody := s_stmts (s_new x Int (update pred this empty)) (s_rtrn x).

Definition inc := 500.

Definition IntegerDef := clazz Int (pred::nil) (update inc incBody empty) empty.

Definition Dispenser := 2.

Definition count := 101.



s_asgn x_ 

Definition pressBody := s_stmts (s_stmts this count ) (s_rtrn x)

Definition DispenserDef := clazz Dispenser (count::nil) empty empty.
*)