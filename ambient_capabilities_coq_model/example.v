Require Export Arith.
Require Import List.
Require Import Bool.
Require Import String.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert.
Require Export operational_semantics.
Require Import assert_theory.
Require Import hoare.
Require Import spec.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

Module Example.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.
  Import SpecSatisfaction.

  Open Scope hoare_scope.
  Open Scope assert_scope.

  (***

      class Shop{
            acc : Account
            myItem : Item
            client : external
            public method buy(buyer : external, anItem : Item)
                   int price = myItem.price
                   int oldBalance = this.acc.balance
                   buyer.pay(this.acc, price)
                   if this.acc.balance == oldBalance + price
                      buyer.send(myItem)
                      // this.send(buyer, myItem)
                   else
                      buyer.tell("pay me!!!!")
           private send(buyer : external, anItem : Item)
      }

      class Account {
            balance : int
            key : Key
            public method transfer(to : Account, k : Key, amt : int)
                   if this.key == k
                      this.balance -= amt
                      to.balance += amt
            public method set(k : Key)
                   if this.key == null
                      this.key = k
      }

      class Key {}

      class Item {
            price : int
      }

e ::=
e.f
x
bool
int
if e then e else e
e - e
e + e
e.g(e)
e : C


   ***)

  (*)Parameter s_minus (x y : var)(i : Z) : stmt.

  Parameter s_plus (x y : var)(i : Z) : stmt.*)

  (*Parameter plus_hoare (M : module)(x y : var)(i : Z) :=
   M ⊢ {} x*)

  Definition Shop := c_id 1.

  Definition Account := c_id 2.

  Definition Key := c_id 3.

  Definition Item := c_id 4.

  Definition acc := f_id 0.

  Definition myItem := f_id 1.

  Definition client := f_id 2.

  Definition balance := f_id 3.

  Definition key := f_id 4.

  Definition price := f_id 5.

  Definition ShopFlds :=
    ⟦ acc ↦ t_int ⟧
      ⟦ myItem ↦ t_cls Item ⟧
      ⟦ client ↦ t_ext ⟧ ∅.

  Definition AccountFlds :=
    ⟦ balance ↦ t_int ⟧
      ⟦ key ↦ t_cls Key ⟧ ∅.

  Definition ItemFlds :=
    ⟦ price ↦ t_int ⟧ ∅.

  Definition buy := mth_id 0.

  Definition buyer := v_id 2.

  Definition item := v_id 3.

  Definition itemPrice := v_id 4.

  Definition oldBalance := v_id 5.

  Definition thisAcc := v_id 6.

  Definition tmp := v_id 7.

  Definition pay := mth_id 1.

  Definition send := mth_id 2.

  Definition tell := mth_id 3.

  (*
    itemPrice = item.price
    thisAcc = this.acc
    oldBalance = thisAcc.balance
    tmp = buyer.pay(thisAcc, itemPrice)
    if this.acc.balance == oldBalance + itemPrice
       tmp = buyer.send(item)
    else
       tmp = buyer.buyFailed()
    return tmp
   *)

  Definition buyBody := (s_read itemPrice (e_fld (e_ item) price)) ;;
                        (s_read thisAcc (e_fld (e_ this) acc) ;;
                         (s_read oldBalance (e_fld (e_ thisAcc) balance) ;;
                          (s_call tmp buyer pay (thisAcc :: itemPrice :: nil) ;;
                           (s_if (e_eq
                                    (e_fld (e_fld (e_ this) acc) balance)
                                    (e_plus (e_ oldBalance) (e_ itemPrice)))
                              (s_call tmp this send (buyer :: item :: nil))
                              (s_call tmp buyer tell nil) ;;
                            ret (e_false))))).

  (* TODO: method specs on buy *)
  Definition buyDef := meth nil
                            ((buyer, t_ext)::
                               (item, t_cls Item) :: nil)
                            buyBody.

  Parameter sendBody : stmt.

  Definition sendDef := meth nil
                          ((buyer, t_ext) ::
                             (item, t_cls Item) :: nil)
                          sendBody.

  Definition ShopMths := ⟦ buy ↦ buyDef ⟧ ⟦ send ↦ sendDef ⟧ ∅.

  Definition ShopDef := clazz Shop
                              ShopFlds
                              empty
                              ShopMths.

  Definition to := v_id 8.

  Definition k := v_id 9.

  Definition amt := v_id 10.

  Definition transfer := mth_id 4.

  Definition transferBody :=
    s_if (e_eq (e_fld (e_ this) key) (e_ k))
      (s_write this balance (e_minus (e_fld (e_ this) balance) (e_ amt)))
      (s_write to balance (e_plus (e_fld (e_ to) balance) (e_ amt))) ;;
    ret e_false.

  Definition transferDef := meth nil
                              ((to, t_cls Account) ::
                                 (amt, t_int) :: nil)
                              transferBody.

  Definition setKey := mth_id 5.

  Definition setKeyBody :=
    s_if (e_eq (e_fld (e_ this) key) e_null)
      (s_write this key (e_ k) ;;
       ret e_false)
      (ret e_false).

  Definition setKeyDef := meth nil
                            ((k, t_cls Key) :: nil)
                            setKeyBody.

  Definition AccountMths := ⟦ transfer ↦ transferDef ⟧ ⟦ setKey ↦ setKeyDef ⟧ ∅.

  Definition AccountDef := clazz Account
                             AccountFlds
                             empty
                             AccountMths.

  Definition KeyDef := clazz Key
                             empty
                             empty
                             empty.

  (* Shop Specifications *)

  Definition a := v_id 11.

  Definition S1 := S_inv ((a, Account)::nil) (a_prt (e_fld (e_ a) key)).

  Definition Mgood : module := (S1,
                                 ⟦ Shop ↦ ShopDef ⟧
                                   ⟦ Account ↦ AccountDef ⟧
                                   ⟦ Key ↦ KeyDef ⟧ ∅).

  Lemma destruct_Mgood :
    forall C CDef, ⟦ C ↦ CDef ⟧_∈ snd Mgood ->
              (C = Shop /\ CDef = ShopDef) \/
                (C = Account /\ CDef = AccountDef) \/
                (C = Key /\ CDef = KeyDef).
  Proof.
  Admitted.

  Lemma destruct_shopMths :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths ShopDef ->
              (m = buy /\ mDef = buyDef) \/
                (m = send /\ mDef = sendDef).
  Proof.
  Admitted.

  Lemma post_true :
    forall M A s, M ⊢ ⦃ A ⦄ s ⦃ a_true ⦄.
  Proof.
  Admitted.

  Ltac apply_hq_sequ_with_mid_eq_fst :=
    match goal with
      [|- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄] => apply hq_sequ with (A2:=A)
    end.

  Ltac simpl_types :=
    unfold a_typs;
    unfold asrt_frm_list;
    simpl in *.

  Open Scope string_scope.

  Lemma entails_refl :
    forall M A, M ⊢ A ⊆ A.
  Proof.
  Admitted.

  #[global] Hint Resolve entails_refl : assert_db.

  Ltac hq_conj_post_conseq :=
    match goal with
      | [|- _ ⊢ ⦃ ?A1 ⦄ _ ⦃ ?A2 ∧ ?A3 ⦄ || ⦃ ?A ⦄ ] =>
          apply hq_conseq with (A4:=A1)(A5:=A2)(A6:=A)
    end.

  Lemma entails_assoc1 :
    forall M A1 A2 A3, M ⊢ ((A1 ∧ A2) ∧ A3) ⊆ (A1 ∧ (A2 ∧ A3)). Admitted.

  Lemma entails_assoc2 :
    forall M A1 A2 A3, M ⊢ (A1 ∧ (A2 ∧ A3)) ⊆ ((A1 ∧ A2) ∧ A3). Admitted.

  Lemma entails_trans :
    forall M A1 A2 A3, M ⊢ A1 ⊆ A2 ->
                  M ⊢ A2 ⊆ A3 ->
                  M ⊢ A1 ⊆ A3.
  Admitted.


  Ltac simpl_conj_entails :=
    repeat try (eapply entails_trans; [solve [apply entails_assoc1] |]);
    repeat try (eapply entails_trans; [|solve [apply entails_assoc2]]).

  Lemma hq_conj_assoc1 :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc2 :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Ltac simpl_conj :=
    repeat apply hq_conj_assoc1;
    repeat apply hq_conj_assoc2.

  Fixpoint contains {A : Type}`{Eq A}(l : list A)(a : A) :=
    match l with
    | nil => false
    | h :: t => eqb a h || contains t a
    end.

  Fixpoint remove (A : asrt)(removed : list asrt) :=
    match A with
    | a_exp _ => if  then
                  (a_true, A1 :: removed)
    end.

  Fixpoint conj_simplify A :=
    match A with
    | A1 \

  Lemma hq_pre_dup :
    forall M A1 A2 A3

  Lemma I1 :
    spec_sat Mgood S1.
  Proof.
    apply spec_invariant.
    intros.
    apply destruct_Mgood in H;
      destruct H.

    * (* Shop *)
      destruct H; subst.
      apply destruct_shopMths in H0;
        destruct H0.
      ** (* buy *)
        destruct H;
          subst.
        simpl.
        unfold buyBody.

        apply_hq_sequ_with_mid_eq_fst.
        *** (* itemPrice = item.price *)
          simpl_types.
          simpl_conj.
          hq_conj_post_conseq;
            eauto with assert_db.
          

        ***
          simpl_types.
          repeat apply hq_combine;
            try solve [apply hq_mid, post_true].

          ****
            admit.




  Qed.

End Example.
