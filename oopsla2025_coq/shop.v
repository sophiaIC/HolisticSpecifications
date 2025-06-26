Require Export Arith.
Require Import List.
Require Import Bool.
Require Import String.

Require Import CpdtTactics.
Require Import common.
Require Import language_def.
Require Import subst.
Require Import assert_theory.
Require Import hoare.
Require Import spec.

Require Export Coq.Numbers.BinNums.
Require Export ZArith.

(** 

Definition of the Shop Example

 *)

Module Shop.

  Import LanguageDefinition.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.
  Import SpecSatisfaction.

  Open Scope hoare_scope.

  (** Shop Example:

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


   ***)

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
    ⟦ acc ↦ t_cls Account ⟧
      ⟦ myItem ↦ t_cls Item ⟧
      ⟦ client ↦ t_ext ⟧ ∅.

  Definition AccountFlds :=
    ⟦ balance ↦ t_int ⟧
      ⟦ key ↦ t_cls Key ⟧ ∅.

  Definition ItemFlds :=
    ⟦ price ↦ t_int ⟧ ∅.

  Definition buy := mth_id 0.

  Definition buyer := v_prog 2.

  Definition item := v_prog 3.

  Definition itemPrice := v_prog 4.

  Definition oldBalance := v_prog 5.

  Definition thisAcc := v_prog 6.

  Definition tmp := v_prog 7.

  Definition pay := mth_id 1.

  Definition send := mth_id 2.

  Definition tell := mth_id 3.

  Definition a := v_spec 11.

  Definition b := v_spec 12.

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

  Definition buyDef := meth nil
                         public
                         ((buyer, t_ext)::
                            (item, t_cls Item) :: nil)
                         buyBody
                         t_bool.

  Parameter sendBody : stmt.

  Definition sendDef := meth ((a_ (e_typ (e_ a) (t_cls Account)) ∧
                                 (a_prt ((e_ a) ∙ key)),
                                a_prt ((e_ a) ∙ key),
                                a_prt ((e_ a) ∙ key)) ::
                                ((a_ (e_typ (e_ a) (t_cls Account))) ∧
                                   (a_prt_frm ((e_ a) ∙ key) (e_ buyer)),
                                  a_prt_frm ((e_ a) ∙ key) (e_ buyer),
                                  a_prt ((e_ a) ∙ key)) ::
                                (a_ (e_typ (e_ a) (t_cls Account)) ∧
                                   (a_ (e_typ (e_ b) t_int) ∧
                                      (a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b)((e_ a) ∙ balance))))),
                                  a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b)((e_ a) ∙ balance))),
                                  a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b)((e_ a) ∙ balance)))) ::
                                nil)
                          private
                          ((buyer, t_ext) ::
                             (item, t_cls Item) :: nil)
                          sendBody
                          t_bool.

  Definition ShopMths := ⟦ buy ↦ buyDef ⟧ ⟦ send ↦ sendDef ⟧ ∅.

  Definition ShopDef := clazz Shop
                              ShopFlds
                              empty
                              ShopMths.

  Definition to := v_prog 8.

  Definition k := v_prog 9.

  Definition amt := v_prog 10.

  Definition transfer := mth_id 4.

  Definition transferBody :=
    s_if (e_eq (e_fld (e_ this) key) (e_ k))
      (s_write this balance (e_minus (e_fld (e_ this) balance) (e_ amt)) ;; 
       (s_write to balance (e_plus (e_fld (e_ to) balance) (e_ amt))))
      (ret e_false);;
    ret e_false.

  Definition transferDef := meth nil
                              public
                              ((k, t_cls Key) ::
                                 (to, t_cls Account) ::
                                 (amt, t_int) :: nil)
                              transferBody
                              t_bool.

  Definition setKey := mth_id 5.

  Definition setKeyBody :=
    s_if (e_eq (e_fld (e_ this) key) e_null)
      (s_write this key (e_ k) ;;
       ret e_false)
      (ret e_false).

  Definition setKeyDef := meth nil
                            public
                            ((k, t_cls Key) :: nil)
                            setKeyBody
                            t_bool.

  Definition AccountMths := ⟦ transfer ↦ transferDef ⟧
                              ⟦ setKey ↦ setKeyDef ⟧ ∅.

  Definition AccountDef := clazz Account
                             AccountFlds
                             empty
                             AccountMths.

  Definition KeyDef := clazz Key
                             empty
                             empty
                             empty.

  Definition ItemDef := clazz Item
                          (⟦ price ↦ t_int ⟧ ∅)
                          empty
                          empty.

  (* Shop Specifications *)

  Definition S2 := S_inv ((a, t_cls Account)::nil) (a_prt (e_fld (e_ a) key)).

  Definition S3 := S_inv ((a, t_cls Account)::(b, t_int)::nil) (a_prt (e_fld (e_ a) key) ∧ a_ (e_lt (e_ b) (e_fld (e_ a) balance))). 

  Definition Mgood : module := (S_and S2 S3,
                                 ⟦ Shop ↦ ShopDef ⟧
                                   ⟦ Account ↦ AccountDef ⟧
                                   ⟦ Key ↦ KeyDef ⟧
                                   ⟦ Item ↦ ItemDef ⟧ ∅).

  (** Shop Assumptions  *)

  (* We assume the deconstruction of Mgood to its composite class definitions  *)
  Parameter destruct_Mgood :
    forall C CDef, ⟦ C ↦ CDef ⟧_∈ snd Mgood ->
              (C = Shop /\ CDef = ShopDef) \/
                (C = Account /\ CDef = AccountDef) \/
                (C = Key /\ CDef = KeyDef).

  (* We assume the deconstruction of the methods of shop to its composite method definitions  *)
  Parameter destruct_shopMths :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths ShopDef ->
              (m = buy /\ mDef = buyDef) \/
                (m = send /\ mDef = sendDef).

  (* We assume the deconstruction of the methods of account to its composite method definitions  *)
  Parameter destruct_accountMths :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths AccountDef ->
              (m = transfer /\ mDef = transferDef) \/
                (m = setKey /\ mDef = setKeyDef).

  (* We assume that the type system provides a proof that the key field in Account has type Key  *)
  Parameter keyHasTypeKey :
    forall x, Mgood ⊢ (a_ e_typ x (t_cls Account)) ⊆
           (a_ e_typ (e_fld x key) (t_cls Key)).

  (* We assume that the type system provides a proof that the balance field in Account has type int  *)
  Parameter balanceHasTypeInt :
    forall x, Mgood ⊢ (a_ e_typ x (t_cls Account)) ⊆
           (a_ e_typ (e_fld x balance) t_int).

  Lemma type_of_itemPrice :
    typeOf_f Mgood Item price = Some t_int.
  Proof.
    auto.
  Qed.

  Lemma type_of_shopAcc :
    typeOf_f Mgood Shop acc = Some (t_cls Account).
  Proof.
    auto.
  Qed.

  Lemma type_of_accountBalance :
    typeOf_f Mgood Account balance = Some t_int.
  Proof.
    auto.
  Qed.

  #[global] Hint Resolve type_of_itemPrice type_of_shopAcc type_of_accountBalance : shop_db.

  Ltac setup_shop :=
    assert (HitemPrice : ⟦ price ↦ t_int ⟧_∈ typeOf_f Mgood Item);
    [apply type_of_itemPrice|];
    assert (HaccountBalance : ⟦ balance ↦ t_int ⟧_∈ typeOf_f Mgood Account);
    [apply type_of_accountBalance|];
    assert (HshopAccount : ⟦ acc ↦ t_cls Account ⟧_∈ typeOf_f Mgood Shop);
    [apply type_of_shopAcc|].

End Shop.
