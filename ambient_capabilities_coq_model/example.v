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

Module Example.

  Import LanguageDefinition.
  Import OperationalSemantics.
  Import Assert.
  Import SubstDefn.
  Import AssertTheory.
  Import Hoare.

  Declare Scope hoare_scope.
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

  Parameter s_minus (x y : var)(i : Z) : stmt.

  Parameter s_plus (x y : var)(i : Z) : stmt.

  Parameter plus_hoare (M : module)(x y : var)(i : Z) :
   M ⊢ {} x

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
                        ((s_read thisAcc (e_fld (e_ this) acc)) ;;
                         ((s_read oldBalance (e_fld (e_ thisAcc) balance)) ;;
                          ((s_call tmp buyer pay (thisAcc :: itemPrice :: nil)) ;;
                           ((s_if (e_eq
                                     (e_fld (e_fld (e_ this) acc) balance)
                                     (e_plus (e_ oldBalance) (e_ itemPrice)))
                               (s_call tmp this send (buyer :: item :: nil))
                               (s_call tmp buyer tell nil)) ;;
                            (s_stmt (s_ret (v_ (v_int 0)))))))).

  (* TODO: method specs on buy *)
  Definition buyDef := meth nil
                            ((buyer, t_ext)::
                               (item, t_cls Item) :: nil)
                            buyBody.

  Parameter sendBody : stmts.

  Definition ShopMths := ⟦ buy ↦ buyDef ⟧ ∅.

  Definition to := v_id 8.

  Definition k := v_id 9.

  Definition amt := v_id 10.

  Definition transfer := mth_id 4.

  Definition tranferBody :=
    (s_if (e_eq (e_fld (e_ this) key) (e_ k))
       (s_write this balance (e_minus (e_fld (e_ this) balance) (e_ amt)) ;;
        (s_stmt (s_write to balance (e_plus (e_fld (e_ to) balance) (e_ amt)))))
       (s_ret (v_ (v_int 0)))) ;;
    (s_stmt (s_ret (v_ (v_int 0)))).

End Example.
