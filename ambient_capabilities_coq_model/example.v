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
Require Import shop.
Require Import assumptions.

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

  Lemma destruct_accountMths :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths AccountDef ->
              (m = transfer /\ mDef = transferDef) \/
                (m = setKey /\ mDef = setKeyDef).
  Proof.
  Admitted.

(*)  Lemma destruct_keyMths :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths KeyDef ->
              mDef =
              (m = transfer /\ mDef = transferDef) \/
                (m = setKey /\ mDef = setKeyDef).
  Proof.
  Admitted.*)

  Lemma keyHasTypeKey :
    forall x, Mgood ⊢ (a_ e_typ x (t_cls Account)) ⊆
           (a_ e_typ (e_fld x key) (t_cls Key)).
  Proof.
  Admitted.

  Lemma balanceHasTypeInt :
    forall x, Mgood ⊢ (a_ e_typ x (t_cls Account)) ⊆
           (a_ e_typ (e_fld x balance) t_int).
  Proof.
  Admitted.

  Lemma apply_entails :
    forall M σ A1 A2, M ⊢ A1 ⊆ A2 ->
                 sat M σ A1 ->
                 sat M σ A2.
  Proof.
  Admitted.

   Lemma entails_fld_type :
    forall M C f T, typeOf_f M C f = Some T ->
               forall e, M ⊢ (a_ (e_typ e (t_cls C))) ⊆
                           (a_ (e_typ (e_fld e f) T)).
  Proof.

  Admitted.

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

  Ltac apply_hq_sequ_with_mid_eq_fst :=
    match goal with
    | [ H : typeOf_f ?M ?C ?f = Some ?T  |- ?M ⊢ ⦃ ?A ⦄ (s_read ?x (e_fld _ ?f)) ;; _ ⦃ _ ⦄ || ⦃ _ ⦄] => apply hq_sequ with (A2:=(a_ (e_typ (e_ x) T)) ∧ A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ ] => apply h_seq with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    end.

  Ltac simpl_types :=
    unfold a_typs;
    unfold asrt_frm_list;
    simpl in *.

  Open Scope string_scope.  Ltac asrt_sat_unfold_neg :=
    match goal with
    | [ H : sat ?M ?σ (¬ ?A)  |- _ ] =>
        inversion H; subst; clear H
    | [ H : nsat ?M ?σ (¬ ?A)  |- _ ] =>
        inversion H; subst; clear H
    | [ |- nsat ?M ?σ (¬ ?A) ] =>
        apply nsat_neg
    | [ |- sat ?M ?σ (¬ ?A) ] =>
        apply sat_neg
    end.

  Ltac asrt_sat_auto_destruct_conj :=
    match goal with
    | [H : sat ?M ?σ (?A1 ∧ ?A2) |- _] =>
        inversion H; subst; clear H
    | [H : nsat ?M ?σ (?A1 ∧ ?A2) |- _] =>
        inversion H; subst; clear H
    | [|- sat ?M ?σ (?A1 ∧ ?A2)] =>
        apply sat_and; auto
    | [H : nsat ?M ?σ ?A1 |- nsat ?M ?σ (?A1 ∧ ?A2)] =>
        apply nsat_and1; auto
    | [H : nsat ?M ?σ ?A2 |- nsat ?M ?σ (?A1 ∧ ?A2)] =>
        apply nsat_and2; auto
    end.

  Lemma sat_excluded_middle :
    forall M σ A, sat M σ (A ∨ ¬ A).
  Proof.
  Admitted.

  Lemma destruct_entails :
    forall M A1 A2, (forall σ, sat M σ A1 -> sat M σ A2) ->
               M ⊢ A1 ⊆ A2.
  Proof.
    apply entails_sound.
  Qed.

  Lemma sat_neg_is_not_sat :
    forall M σ A, sat M σ (¬ A) ->
             ~ sat M σ A.
  Proof.
    intros.
  Admitted.

  Lemma entails_excluded_middle :
    forall M A, M ⊢ a_true ⊆ (A ∨ ¬ A).
  Admitted.

  Lemma or_and_dist1 :
    forall M A1 A2 A, M ⊢ (A1 ∨ A2) ∧ A ⊆ (A1 ∧ A) ∨ (A2 ∧ A).
  Admitted.

  Lemma or_and_dist2 :
    forall M A1 A2 A, M ⊢ (A1 ∧ A) ∨ (A2 ∧ A) ⊆ (A1 ∨ A2) ∧ A.
  Admitted.

  Lemma entails_unfold :
    forall M A1 A2, M ⊢ A1 ⊆ A2 ->
               (forall σ, sat M σ A1 -> sat M σ A2).
  Proof.
    apply entails_sound.
  Qed.

  Ltac intros_entails :=
    intros;
    match goal with
    | [|- _ ⊢ _ ⊆ _ ] =>
        apply destruct_entails;
        intros
    | [H : ?M ⊢ ?A1 ⊆ ?A2 |- _] =>
        assert (forall σ, sat M σ A1 -> sat M σ A2);
        [apply (entails_unfold M A1 A2 H)|clear H]
    end.

  Lemma entails_refl :
    forall M A, M ⊢ A ⊆ A.
  Proof.
    intros_entails;
      auto.
  Qed.

  #[global] Hint Resolve entails_refl : assert_db.

  Lemma intro_ex_middle_hoare :
    forall M A A1 A2 s, M ⊢ ⦃ (A ∨ ¬ A) ∧ A1 ⦄ s ⦃ A2 ⦄ ->
                   M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄.
  Proof.
    intros.
    eapply h_strengthen;
      [eassumption|];
      intros_entails;
      asrt_sat_auto_destruct_conj;
      auto.
    apply sat_excluded_middle.
  Qed.

  Lemma split_excluded_middle_hoare :
    forall M A A1 A2 s, M ⊢ ⦃ (A ∧ A1) ∨ (¬ A ∧ A1) ⦄ s ⦃ A2 ⦄ ->
                   M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄.
  Proof.
    intros.
    apply intro_ex_middle_hoare with (A:=A).
    eapply h_strengthen;
      [|apply or_and_dist1];
      auto.
  Qed.

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

  Lemma hq_conj_assoc1_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc2_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc2_pre :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ (A1 ∧ A2) ∧ A3 ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ∧ (A2 ∧ A3) ⦄ s ⦃ A4 ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Lemma hq_conj_assoc1_post :
    forall M A1 A2 A3 A4 s A, M ⊢ ⦃ A1 ⦄ s ⦃ (A2 ∧ A3) ∧ A4 ⦄ || ⦃ A ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ∧ (A3 ∧ A4) ⦄ || ⦃ A ⦄.
  Proof.
  Admitted.

  Fixpoint contains {A : Type}`{Eq A}(l : list A)(a : A) :=
    match l with
    | nil => false
    | h :: t => eqb a h || contains t a
    end.
  Print asrt.

  Fixpoint and A1 A2 :=
    match A1 with
    | A ∧ A' => and A (and A' A2)
    | _ => A1 ∧ A2
    end.

  Fixpoint simplify_conj (A : asrt) : asrt :=
    match A with
    | (a_true) ∧ A' => (simplify_conj A')
    | A' ∧ (a_true) => (simplify_conj A')
    | A1 ∧ A2 => and (simplify_conj A1) (simplify_conj A2)
    | _ => A
    end.

  Compute and (a_true ∧ a_false) (a_ e_ this).
  Compute simplify_conj ((a_false ∧ a_true ∧ a_false) ∧ (a_ e_ this)).
  Compute simplify_conj (a_false ∧ a_ e_ this).

(*)  Fixpoint simplify_conj_helper
    (A : asrt)(removed : list asrt) : asrt * (list asrt) :=
    match A with
    | A1 ∧ A2 =>
        let res1 := simplify_conj_helper A1 removed in
        match fst res1 with
        | a_exp (e_val v_true) => simplify_conj_helper A2 removed
        | _ =>
            let res2 := simplify_conj_helper A2 (snd res1) in
            match fst res2 with
            | a_ e_true => res1
            | _ => (fst res1 ∧ fst res2, snd res2)
            end
        end
    | ¬ A' =>
        if contains removed A
        then (a_true, removed)
        else (¬ fst (simplify_conj_helper A' nil), A :: removed)
    | a_all C A' =>
        if contains removed A
        then (a_true, removed)
        else let res := simplify_conj_helper A' removed in
             (a_all C (fst res), A :: removed)
    | _ =>
        if contains removed A
        then (a_true, removed)
        else (A, A :: removed)
    end.

  Definition simplify_conj A := fst (simplify_conj_helper A nil).*)

  Fixpoint simplify_neg (A : asrt) : asrt :=
    match A with
    | ¬ ¬ A' => simplify_neg A'
    | A1 ∧ A2 => (simplify_neg A1) ∧ (simplify_neg A2)
    | a_all C A' => a_all C (simplify_neg A')
    | _  => A
    end.

  Compute (simplify_conj (a_ e_ k)).
  Compute simplify_neg (simplify_conj ((a_ e_ k) ∧
                                         ((a_prt (e_ k)) ∨
                                            (a_prt (e_ k))))).

  Lemma simplify_conj_entails1 :
    forall M A, M ⊢ A ⊆ (simplify_conj A).
  Proof.
  Admitted.

  Lemma simplify_conj_entails2 :
    forall M A, M ⊢ (simplify_conj A) ⊆ A.
  Proof.
  Admitted.

  Lemma rewrite_hoare_quad1 :
    forall M A A1, M ⊢ A1 ⊆ A ->
              forall A2 A3 s, M ⊢ ⦃ A ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.
  Proof.
  Admitted.

  Definition rewrite_hq_conj_simpl1 M A :=
    rewrite_hoare_quad1 M (simplify_conj A) A
      (simplify_conj_entails1 M A).

  Lemma rewrite_hoare_quad2 :
    forall M A A2, M ⊢ A ⊆ A2 ->
              forall A1 A3 s, M ⊢ ⦃ A1 ⦄ s ⦃ A ⦄ || ⦃ A3 ⦄ ->
                         M ⊢ ⦃ A1 ⦄ s ⦃ A2 ⦄ || ⦃ A3 ⦄.
  Proof.
  Admitted.

  Definition rewrite_hq_conj_simpl2 M A :=
    rewrite_hoare_quad2 M (simplify_conj A) A
      (simplify_conj_entails2 M A).


  Ltac simpl_conj_hq :=
    repeat apply hq_conj_assoc1_pre;
    repeat apply hq_conj_assoc2_post;
    apply rewrite_hq_conj_simpl1;
    apply rewrite_hq_conj_simpl2.



  Lemma conj_entails_left :
    forall M A1 A2, M ⊢ A1 ∧ A2 ⊆ A1.
  Proof.
    intros_entails;
      asrt_sat_auto_destruct_conj;
      auto.
  Qed.

  Lemma conj_entails_right :
    forall M A1 A2, M ⊢ A1 ∧ A2 ⊆ A2.
  Proof.
    intros_entails;
      asrt_sat_auto_destruct_conj;
      auto.
  Qed.

  Lemma entails_conj_split :
    forall M A A1 A2, M ⊢ A ⊆ A1 ->
                 M ⊢ A ⊆ A2 ->
                 M ⊢ A ⊆ A1 ∧ A2.
  Proof.
    repeat intros_entails.
    eauto with assert_db.
  Qed.

  Lemma sat_true :
    forall M σ, sat M σ (a_true).
  Proof.
    intros.
    apply sat_exp, eval_val.
  Qed.

  #[global] Hint Resolve sat_true : assert_db.

  Lemma entails_true :
    forall M A, M ⊢ A ⊆ a_true.
  Proof.
    repeat intros_entails.
    apply sat_true.
  Qed.

  Lemma conj_entails_dup :
    forall M A, M ⊢ A ⊆ (A ∧ A).
  Proof.
    intros; intros_entails;
      repeat asrt_sat_auto_destruct_conj.
  Qed.

  Lemma conj_strengthen_entails :
    forall M A1 A2 A, M ⊢ A1 ⊆ A2 ->
                 M ⊢ (A1 ∧ A) ⊆ A2.
  Proof.
  Admitted.

  Ltac split_post_condition_by_conjunction :=
    match goal with
    | [|- ?M ⊢ ⦃ ?A1 ⦄ ?s ⦃ ?A2 ∧ ?A3 ⦄ || ⦃ ?Ainv ⦄ ] =>
        apply hq_conseq with (A4:=A1 ∧ A1)(A5:=A2 ∧ A3)(A6:=Ainv);
        [apply hq_combine| apply conj_entails_dup with (A:=A1) | | ];
        try solve [apply entails_refl]
    end.

  Ltac by_hq_types2 :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ a_ (e_typ (e_ ?x) ?T) ⦄ || ⦃ ?A ⦄ ] =>
        apply hq_conseq with (A4:=a_ (e_typ (e_ x) T))(A5:=a_ (e_typ (e_ x) T))(A6:=A);
        [apply hq_types2| | |];
        try solve [apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ a_ (e_typ ?e ?T) ⦄ || ⦃ ?A ⦄ ] =>
        apply hq_conseq with (A4:=a_ (e_typ e T))(A5:=a_ (e_typ e T))(A6:=A);
        [apply hq_types2| | |];
        try solve [apply entails_refl]
    end.

  Ltac by_assumption :=
    match goal with
(*    |[|- _ ⊢ ?A ⊆ ?A ] =>
       apply entails_refl
    |[|- _ ⊢ _ ⊆ a_true ] =>
       apply entails_true*)
    |[|- _ ⊢ ?A ∧ _ ⊆ _ ] =>
       intros_entails; repeat asrt_sat_auto_destruct_conj; auto with assert_db
    end.

  Ltac has_spec S :=
    match S with
    | S2 => apply lspec_and1, lspec_base
    | S3 => apply lspec_and2, lspec_base
    end.

  Ltac by_call_ext_adapt_strong_using S :=
    try (eapply hq_conseq; [apply hq_call_ext_adapt_strong;
                           has_spec S| | | ];
         simpl;
         try solve [auto with assert_db; by_assumption]).

  (*Lemma entails_simplify :

  Lemma hq_pre_dup :
    forall M A1 A2 A3*)

  Lemma sat_cls_is_object :
    forall M σ e C, sat M σ (a_ e_typ e (t_cls C)) ->
               exists a, eval M σ e (v_addr a).
  Proof.
    intros.
    inversion H;
      subst.
    inversion H3;
      subst.
    eauto.
  Qed.

  Lemma entails_prt_int :
    forall M e1 e2 C, M ⊢ (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_int)) ⊆ (a_prt_frm e1 e2).
  Proof.
    intros_entails.
    asrt_sat_auto_destruct_conj.
    edestruct sat_cls_is_object;
      eauto.
    eapply sat_prt_frm_scalar;
      eauto.
  Qed.

  Lemma entails_prt_str :
    forall M e1 e2 C, M ⊢ (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_str)) ⊆ (a_prt_frm e1 e2).
  Proof.
    intros_entails.
    asrt_sat_auto_destruct_conj.
    edestruct sat_cls_is_object;
      eauto.
    eapply sat_prt_frm_scalar;
      eauto.
  Qed.

  Lemma entails_prt_bool :
    forall M e1 e2 C, M ⊢ (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_bool)) ⊆ (a_prt_frm e1 e2).
  Proof.
    intros_entails.
    asrt_sat_auto_destruct_conj.
    edestruct sat_cls_is_object;
      eauto.
    eapply sat_prt_frm_scalar;
      eauto.
  Qed.

(*  Lemma entails_prt_prog_var :
    forall M x y, M ⊢ (a_prt x) ⊆ (a_prt_frm x (e_ (v_prog y))).
  Proof.
  Admitted.*)

  Lemma entails_prt_intl :
    forall M x y C, M ⊢ ((a_ e_typ y (t_cls C)) ∧ ¬ a_extl y) ⊆ a_prt_frm x y.
  Proof.
  Admitted.

  Lemma entails_intl :
    forall M e C, C ∈ (snd M) ->
             M ⊢ (a_ (e_typ e (t_cls C))) ⊆ (¬ a_extl e).
  Admitted.
(*  
  Lemma entails_intl_not_extl :
    forall M e C, C ∈ (snd M) ->
             M ⊢ (a_ (e_typ e (t_cls C))) ⊆ ¬ a_extl e.
  Proof.
  Admitted.*)

  Ltac setup_shop :=
    assert (HitemPrice : ⟦ price ↦ t_int ⟧_∈ typeOf_f Mgood Item);
    [apply type_of_itemPrice|];
    assert (HaccountBalance : ⟦ balance ↦ t_int ⟧_∈ typeOf_f Mgood Account);
    [apply type_of_accountBalance|];
    assert (HshopAccount : ⟦ acc ↦ t_cls Account ⟧_∈ typeOf_f Mgood Shop);
    [apply type_of_shopAcc|].

  Lemma entails_different_type_neq :
    forall M e1 e2 T1 T2, T1 <> T2 ->
                     M ⊢ ((a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2)) ⊆
                       ¬ (a_ (e_eq e1 e2)).
  Proof.
    intros.
  Admitted.

  Lemma exp_neq_different_type :
    forall M e1 e2 T1 T2,
      T1 <> T2 ->
      M ⊢ (a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2) ⊆
                               (¬ a_ (e_eq e1 e2)).
  Proof.
  Admitted.

  Lemma exp_eq_same_type :
    forall M e1 e2 T,
      M ⊢ (a_ e_typ e1 T) ∧ (a_ e_eq e1 e2) ⊆ (a_ e_typ e2 T).
  Proof.
  Admitted.

  Ltac conseq_pre A :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A4:=A);
        [
        |
        |apply entails_refl
        |apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen with (P1:=A)
    end.

  Ltac econseq_pre :=
    match goal with
      | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |
        |apply entails_refl
        |apply entails_refl]
    | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄] =>
        eapply h_strengthen
    end.

  Ltac conseq_post A :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A5:=A);
        [
        |apply entails_refl
        |
        |apply entails_refl]
    end.

  Ltac econseq_post :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |apply entails_refl
        |
        |apply entails_refl]
    end.

  Ltac conseq_inv A :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq with (A6:=A);
        [
        |apply entails_refl
        |apply entails_refl
        |]
    end.

  Ltac econseq_inv :=
    match goal with
      [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
        eapply hq_conseq;
        [
        |apply entails_refl
        |apply entails_refl
        |]
    end.

  Ltac hq_conj_assoc_left_rewrite :=
    match goal with
    | [ |- _ ⊢ ⦃ ?A1 ∧ (?A2 ∧ ?A3) ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc2_pre
    end.

  Ltac hq_conj_assoc_right_rewrite :=
    match goal with
    | [ |- _ ⊢ ⦃ (?A1 ∧ ?A2) ∧ ?A3 ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc1_pre
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ (_ ∧ _) ∧ _ ⦄ || ⦃ _ ⦄ ] =>
        apply hq_conj_assoc2_post
    end.

  Ltac drop_right_of_conj :=
    repeat hq_conj_assoc_left_rewrite;
    econseq_pre;
    [|apply conj_entails_left];
    repeat hq_conj_assoc_right_rewrite.

  (* TODO: change S1 to S2 to match paper *)
  (* TODO: change entails to stand alone deifnition *)
  (* TODO: change from entails_prt_extl to entails_prt_prgm_var??? *)

  Parameter hoare_ul_assgn :
    forall M A x e, hoare_base M ([ e /s x ] A ) (s_read x e) A.

  Lemma return_false_prt_akey :
    Mgood
      ⊢ ⦃ (a_ e_typ (e_ result) t_bool
           ∧ (a_ e_typ (e_ a) (t_cls Account)
              ∧ a_prt ((e_ a) ∙ key))) ⦄
      ret e_false ⦃ a_prt ((e_ a) ∙ key) ∧
                      a_prt_frm (e_fld (e_ a) key) (e_ result) ⦄
    || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    split_post_condition_by_conjunction.

    *
      repeat hq_conj_assoc_left_rewrite.
      apply hq_mid.
      eapply h_prot1;
        simpl;
        auto;
        intros.

      match goal with
      | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄] =>
          apply h_strengthen
          with (P1:=[e_false /s result] A);
          [|try solve [intros_entails;
                       repeat asrt_sat_auto_destruct_conj;
                       auto]]
      end.
      apply h_embed_UL.
      apply hoare_ul_assgn.

    *
      match goal with
      | [|- ?M ⊢ ⦃ ?A1 ⦄ _ ⦃ a_prt_frm ?e ?x ⦄ || ⦃ ?A3 ⦄ ] =>
          eapply hq_conseq with
          (A4:=A1)
          (A5:=a_ (e_typ x t_bool) ∧ (a_ (e_typ e (t_cls Key))))
          (A6:=A3)
      end.

      **
        split_post_condition_by_conjunction.
        by_hq_types2;
          intros_entails;
          repeat asrt_sat_auto_destruct_conj;
          eauto.
        by_hq_types2;
          intros_entails;
          repeat asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply keyHasTypeKey|eauto].

      **
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.

      **
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [apply entails_prt_bool|asrt_sat_auto_destruct_conj; eauto].

      **
        apply entails_refl.
  Qed.

  Ltac return_false_protects_key :=
    eapply hq_conseq;
    [apply return_false_prt_akey| | | ];
    try solve [intros_entails;
               repeat asrt_sat_auto_destruct_conj;
               auto].

  Lemma entails_eq_trans :
    forall M e1 e2 e3, M ⊢ a_ (e_eq e1 e2) ∧ a_ (e_eq e2 e3) ⊆ a_ (e_eq e1 e3).
  Admitted.

  Lemma entails_eq_fld :
    forall M e1 e2 f, M ⊢ a_ (e_eq e1 e2) ⊆ a_ (e_eq (e1 ∙ f) (e2 ∙ f)).
  Admitted.

  Lemma entails_eq_not_prt_frm :
    forall M e1 e2, M ⊢ a_ (e1 ⩵ e2) ⊆ ¬ a_prt_frm e1 e2.
  Admitted.

  Lemma entails_prt_eq :
    forall M e1 e2, M ⊢ a_ (e_eq e1 e2) ∧ a_prt e1 ⊆ a_prt e2.
  Admitted.

  Lemma entails_prt_null :
    forall M, M ⊢ a_prt e_null ⊆ a_false.
  Admitted.

  Lemma hoare_false :
    forall M s A, M ⊢ ⦃ a_false ⦄ s ⦃ A ⦄.
  Admitted.

  Lemma neg_absurd :
    forall M A, M ⊢ A ∧ ¬ A ⊆ a_false.
  Admitted.

  Ltac solve_entails :=
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  Ltac unrelated_var_assgn_preserves_prt x e :=
          try (
              match goal with
              | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
                  apply hq_mid
              end);
          eapply h_strengthen;
          [apply h_prot1 with (A:=a_true);
           crush;
           match goal with
           | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄ ] =>
               apply h_strengthen with (P1:=A);
               [|]
           end;
           try solve [solve_entails];
           match goal with
           | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
               apply h_strengthen
               with (P1:=[e /s x] A);
               [|simpl; auto with assert_db]
           end;
           apply h_embed_UL;
           apply hoare_ul_assgn;
           intros_entails;
           repeat asrt_sat_auto_destruct_conj;
           auto with assert_db
          |try solve [solve_entails]].

  Ltac by_UL_hoare_unrelated_var_assgn x e :=
    try (
        match goal with
        | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
            apply hq_mid
        end);
    match goal with
    | [|- context [e_lt ?e1 ?e2] ] =>
        apply h_strengthen with (P1:=a_ e_lt e1 e2)
    end;
    try solve [solve_entails];
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen
        with (P1:=[e /s x] A);
        [|simpl; auto with assert_db]
    end;
    apply h_embed_UL;
    apply hoare_ul_assgn;
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  (*Lemma itemPriceAssgnPreserves_akey_prot :
    Mgood
      ⊢ ⦃ a_ e_typ (e_ result) t_bool
          ∧ (a_ e_typ (e_ this) (t_cls Shop)
             ∧ (a_ e_typ (e_ buyer) t_ext
                ∧ (a_ e_typ (e_ item) (t_cls Item)
                   ∧ (a_ e_typ (e_ a) (t_cls Account)
                      ∧ a_prt ((e_ a) ∙ key)))))
      ⦄ s_read itemPrice ((e_ item) ∙ price)
      ⦃ a_prt ((e_ a) ∙ key) ⦄ || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    (* itemPrice = item.price *)
    unrelated_var_assgn itemPrice (e_fld (e_ item) price).

  Qed.*)

  (*)Lemma.

  Proof.
    (* thisAcc = this.acc *)
  Qed.*)

  Lemma buyCallPreserves_akey_prot:
    Mgood
      ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int
          ∧ (a_ e_typ (e_ thisAcc) (t_cls Account)
             ∧ (a_ e_typ (e_ itemPrice) t_int
                ∧ (a_ e_typ (e_ result) t_bool
                   ∧ (a_ e_typ (e_ this) (t_cls Shop)
                      ∧ (a_ e_typ (e_ buyer) t_ext
                         ∧ (a_ e_typ (e_ item) (t_cls Item)
                            ∧ (a_ e_typ (e_ a) (t_cls Account)
                               ∧ (a_prt ((e_ a) ∙ key) ∧ a_prt_frm ((e_ a) ∙ key) (e_ buyer)))))))))
      ⦄ s_call tmp buyer pay (thisAcc :: itemPrice :: nil) ⦃ a_prt ((e_ a) ∙ key)
      ⦄ || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.

    (* tmp = buyer.pay(thisAcc, itemPrice) *)
    by_call_ext_adapt_strong_using S2.
    simpl_types;
    repeat apply entails_conj_split;
      try solve [by_assumption].

    ****
      by_assumption;
      eapply apply_entails;
        [apply entails_prt_intl|].
      repeat asrt_sat_auto_destruct_conj;
        eauto with assert_db.
      eapply apply_entails;
        [eapply entails_intl|];
        eauto.
      unfold Mgood;
        simpl;
        auto.
      eexists; crush.

    **** (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

  Qed.

(*  Lemma buyCallPreserves_akey_prt_frm_this :
    Mgood
    ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int
        ∧ (a_ e_typ (e_ thisAcc) (t_cls Account)
           ∧ (a_ e_typ (e_ itemPrice) t_int
              ∧ (a_ e_typ (e_ result) t_bool
                 ∧ (a_ e_typ (e_ this) (t_cls Shop)
                    ∧ (a_ e_typ (e_ buyer) t_ext
                       ∧ (a_ e_typ (e_ item) (t_cls Item)
                          ∧ (a_ e_typ (e_ a) (t_cls Account)
                             ∧ (a_prt ((e_ a) ∙ key)
                                ∧ (a_prt_frm ((e_ a) ∙ key) (e_ this)
                                   ∧ (a_prt_frm ((e_ a) ∙ key) (e_ buyer)
                                      ∧ a_prt_frm ((e_ a) ∙ key) (e_ item)))))))))))
    ⦄ s_call tmp buyer pay (thisAcc :: itemPrice :: nil) ⦃ a_prt_frm ((e_ a) ∙ key) (e_ this)
    ⦄ || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    
    (* tmp = buyer.pay(thisAcc, itemPrice) *)
    by_call_ext_adapt_strong_using S2.
    simpl_types.
    repeat apply entails_conj_split;
      try solve [by_assumption].

    ****
      by_assumption;
      eapply apply_entails;
        [apply entails_prt_intl|].
      repeat asrt_sat_auto_destruct_conj;
        eauto with assert_db.
      eapply apply_entails;
        [eapply entails_intl|];
        eauto.
      unfold Mgood;
        simpl;
        auto.
      eexists; crush.

    **** (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

    ****
      intros_entails.
      repeat asrt_sat_auto_destruct_conj;
        auto.
    
  Qed.*)


(*  Lemma buyCallPreserves_abalance :
    Mgood
      ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int ∧
            (a_ e_typ (e_ thisAcc) (t_cls Account) ∧
               (a_ e_typ (e_ itemPrice) t_int ∧
                  (a_ e_typ (e_ result) t_bool ∧
                     (a_ e_typ (e_ this) (t_cls Shop) ∧
                        (a_ e_typ (e_ buyer) t_ext ∧
                           (a_ e_typ (e_ item) (t_cls Item) ∧
                              (a_ e_typ (e_ a) (t_cls Account) ∧
                                 (a_ e_typ (e_ b) t_int ∧
                                    (a_prt ((e_ a) ∙ key) ∧
                                       a_ (e_lt
                                             (e_ b)
                                             ((e_ a) ∙ balance)))))))))))⦄
      s_call tmp buyer pay (thisAcc :: itemPrice :: nil)
      ⦃ a_ e_lt (e_ b) ((e_ a) ∙ balance) ⦄
    || ⦃ a_prt ((e_ a) ∙ key)
            ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance) ⦄.
  Proof.

    by_call_ext_adapt_strong_using S3.

    simpl_types.
    repeat apply entails_conj_split;
      try solve [by_assumption].

    ****
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_prog_var|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.

    ****
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_intl|].
      asrt_sat_auto_destruct_conj;
        eauto.
      eapply apply_entails;
        [apply entails_intl_not_extl|];
        eauto.
      unfold Mgood;
        simpl;
        auto.
      unfold update, t_update;
        simpl;
        crush.
      auto.
      eexists; eauto.

    **** (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

  Qed.*)

  Parameter hoare_UL_write_different_field :
    forall M x f y f' e z,
      f <> f' ->
      hoare_base M (a_ (e_eq (e_fld (e_ x) f) (e_ z)))
                 (s_write y f' e)
                 (a_ (e_eq (e_fld (e_ x) f) (e_ z))).

  Parameter hoare_UL_write_different_field_lt :
    forall M x f y f' e z,
      f <> f' ->
      hoare_base M (a_ (e_lt (e_ z) (e_fld (e_ x) f)))
        (s_write y f' e)
        (a_ (e_lt (e_ z) (e_fld (e_ x) f))).

  Parameter hoare_UL_write_different_object :
    forall M x f y f' e z,
      hoare_base M ((¬ (a_ (e_eq (e_ x) (e_ y)))) ∧
                      (a_ (e_eq (e_fld (e_ x) f) (e_ z))))
                 (s_write y f' e)
                 (a_ (e_eq (e_fld (e_ x) f) (e_ z))).

  Parameter hoare_UL_addition_lt :
    forall M x f y z f' i,
      hoare_base M (a_ (e_lt (e_ y) (e_fld (e_ x) f)))
        (s_write z f' (e_plus ((e_ z) ∙ f') i))
        (a_ (e_lt (e_ y) (e_fld (e_ x) f))).

  Ltac by_h_prot1_normal :=
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄ ] =>
        apply h_strengthen with (P1:=a_true ∧ A);
        [|solve_entails]
    end;
    apply h_prot1 with (A:=a_true);
    crush;
    match goal with
    | [|- _ ⊢ ⦃ _ ∧ ?A ⦄ _ ⦃ _ ⦄ ] =>
        apply h_strengthen with (P1:=A);
        [|]
    end;
    try solve [solve_entails].

  Ltac by_UL_hoare_write_unrelated_field :=
    match goal with
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ || ⦃ _ ⦄ ] =>
        apply hq_mid;
        apply h_strengthen with (P1:=A);
        try solve [intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto]
    |[ |- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ ] =>
       apply h_strengthen with (P1:=A);
       try solve [intros_entails;
                  repeat asrt_sat_auto_destruct_conj;
                  auto]
    end;
    by_h_prot1_normal;

    apply h_embed_UL;
    apply hoare_UL_write_different_field;
    intro Hcontra; inversion Hcontra.

  Ltac by_prt_frm_preserved_by_unrelated_var_assigment x z f :=
    apply hq_mid;
    eapply h_strengthen;
    [apply h_read_prt_frm with (y:=z); intros|];
    try solve [solve_entails];
    try solve [left; auto];
    try solve [right; eexists; auto];
    try (
        match goal with
        | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ _ ⦄ || ⦃ _ ⦄] =>
            apply hq_mid
        end);
    match goal with
    | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
        apply h_strengthen
        with (P1:=[(e_ z) ∙ f /s x] A);
        [|simpl; auto with assert_db]
    end;
    apply h_embed_UL;
    apply hoare_ul_assgn;
    intros_entails;
    repeat asrt_sat_auto_destruct_conj;
    auto with assert_db.

  Ltac by_prt_frm_preserved_by_unrelated_var_assgn :=
    match goal with
    | [|- _ ⊢ ⦃ _ ⦄ s_read ?x (e_fld (e_ ?y) ?f) ⦃ _ ⦄ || ⦃ _ ⦄] =>
        by_prt_frm_preserved_by_unrelated_var_assigment x y f
    end.

  Lemma Shop_sat_I2 :
    forall m mDef, ⟦ m ↦ mDef ⟧_∈ c_meths ShopDef ->
                   vis mDef = public ->
                   Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                                         (this, t_cls Shop) ::
                                         params mDef) ∧
                                 a_typs ((a, t_cls Account) :: nil)) ∧
                                a_prt ((e_ a) ∙ key)) ∧
                               adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
                     body mDef
                     ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
                   || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    setup_shop.
    intros.
    (* Shop *)
    apply destruct_shopMths in H;
      destruct H.
    * (* buy *)
      destruct H;
        subst.
      simpl.
      unfold buyBody.

      simpl_types.
      simpl_conj_hq.
      unfold simplify_conj;
        simpl.
      eapply hq_conseq with (A4:=a_ e_typ (e_ result) t_bool
                                 ∧ (a_ e_typ (e_ this) (t_cls Shop)
                                    ∧ (a_ e_typ (e_ buyer) t_ext
                                       ∧ (a_ e_typ (e_ item) (t_cls Item)
                                          ∧ (a_ e_typ (e_ a) (t_cls Account)
                                             ∧ (a_prt ((e_ a) ∙ key)
                                                ∧ (a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))));
        [| |apply entails_refl|apply entails_refl];
        try solve [solve_entails].
      repeat try apply_hq_sequ_with_mid_eq_fst;
        repeat split_post_condition_by_conjunction;
        try solve [by_hq_types2; by_assumption];

        try solve [apply hq_mid;
                   eapply h_strengthen;
                   [apply h_read_type|];
                   solve_entails;
                   eapply apply_entails;
                   [apply entails_fld_type; eauto|eauto]];

        (* <a.key> <-\- x is preserved by var assgn that is unrelated to the preservation *)
        try solve [by_prt_frm_preserved_by_unrelated_var_assgn].

      ** (* itemPrice = item.price *)
        unrelated_var_assgn_preserves_prt itemPrice (e_fld (e_ item) price).

      **
        unrelated_var_assgn_preserves_prt thisAcc (e_fld (e_ this) acc).

      ** (* oldBalance = thisAcc.balance *)
        unrelated_var_assgn_preserves_prt
          oldBalance
            (e_fld (e_ thisAcc) balance).

      ** (* tmp = buyer.pay(thisAcc, itemPrice) *)
        apply buyCallPreserves_akey_prot.

      **
        by_call_ext_adapt_strong_using S2;
          unfold prt_frms, asrt_frm_list; simpl;
          [|solve_entails].
        simpl_types.
        solve_entails.

        eapply apply_entails;
          [apply entails_prt_intl|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_intl; unfold update, t_update, Mgood; simpl; eexists|eauto].
        crush.

        eapply apply_entails;
          [apply entails_prt_int|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_fld_type|eauto].
        unfold typeOf_f, Mgood;
          simpl.
        eexists; eauto.

      **
        apply hq_if.

        *** (* internal call to this.send *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
              eapply hq_conseq with (A6:=A3);
              [| | |apply entails_refl]
          end;
          [eapply hq_call_int with
            (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                   a_prt ((e_ a) ∙ key))
            (A2:=a_prt ((e_ a) ∙ key))
            (A3:=a_prt ((e_ a) ∙ key))
            (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
          | |];

          [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
           try solve [apply in_eq];
           try solve [simpl; eauto];
           simpl
          | | | | | ];

          try solve [simpl; eauto];

          try solve [simpl_types; solve_entails].

        *** (* external call to buyer.tell *)
          by_call_ext_adapt_strong_using S2;
            try solve [by_assumption].
          simpl_types.
          repeat apply entails_conj_split;
            try solve [by_assumption].

      **
        apply hq_if.

        *** (* internal call to this.send *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
              eapply hq_conseq with (A6:=A3);
              [| | |apply entails_refl]
          end;
          [eapply hq_call_int with
            (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                   a_prt_frm ((e_ a) ∙ key) (e_ buyer))
            (A2:=a_prt_frm ((e_ a) ∙ key) (e_ buyer))
            (A3:=a_prt ((e_ a) ∙ key))
            (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
          | |];

          [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
           try solve [apply in_cons, in_eq];
           try solve [auto];
           try solve [simpl; eauto]
          | | | | | ];

          try solve [simpl; eauto];
          try solve [simpl_types; solve_entails].

        *** (* external call to buyer.tell *)
          by_call_ext_adapt_strong_using S2;
            try solve [by_assumption];
            simpl.
          simpl_types.
          repeat apply entails_conj_split;
            try solve [by_assumption].
          unfold prt_frms, asrt_frm_list; simpl.
          try solve [solve_entails].


      (*            match goal with
            | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
                eapply hq_conseq with (A6:=A3);
                [| | |apply entails_refl]
            end;
            [eapply hq_call_int with
              (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                     a_prt ((e_ a) ∙ key))
              (A2:=a_prt ((e_ a) ∙ key))
              (A3:=a_prt ((e_ a) ∙ key))
              (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
            | |];
            [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
             auto;
             [simpl; eauto|simpl; eauto| | |];
             try solve [auto]
            | | | | | ];
            try solve [simpl; eauto].

            simpl_types;
              solve_entails.

            simpl; auto with assert_db.

          **** (* external call to buyer.tell *)
            by_call_ext_adapt_strong_using S2;
              try solve [by_assumption].
            simpl_types.
            repeat apply entails_conj_split;
              try solve [by_assumption].*)

      **
        unrelated_var_assgn_preserves_prt result e_false.

      **
        return_false_protects_key.

    * (* send method: private method not considered *)
      destruct H;
        subst.
      simpl_types.
      crush.
  Qed.

  Parameter UL_post_true :
    forall M A s, hoare_base M A s (a_true).

  Lemma hoare_triple_post_true :
    forall M A s, M ⊢ ⦃ A ⦄ s ⦃ a_true ⦄.
  Proof.
    intros;
      apply h_embed_UL, UL_post_true.
  Qed.

  Lemma hoare_quad_post_true :
    forall M A1 A2 s, M ⊢ ⦃ A1 ⦄ s ⦃ a_true ⦄ || ⦃ A2 ⦄.
  Proof.
    intros; apply hq_mid, hoare_triple_post_true.
  Qed.

  Ltac hoare_post_true :=
    try solve [apply UL_post_true];
    try solve [apply hoare_triple_post_true];
    try solve [apply hoare_quad_post_true].

  Ltac by_prt_frm_bool :=
    match goal with
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ a_prt_frm (?o ∙ key) ?b ⦄ ] =>
        match goal with
        | |- context [e_typ b t_bool] =>
            conseq_post ((a_ (e_typ (o ∙ key) (t_cls Key))) ∧ (a_ (e_typ b t_bool)));
            [|solve [apply entails_prt_bool]];
            repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption];
            conseq_post (a_ (e_typ o (t_cls Account)));
            [|apply keyHasTypeKey];
            by_hq_types2; by_assumption
        end
    | [ |- _ ⊢ ⦃ _ ⦄ _ ⦃ a_prt_frm (?o ∙ key) ?b ⦄ || ⦃ _ ⦄ ] =>
        match goal with
        | |- context [e_typ b t_bool] =>
            conseq_post ((a_ (e_typ (o ∙ key) (t_cls Key))) ∧ (a_ (e_typ b t_bool)));
            [|solve [apply entails_prt_bool]];
            repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption];
            conseq_post (a_ (e_typ o (t_cls Account)));
            [|apply keyHasTypeKey];
            by_hq_types2; by_assumption
        end
    end.

(*  (a_ (e_typ e1 (t_cls C))) ∧ (a_ (e_typ e2 t_bool)) ⊆ (a_prt_frm e1 e2)*)

  Lemma Account_sat_I2 :
    forall m mDef,
      ⟦ m ↦ mDef ⟧_∈ c_meths AccountDef ->
      vis mDef = public ->
      Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                            (this, t_cls Account) ::
                            params mDef) ∧
                    a_typs ((a, t_cls Account) :: nil)) ∧
                   a_prt ((e_ a) ∙ key)) ∧
                  adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
        body mDef
        ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
      || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    intros.
    setup_shop.

    simpl_types.
    apply destruct_accountMths in H;
      repeat destruct H;
      subst;
      simpl;
      simpl_types;
      simpl_conj_hq.

    *
      (* Account::transfer *)
      unfold simplify_conj;
        simpl.
      unfold transferBody.
      repeat split_post_condition_by_conjunction.
 (*     drop_right_of_conj.
      drop_right_of_conj.
      apply_hq_sequ_with_mid_eq_fst.*)

      **
        conseq_pre (a_prt ((e_ a) ∙ key));

          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     eauto;
                     try solve [apply sat_true]].
        apply_hq_sequ_with_mid_eq_fst.

        ***
          apply hq_mid.
          by_h_prot1_normal.

          apply h_if.

          ****
            eapply h_strengthen;
              [|apply conj_entails_left].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [
                  apply h_embed_UL;
                  apply hoare_UL_write_different_field;
                  unfold key, balance;
                  crush].

          ****
            match goal with
            | [|- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ⦃ _ ⦄] =>
                apply h_strengthen
                with (P1:=[e_false /s result] A);
                [|try solve [intros_entails;
                             repeat asrt_sat_auto_destruct_conj;
                             auto]]
            end.
            apply h_embed_UL.
            apply hoare_ul_assgn.


        ***
          apply hq_mid.

          match goal with
          | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
              apply h_strengthen
              with (P1:=[e_false /s result] A);
              [|try solve [intros_entails;
                           repeat asrt_sat_auto_destruct_conj;
                           auto]]
          end.
          apply h_embed_UL.
          apply hoare_ul_assgn.

      **
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.

        apply_hq_sequ_with_mid_eq_fst.

        ***
          repeat split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption].

        ***
          by_prt_frm_bool.

    * (* setKey *)
      unfold simplify_conj;
        simpl.
      unfold setKeyBody.

      apply hq_if.

      ** (* true branch, i.e. this.key == null: this.key = k *)
        drop_right_of_conj.
        drop_right_of_conj.
        match goal with
        | [ |- _ ⊢ ⦃ ?A ∧ ?A1 ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
            apply hq_sequ with (A2:=A1)
        end;
        [|return_false_protects_key].
        repeat split_post_condition_by_conjunction;
          try solve [by_hq_types2; by_assumption].

        apply hq_mid.
        eapply h_strengthen with
          (P1:=(a_ (e_eq (e_fld (e_ this) key) e_null)) ∧
                 (a_prt (e_fld (e_ a) key)));
          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     auto].

        apply split_excluded_middle_hoare with
          (A:=a_ e_eq (e_ a) (e_ this)).
        apply h_or.

        *** (* a == this *)
          apply h_strengthen with (P1:=a_false);
            [apply hoare_false|].
          (* TODO: move hoare_false to hoare.v as a rule: h_absurd  *)
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [eapply entails_prt_null|].
        eapply apply_entails;
          [eapply entails_prt_eq|].
        asrt_sat_auto_destruct_conj; [|eassumption].
        eapply apply_entails;
          [eapply entails_eq_trans|].
        asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply entails_eq_fld|auto].

        *** (* a <> this  *)
          eapply h_strengthen with
            (P1:=(e_ a) ≠ (e_ this) ∧ (a_prt ((e_ a) ∙ key)));
            try solve [solve_entails].
        apply h_prot1;
          try solve [crush].
        intros.
        apply h_embed_UL.
        apply hoare_UL_write_different_object.

      **
      (* false branch, i.e. this.key != null: return false *)
      return_false_protects_key.
  Qed.

  Lemma Key_sat_I2 :
    forall m mDef,
      ⟦ m ↦ mDef ⟧_∈ c_meths KeyDef ->
      vis mDef = public ->
      Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                            (this, t_cls Key) ::
                            params mDef) ∧
                    a_typs ((a, t_cls Account) :: nil)) ∧
                   a_prt ((e_ a) ∙ key)) ∧
                  adapt (a_prt ((e_ a) ∙ key)) (this :: map fst (params mDef)) ⦄
        body mDef
        ⦃ a_prt ((e_ a) ∙ key) ∧ adapt (a_prt ((e_ a) ∙ key)) (result :: nil) ⦄
      || ⦃ a_prt ((e_ a) ∙ key) ⦄.
  Proof.
    intros;
      setup_shop.
    unfold KeyDef in *; simpl in *.
    match goal with
    | [ H : ⟦ _ ↦ _ ⟧_∈ (∅) |-_] =>
        inversion H
    end.
  Qed.

  Lemma I2 :
    spec_sat Mgood S2.
  Proof.
    setup_shop.
    apply spec_invariant.
    intros.
    apply destruct_Mgood in H;
      destruct H.

    *
      (* Shop *)
      destruct H; subst.
      eapply Shop_sat_I2;
        eauto.

    *
      (* Account \/ Key*)
      destruct H;
        destruct H;
        subst;
        simpl.

      **
        (* Account *)
        eapply Account_sat_I2;
          eauto.

      **
        (* Key *)
        eapply Key_sat_I2;
          eauto.
  Qed.

  Ltac split_post_condition_by_conjunction_and_solve :=
    repeat split_post_condition_by_conjunction;
    try solve [by_hq_types2; by_assumption];
    try solve [apply hq_mid;
               eapply h_strengthen;
               [apply h_read_type|];
               solve_entails;
               eapply apply_entails;
               [apply entails_fld_type; eauto|eauto]];
    try solve [by_prt_frm_preserved_by_unrelated_var_assgn].

  Ltac by_hoare_ul_assgn :=
    match goal with
    | [|- ?M ⊢ ⦃ ?A ⦄ s_read ?x ?e ⦃ ?A ⦄ ] =>
        assert (Hrewrite: A = [e /s x] A);
        [|assert ( M ⊢ ⦃ [e /s x] A ⦄ s_read x e ⦃ A ⦄);
          [auto|simpl; auto]];
        [|apply h_embed_UL, hoare_ul_assgn]
    | [|- _ ] => apply hq_mid; by_hoare_ul_assgn
    end.

  Ltac S3_by_unrelated_var_assgn_prt_and_lt x y f:=
    split_post_condition_by_conjunction_and_solve;
    [(* prt *)
      unrelated_var_assgn_preserves_prt x (e_fld (e_ y) f)
    |(* b <= a.balance *)
      drop_right_of_conj;
      repeat hq_conj_assoc_left_rewrite;
      econseq_pre;
      [
      |apply conj_entails_right]; (*;
      apply hq_mid, h_embed_UL;*)
      by_hoare_ul_assgn
    ];
    auto.

  Lemma buyCallPreserves_akey_prot_and_balance:
    Mgood
      ⊢ ⦃ a_ e_typ (e_ oldBalance) t_int
          ∧ (a_ e_typ (e_ thisAcc) (t_cls Account)
             ∧ (a_ e_typ (e_ itemPrice) t_int
                ∧ (a_ e_typ (e_ result) t_bool
                   ∧ (a_ e_typ (e_ this) (t_cls Shop)
                      ∧ (a_ e_typ (e_ buyer) t_ext
                         ∧ (a_ e_typ (e_ item) (t_cls Item)
                            ∧ (a_ e_typ (e_ a) (t_cls Account) ∧
                                 (a_ e_typ (e_ b) t_int ∧
                                    (a_prt ((e_ a) ∙ key) ∧ (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧ a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))))))) ⦄
      s_call tmp buyer pay (thisAcc :: itemPrice :: nil)
      ⦃ a_prt ((e_ a) ∙ key) ∧ (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)) ⦄
    || ⦃ a_prt ((e_ a) ∙ key) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)⦄.
  Proof.

    (* tmp = buyer.pay(thisAcc, itemPrice) *)
    by_call_ext_adapt_strong_using S3;
      simpl_types;
      repeat apply entails_conj_split;
      try solve [by_assumption].

    *
      by_assumption;
        eapply apply_entails;
        [apply entails_prt_intl|].
      repeat asrt_sat_auto_destruct_conj;
        eauto with assert_db.
      eapply apply_entails;
        [eapply entails_intl|];
        eauto.
      unfold Mgood;
        simpl;
        auto.
      eexists; crush.

    * (* a.key protected from itemPrice *)
      by_assumption.
      eapply apply_entails;
        [apply entails_prt_int|].
      repeat asrt_sat_auto_destruct_conj;
        auto with assert_db.
      eapply apply_entails;
        [apply keyHasTypeKey|].
      auto.

  Qed.

  Ltac apply_hq_sequ_preserving_left_of_pre :=
    repeat hq_conj_assoc_left_rewrite;
    match goal with
    | [ H : typeOf_f ?M ?C ?f = Some ?T  |- ?M ⊢ ⦃ ?A ⦄ (s_read ?x (e_fld _ ?f)) ;; _ ⦃ _ ⦄ || ⦃ _ ⦄] => apply hq_sequ with (A2:=(a_ (e_typ (e_ x) T)) ∧ A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ ] => apply h_seq with (A2:=A)
    | [ |- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] => apply hq_sequ with (A2:=A)
    end;
    repeat hq_conj_assoc_right_rewrite.

  Ltac extract_classDef :=
    match goal with
    |[def : classDef |- _ ] =>
       match goal with
       |[H : ⟦ _ ↦ def ⟧_∈ _ |- _] =>
          unfold update, t_update in H;
          simpl in H;
          inversion H;
          subst;
          clear H
       end
    end.

  Ltac setup_class :=
    simpl;
    intros;
    extract_classDef.

  Ltac setup_methods :=
  match goal with
  | [m : mth, mDef : methDef |- _] =>
      match goal with
      | [H : (m = _ ) /\ (mDef = _) \/ _ |- _ ] =>
          destruct H as [l |];
          [destruct l; subst|try setup_methods]
      | [H : (m = _ ) /\ (mDef = _) |- _ ] =>
          destruct H; subst
      end
  end.

  Ltac fetch_methods :=
    match goal with
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths ShopDef |- _ ] =>
        apply destruct_shopMths in H
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths AccountDef |- _ ] =>
        apply destruct_accountMths in H
    | [H : ⟦ _ ↦ _ ⟧_∈ c_meths KeyDef |- _ ] =>
        idtac
    end.

  Definition class_satisfies_invariant (M : module) C S : Prop :=
    match S with
    | S_inv Quantifications A => forall CDef m mDef,
        ⟦ C ↦ CDef ⟧_∈ snd M ->
        ⟦ m ↦ mDef ⟧_∈ c_meths CDef ->
        vis mDef = public ->
        Mgood ⊢ ⦃ ((a_typs ((result, rtrn mDef) ::
                              (this, t_cls C) ::
                              params mDef) ∧
                      a_typs (Quantifications)) ∧
                     A ∧ adapt A (this :: map fst (params mDef))) ⦄
          body mDef
          ⦃ A ∧ adapt A (result :: nil) ⦄
        || ⦃ A ⦄
    | _ => False
    end.

  Lemma Shop_sat_I3 :
    class_satisfies_invariant Mgood Shop S3.
  Proof.
    setup_shop.
    setup_class.
    (* Shop *)
    fetch_methods.
    setup_methods.
    * (* buy *)
      simpl.
      unfold buyBody.

      simpl_types.
      simpl_conj_hq.
      unfold simplify_conj;
        simpl.
      eapply hq_conseq with (A4:=a_ e_typ (e_ result) t_bool
                                 ∧ (a_ e_typ (e_ this) (t_cls Shop)
                                    ∧ (a_ e_typ (e_ buyer) t_ext
                                       ∧ (a_ e_typ (e_ item) (t_cls Item)
                                          ∧ (a_ e_typ (e_ a) (t_cls Account)
                                             ∧ (a_ e_typ (e_ b) t_int
                                                ∧ (a_prt ((e_ a) ∙ key) ∧
                                                     (a_ e_lt (e_ b) ((e_ a) ∙ balance)
                                                      ∧ (a_prt_frm ((e_ a) ∙ key) (e_ buyer))))))))));
        [| |apply entails_refl|apply entails_refl];
        try solve [solve_entails].

      (* Itemprice = item.price *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt itemPrice item price
        |].

      (* thisAcc = this.acc *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt thisAcc this acc
        |].

      (* oldBalance = thisAcc.balance *)
      apply_hq_sequ_with_mid_eq_fst;
        [S3_by_unrelated_var_assgn_prt_and_lt oldBalance thisAcc balance
        |].

      (* tmp = buyer.pay(thisAcc, itemPrice) *)
      apply_hq_sequ_with_mid_eq_fst;
        [split_post_condition_by_conjunction_and_solve;
         try solve [econseq_post;
                    [apply buyCallPreserves_akey_prot_and_balance
                     |by_assumption]]
        |].

      **
        (* prt_frm a.key buyer is preserved across external pay call  *)
        by_call_ext_adapt_strong_using S3;
          unfold prt_frms, asrt_frm_list; simpl;
          [|solve_entails].
        simpl_types.
        solve_entails.

        eapply apply_entails;
          [apply entails_prt_intl|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_intl; unfold update, t_update, Mgood; simpl; eexists|eauto].
        crush.

        eapply apply_entails;
          [apply entails_prt_int|].
        asrt_sat_auto_destruct_conj; eauto.
        eapply apply_entails;
          [apply entails_fld_type|eauto].
        unfold typeOf_f, Mgood;
          simpl.
        eexists; eauto.

        **
          apply_hq_sequ_preserving_left_of_pre.

          ***
            repeat split_post_condition_by_conjunction;
              try solve [by_hq_types2; by_assumption].

            **** (* prt a.key *)

              apply hq_if.

              ***** (* internal call to this.send *)
                econseq_inv;
                  [|apply conj_entails_left].
              match goal with
              | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
                  eapply hq_conseq with (A6:=A3);
                  [| | |apply entails_refl]
              end;
              [eapply hq_call_int with
                (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                       a_prt ((e_ a) ∙ key))
                (A2:=a_prt ((e_ a) ∙ key))
                (A3:=a_prt ((e_ a) ∙ key))
                (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
              | |];

              [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
               try solve [apply in_eq];
               try solve [simpl; eauto];
               simpl
              | | | | | ];

              try solve [simpl; eauto];

              try solve [simpl_types; solve_entails].

              ***** (* external call to buyer.tell *)
                by_call_ext_adapt_strong_using S3;
                  try solve [by_assumption];
                  simpl.
              simpl_types.
              repeat apply entails_conj_split;
                try solve [by_assumption].

            **** (* b < a.balance *)

              apply hq_if.

              *****(* internal call to this.send *)
                match goal with
                | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A2 ⦄ || ⦃ ?A3 ⦄ ] =>
                    eapply hq_conseq with (A6:=A3);
                    [| | |apply entails_refl]
                end;
              [eapply hq_call_int with
                (A1:=a_ e_typ (e_ a) (t_cls Account) ∧
                       (a_ e_typ (e_ b) t_int ∧
                          (a_prt ((e_ a) ∙ key) ∧
                             (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))))
                (A2:=a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))
                (A3:=a_prt ((e_ a) ∙ key) ∧ (a_ (e_lt (e_ b) ((e_ a) ∙ balance))))
                (C:=Shop)(xCs:=params sendDef)(T:=rtrn sendDef)
              | |];

              [eapply mspec with (mDef:=sendDef)(CDef:=ShopDef);
               try solve [simpl; auto];
               simpl
              | | | | | ];

              try solve [simpl; eauto];

              try solve [simpl_types; solve_entails].

              ***** (* external call to buyer.tell *)
                by_call_ext_adapt_strong_using S3;
                  try solve [by_assumption];
                  simpl.
              simpl_types.
              repeat apply entails_conj_split;
                try solve [by_assumption].

          ***
            repeat split_post_condition_by_conjunction;
              try solve [return_false_protects_key];
              try solve [by_UL_hoare_unrelated_var_assgn result (e_false)].

    * (* send *)
      crush. (* send is not a public method *)
  Qed.

  Lemma hoare_ul_write_to_different_object_lt :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_lt (e_ z) ((e_ x) ∙ f1) ⦄.
  Admitted.

  Lemma hoare_ul_write_to_different_object_eq :
    forall M x y z f1 f2 e,
      M ⊢ ⦃ (e_ x) ≠ (e_ y) ∧ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄
        s_write y f2 e
        ⦃ a_ e_eq (e_ z) ((e_ x) ∙ f1) ⦄.
  Admitted.

  Parameter hoare_ul_return_bool_preserves_fld_lt :
    forall M x y f, hoare_base M
                 ((a_ e_typ (e_ result) t_bool) ∧ a_ (e_lt (e_ x) ((e_ y) ∙ f)))
                 (ret e_false)
                 (a_ (e_lt (e_ x) ((e_ y) ∙ f))).

  Parameter hoare_ul_return_bool_preserves_fld_eq :
    forall M x y f, hoare_base M
                      ((a_ e_typ (e_ result) t_bool) ∧ a_ (e_eq ((e_ x) ∙ f) (e_ y)))
                      (ret e_false)
                      (a_ (e_eq ((e_ x) ∙ f) (e_ y))).

  Lemma Account_sat_I3 :
    class_satisfies_invariant Mgood Account S3.
  Proof.
    setup_shop.
    setup_class.
    fetch_methods.
    setup_methods.

    *
      (* Account::transfer *)
      simpl.
      unfold transferBody.
      simpl_types.
      conseq_post
        (a_prt ((e_ a) ∙ key) ∧
           (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧
              a_prt_frm ((e_ a) ∙ key) (e_ result)));
        try solve [unfold prt_frms, asrt_frm_list;
                   simpl;
                   intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto with assert_db].
      repeat split_post_condition_by_conjunction.
 (*     drop_right_of_conj.
      drop_right_of_conj.
      apply_hq_sequ_with_mid_eq_fst.*)
      (* TODO: clean up. too many subgoals created due to
               duplicates in post-condition
       *)

      **
        conseq_pre (a_prt ((e_ a) ∙ key));

          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     eauto;
                     try solve [apply sat_true]].
        apply_hq_sequ_with_mid_eq_fst.

        ***
          apply hq_mid.
          by_h_prot1_normal.

          apply h_if.

          ****
            eapply h_strengthen;
              [|apply conj_entails_left].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [
                  apply h_embed_UL;
                  apply hoare_UL_write_different_field;
                  unfold key, balance;
                  crush].

          ****
            match goal with
            | [|- _ ⊢ ⦃ ?A ∧ _ ⦄ _ ⦃ _ ⦄] =>
                apply h_strengthen
                with (P1:=[e_false /s result] A);
                [|try solve [intros_entails;
                             repeat asrt_sat_auto_destruct_conj;
                             auto]]
            end.
            apply h_embed_UL.
            apply hoare_ul_assgn.


        ***
          apply hq_mid.

          match goal with
          | [|- _ ⊢ ⦃ ?A ⦄ _ ⦃ _ ⦄] =>
              apply h_strengthen
              with (P1:=[e_false /s result] A);
              [|try solve [intros_entails;
                           repeat asrt_sat_auto_destruct_conj;
                           auto]]
          end.
          apply h_embed_UL.
          apply hoare_ul_assgn.

      **
        unfold prt_frms, asrt_frm_list;
          simpl.

        apply hq_sequ
          with (A2:=a_ e_typ (e_ result) t_bool ∧ a_ e_typ (e_ a) (t_cls Account) ∧ a_ e_lt (e_ b) ((e_ a) ∙ balance)).

        ***
          repeat split_post_condition_by_conjunction_and_solve.
          apply hq_if.

          ****
            apply hq_mid.
            apply split_excluded_middle_hoare
              with (A:=a_ ((e_ a) ⩵ (e_ this))).
            apply h_or.

            ***** (* a == this *)
              apply h_strengthen with (P1:=a_false);
                [apply hoare_false|].
            (* TODO: move hoare_false to hoare.v as a rule: h_absurd  *)
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.
            apply apply_entails with (A1:=a_prt_frm ((e_ a) ∙ key) (e_ k) ∧ ¬ (a_prt_frm ((e_ a) ∙ key) (e_ k)));
              [eapply neg_absurd|].
            asrt_sat_auto_destruct_conj.

            eapply apply_entails;
              [apply entails_eq_not_prt_frm|].

            eapply apply_entails;
              [eapply entails_eq_trans|].

            asrt_sat_auto_destruct_conj;
              eauto.

            eapply apply_entails;
              [apply entails_eq_fld|].

            auto.

            *****
              econseq_pre.
            eapply h_seq with (A2:=a_ e_lt (e_ b) ((e_ a) ∙ balance)).
            apply hoare_ul_write_to_different_object_lt.
            apply h_embed_UL.
            apply hoare_UL_addition_lt.
            intros_entails.
            repeat asrt_sat_auto_destruct_conj.

          ****
            econseq_pre.
            apply hq_mid, h_embed_UL.
            apply hoare_ul_return_bool_preserves_fld_lt.
            intros_entails.
            repeat asrt_sat_auto_destruct_conj.

        ***
          econseq_pre.
          apply hq_mid, h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_lt.
          intros_entails.
          repeat asrt_sat_auto_destruct_conj.

(*      ** (* a <> this  *)
          eapply h_strengthen with
            (P1:=(e_ a) ≠ (e_ this) ∧ (a_prt ((e_ a) ∙ key)));
            try solve [solve_entails].
          apply h_prot1;
            try solve [crush].
          intros.
          apply h_embed_UL.
          apply hoare_UL_write_different_object.

        *** (* a ≠ this *)*)

      **
        simpl_types.
        repeat hq_conj_assoc_right_rewrite.
        unfold prt_frms, asrt_frm_list;
          simpl.
        econseq_pre;
          [|apply conj_entails_right].
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.
        drop_right_of_conj.

        repeat split_post_condition_by_conjunction_and_solve;
          try solve [hoare_post_true].

        apply_hq_sequ_with_mid_eq_fst.

        repeat split_post_condition_by_conjunction_and_solve.

        ***
          hoare_post_true.

        ***
          repeat hq_conj_assoc_left_rewrite.
          apply hq_mid.
          apply h_prot1;
            try solve[simpl; auto];
            intros.

          apply h_if.

          ****
            apply h_strengthen with (P1:=a_ (((e_ a) ∙ key) ⩵ (e_ z)));
              try solve [intros_entails;
                         repeat asrt_sat_auto_destruct_conj;
                         auto].
            apply_hq_sequ_with_mid_eq_fst;
              try solve [apply h_embed_UL;
                         apply hoare_UL_write_different_field;
                         intro Hcontra; inversion Hcontra].

          ****
            eapply h_strengthen.
            apply h_embed_UL.
            apply hoare_ul_return_bool_preserves_fld_eq.
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.

        ***
          by_prt_frm_bool.

    * (* setKey *)
      simpl_types.
      conseq_post
        (a_prt ((e_ a) ∙ key) ∧
           (a_ e_lt (e_ b) ((e_ a) ∙ balance) ∧
              a_prt_frm ((e_ a) ∙ key) (e_ result)));
        try solve [unfold prt_frms, asrt_frm_list;
                   simpl;
                   intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   auto with assert_db].
      unfold setKeyBody.

      apply hq_if.

      ** (* true branch, i.e. this.key == null: this.key = k *)

        drop_right_of_conj.
        drop_right_of_conj.
        (*match goal with
        | [ |- _ ⊢ ⦃ ?A ∧ ?A1 ⦄ _ ;; _ ⦃ _ ⦄ || ⦃ _ ⦄ ] =>
            apply hq_sequ with (A2:=A1)
        end;
        [|return_false_protects_key].

        admit.

        by_assumption.

        intros_entails.
        asrt_sat_auto_destruct_conj.
        by_assumption.

        try solve [intros_entails].*)

        repeat split_post_condition_by_conjunction;
          try solve [by_prt_frm_bool].

        apply hq_mid.
        eapply h_strengthen with
          (P1:=(a_ e_typ (e_ result) t_bool) ∧ (a_ (e_eq (e_fld (e_ this) key) e_null)) ∧
                 (a_prt (e_fld (e_ a) key)));
          try solve [intros_entails;
                     repeat asrt_sat_auto_destruct_conj;
                     auto].

        apply split_excluded_middle_hoare with
          (A:=a_ e_eq (e_ a) (e_ this)).
        apply h_or.

        *** (* a == this *)
          apply h_strengthen with (P1:=a_false);
            [apply hoare_false|].
          (* TODO: move hoare_false to hoare.v as a rule: h_absurd  *)
        intros_entails;
          repeat asrt_sat_auto_destruct_conj.
        eapply apply_entails;
          [eapply entails_prt_null|].
        eapply apply_entails;
          [eapply entails_prt_eq|].
        asrt_sat_auto_destruct_conj; [|eassumption].
        eapply apply_entails;
          [eapply entails_eq_trans|].
        asrt_sat_auto_destruct_conj;
          eauto.
        eapply apply_entails;
          [apply entails_eq_fld|auto].

        *** (* a <> this  *)
          eapply h_strengthen with
            (P1:= (a_ e_typ (e_ result) t_bool) ∧ (e_ a) ≠ (e_ this) ∧ (a_prt ((e_ a) ∙ key)));
            try solve [solve_entails].
        apply h_prot1;
          try solve [crush].
        intros.
        apply h_seq with (A2:=(a_ e_typ (e_ result) t_bool) ∧ a_ (((e_ a) ∙ key) ⩵ (e_ z))).
        (*split_post_condition_by_conjunction.
        apply h_embed_UL.
        apply hoare_UL_write_different_object.*)
        ****
          match goal with
          | [ |- _ ⊢ ⦃ ?A1 ⦄ _ ⦃ ?A2 ∧ ?A3 ⦄] =>
              conseq_pre (A1 ∧ A1)
          end;
          [|intros_entails; repeat asrt_sat_auto_destruct_conj].
          apply h_and.

          *****
            econseq_pre.
          apply h_types1.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj;
            auto.

          *****
            econseq_pre.
          apply h_embed_UL.
          apply hoare_UL_write_different_object.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj.

        ****
          apply h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_eq.

        *** (* this.key == null -> contradiction on prt null *)
          match goal with
          | [|- _ ⊢ ⦃ _ ⦄ _ ⦃ ?A ⦄ || ⦃ _ ⦄] =>
              apply hq_sequ with (A2:=(a_ e_typ (e_ result) t_bool) ∧ A)
          end.
          split_post_condition_by_conjunction;
            try solve [by_hq_types2; by_assumption].
          econseq_pre.
          apply hq_mid, h_embed_UL.
          apply hoare_UL_write_different_field_lt.
          intro Hcontra; inversion Hcontra.
          intros_entails;
            repeat asrt_sat_auto_destruct_conj;
            auto.

          apply hq_mid, h_embed_UL.
          apply hoare_ul_return_bool_preserves_fld_lt.

      **
      (* false branch, i.e. this.key != null: return false *)
        repeat split_post_condition_by_conjunction;
          try solve [return_false_protects_key].
        econseq_pre.
        apply hq_mid, h_embed_UL.
        apply hoare_ul_return_bool_preserves_fld_lt.
        intros_entails.
        repeat asrt_sat_auto_destruct_conj.

  Qed.

  Lemma Key_sat_I3 :
    class_satisfies_invariant Mgood Key S3.
  Proof.
    setup_class.
    unfold KeyDef in *; simpl in *.
    match goal with
    | [ H : ⟦ _ ↦ _ ⟧_∈ (∅) |-_] =>
        inversion H
    end.
  Qed.

  Lemma I3 :
    spec_sat Mgood S3.
  Proof.
    setup_shop.
    apply spec_invariant.
    intros.
    apply destruct_Mgood in H;
      destruct H.

    *
      (* Shop *)
      destruct H; subst.
      eapply Shop_sat_I3;
        eauto; auto.

    *
      (* Account \/ Key*)
      destruct H;
        destruct H;
        subst;
        simpl.

      **
        (* Account *)
        eapply Account_sat_I3;
          eauto.
        auto.

      **
        (* Key *)
        eapply Key_sat_I3;
          eauto.
        auto.
  Qed.

End Example.
