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
    ⟦ acc ↦ t_cls Account ⟧
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
                            buyBody
                            t_bool.

  Parameter sendBody : stmt.

  Definition sendDef := meth nil
                          ((buyer, t_ext) ::
                             (item, t_cls Item) :: nil)
                          sendBody
                          t_bool.

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
      (s_write this balance (e_minus (e_fld (e_ this) balance) (e_ amt)) ;; 
       (s_write to balance (e_plus (e_fld (e_ to) balance) (e_ amt))))
      (ret e_false);;
    ret e_false.

  Definition transferDef := meth nil
                              ((to, t_cls Account) ::
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

  Definition a := v_id 11.

  Definition S1 := S_inv ((a, Account)::nil) (a_prt (e_fld (e_ a) key)).

  Definition Mgood : module := (S1,
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
    forall x, Mgood ⊢ (a_ e_typ x (t_cls Account)) ⊆ (a_ e_typ (e_fld x key) (t_cls Key)).
  Proof.
  Admitted.

  Lemma post_true :
    forall M A s, M ⊢ ⦃ A ⦄ s ⦃ a_true ⦄.
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
               forall e, M ⊢ (a_ (e_typ e (t_cls C))) ⊆ (a_ (e_typ (e_fld e f) T)).
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
    forall M σ A, sat M σ A \/ nsat M σ A.
  Proof.
  Admitted.

  Lemma destruct_entails :
    forall M A1 A2, (forall σ, sat M σ A1 -> sat M σ A2) ->
               M ⊢ A1 ⊆ A2.
  Proof.
    intros.
    unfold entails, arr, a_or; intros;
      asrt_sat_unfold_neg.
    specialize (H σ).
    destruct (sat_excluded_middle M σ A1);
      [apply nsat_and2|apply nsat_and1];
      repeat asrt_sat_unfold_neg;
      auto.
  Qed.

  Lemma sat_neg_is_not_sat :
    forall M σ A, sat M σ (¬ A) ->
             ~ sat M σ A.
  Proof.
    intros.
  Admitted.

  Lemma entails_unfold :
    forall M A1 A2, M ⊢ A1 ⊆ A2 ->
               (forall σ, sat M σ A1 -> sat M σ A2).
  Proof.
    intros.
    unfold entails, arr, a_or in *.
    specialize (H σ).
    repeat asrt_sat_unfold_neg;
      asrt_sat_auto_destruct_conj;
      repeat asrt_sat_unfold_neg;
      auto.

    contradiction (sat_neg_is_not_sat M σ A1).
    apply sat_neg; auto.
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

  Fixpoint contains {A : Type}`{Eq A}(l : list A)(a : A) :=
    match l with
    | nil => false
    | h :: t => eqb a h || contains t a
    end.
  Print asrt.

  Fixpoint simplify_conj_helper
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

  Definition simplify_conj A := fst (simplify_conj_helper A nil).

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
    repeat apply hq_conj_assoc1;
    repeat apply hq_conj_assoc2;
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
    forall M σ, sat M σ a_true.
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
    unfold entails, arr, a_or; intros.
    asrt_sat_unfold_neg.
    specialize (H σ).
    asrt_sat_unfold_neg.
    repeat asrt_sat_auto_destruct_conj;
      repeat asrt_sat_unfold_neg;
      repeat asrt_sat_auto_destruct_conj.

    apply nsat_and1.
    repeat asrt_sat_unfold_neg;
      asrt_sat_auto_destruct_conj.
  Qed.

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

  Ltac by_call_ext_adapt_strong :=
    try (eapply hq_conseq; [apply hq_call_ext_adapt_strong, lspec_base| | | ];
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

  Lemma entails_prt_extl :
    forall M x y, M ⊢ (a_prt x ∧ a_extl y) ⊆ (a_prt_frm x y).
  Proof.
  Admitted.

  Lemma entails_prt_intl :
    forall M x y C, M ⊢ ((a_ e_typ y (t_cls C)) ∧ ¬ a_extl y) ⊆ a_prt_frm x y.
  Proof.
  Admitted.

  Lemma entails_intl_not_extl :
    forall M e C, C ∈ (snd M) ->
             M ⊢ (a_ (e_typ e (t_cls C))) ⊆ ¬ a_extl e.
  Proof.
  Admitted.

  Ltac setup_shop :=
    assert (HitemPrice : ⟦ price ↦ t_int ⟧_∈ typeOf_f Mgood Item);
    [apply type_of_itemPrice|];
    assert (HaccountBalance : ⟦ balance ↦ t_int ⟧_∈ typeOf_f Mgood Account);
    [apply type_of_accountBalance|];
    assert (HshopAccount : ⟦ acc ↦ t_cls Account ⟧_∈ typeOf_f Mgood Shop);
    [apply type_of_shopAcc|].

  Lemma entails_different_type_neq :
    forall M e1 e2 T1 T2, T1 <> T2 ->
                     M ⊢ ((a_ e_typ e1 T1) ∧ (a_ e_typ e2 T2)) ⊆ ¬ (a_ (e_eq e1 e2)).
  Proof.
    intros.
    
  Admitted.

  Lemma I1 :
    spec_sat Mgood S1.
  Proof.
    setup_shop.
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

        simpl_types.
        simpl_conj_hq.
        unfold simplify_conj;
          simpl.
        repeat try apply_hq_sequ_with_mid_eq_fst;
          repeat split_post_condition_by_conjunction;
          try solve [by_hq_types2; by_assumption];

        try solve [apply hq_mid;
                   eapply h_strengthen;
                   [apply h_read_type|];
                   intros_entails;
                   repeat asrt_sat_auto_destruct_conj;
                   eapply apply_entails;
                   [apply entails_fld_type; eauto|eauto]].

        *** (* itemPrice = item.price *)
          admit.

        *** (* thisAcc = this.acc *)
          admit.

        *** (* oldBalance = thisAcc.balance *)
          admit.

        *** (* tmp = buyer.pay(thisAcc, itemPrice) *)
          by_call_ext_adapt_strong;
            try solve [by_assumption].
          simpl_types.
          repeat apply entails_conj_split;
            try solve [by_assumption].

          ****
            by_assumption.
            eapply apply_entails;
              [apply entails_prt_extl|].
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

        ***
          apply hq_if.

          **** (* internal call to this.send *)
            admit.

          **** (* external call to buyer.tell *)
            admit.

        *** (* return false *)
          unfold ret.
          apply hq_mid.
          admit.

        ***
          match goal with
          | [|- ?M ⊢ ⦃ ?A1 ⦄ _ ⦃ a_prt_frm ?e ?x ⦄ || ⦃ ?A3 ⦄ ] =>
              eapply hq_conseq with (A4:=A1)
                                    (A5:=a_ (e_typ x t_bool) ∧ (a_ (e_typ e (t_cls Key))))
                                    (A6:=A3)
          end.

          ****
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

          ****
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.

          ****
            intros_entails;
              repeat asrt_sat_auto_destruct_conj.
            eapply apply_entails;
              [apply entails_prt_bool|asrt_sat_auto_destruct_conj; eauto].

          ****
            apply entails_refl.

      **
        destruct H;
          subst.
        simpl.
        simpl_types.
        simpl_conj_hq.
        unfold simplify_conj;
          simpl.
        admit. (* send body needs to be clarified *)

    *
      destruct H;
        destruct H;
        subst;
        simpl.

      ** (* Account *)
        simpl_types.
        apply destruct_accountMths in H0;
          destruct H0;
          destruct H;
          subst;
          simpl;
          simpl_types;
          simpl_conj_hq.

        ***
          simpl.
          unfold simplify_conj;
            simpl.
          unfold transferBody.
          apply hq_mid.

          apply_hq_sequ_with_mid_eq_fst.

          ****
            apply h_if.

            *****
              apply_hq_sequ_with_mid_eq_fst.

            ******
              eapply h_strengthen.


      **
        simpl in *.
        try match goal with
            | [H : ⟦ _ ↦ _ ⟧_∈ empty |- _] =>
                inversion H
            end.
  Qed.

End Example.
