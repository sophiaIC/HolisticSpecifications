// Sophia's attempt


trait Account extends object {

  const obeys: bool

  // these two ghost functions allow us to write classes implementing
  // Account, with different foorprints for balance and CanTrade
  ghost function balanceFootprint(): set<object> 
                reads this
  ghost function CanTradeFootprint(): set<object> 
                reads this
  ghost function sproutFootprint(): set<object> 
                reads this
  ghost function depositFootprint(): set<object> 
                reads this

  ghost function balance(): nat 
    reads this, balanceFootprint()  
  
  ghost predicate CanTrade(acc: Account)  
  reads this, acc, this.CanTradeFootprint(), acc.CanTradeFootprint() 
  ensures this.obeys ==> acc.obeys
  
  // This lemma has to be proven in all classes implementing Account
  lemma CanTradeSymmetric()
  ensures forall a1:Account, a2:Account:: a1.obeys && a1.CanTrade(a2) ==> a2.CanTrade(a1)


method sprouts() returns (account: Account)
  modifies this.sproutFootprint()
  ensures this.obeys ==>
      fresh(account) && account.obeys &&
      account.balance() == 0 &&
      account.CanTrade(this)

  method sprout(acc:Account) returns (account : Account)
    modifies this.sproutFootprint() 
    ensures this.obeys ==>
        ( fresh(account) && account.obeys &&       
        account.balance() == 0 && 
        account.CanTrade(this) )
        /*  Dropping this because of Dafny/SMT difficulty with quantifiers
           ( forall acc:Account::
                  ( allocated(acc) && !fresh(acc)==> ( acc.balance() == old(acc.balance()) ) ) */ 
    ensures this.obeys ==> acc.balance() == old(acc.balance())
         
  method deposit(amount : nat, acc : Account) returns (b : bool) 
    modifies this.depositFootprint(), acc.depositFootprint()
    ensures this.obeys && b ==>  
          this!=acc &&
          this.CanTrade(acc) && old(this.CanTrade(acc)) &&
          old(this.balance())>= amount && 
          this.balance()==old(this.balance())-amount && 
          acc.balance()==old(acc.balance())+amount          
    ensures this.obeys && old(this.balance())>=amount && 
            old(this.CanTrade(acc)) &&  this!=acc 
            ==> 
            b==true && this.CanTrade(acc)
}
   
// Challenges: 1. break the circularities, 2. the foorprints need to be defined

// About the foorprints (reads-clauses)
   
 // UnsUnsure whether the reads clause is needed in 
    // if no reads clause, then it would be heap-independent, 
    // BUT, what about the fresh objects?

//  HOW do wesay that acc.balance not modified unless you have acc?
    // AHA! This is implcit here, because we have specified that balance reads this.
    // But in our work, we do not require that the foorprint of balance is known, and
    // we allow many different implementations of balanace.
    // This will not be expressible in Dafny.



























































