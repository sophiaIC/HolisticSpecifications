# Overview

We sincerely thank the reviewers for detailed and thoughtful comments,
and for the opportunity this gives us to explain our work better.

## O1. The Fundamental Argument


Our fundamental argument is as follows: `Mod1` and `Mod3` are \"fit for
purpose\", whereas `Mod2` is not -- we hope all reviewers agree on that.
Moreover,   (S2), i.e. an account's balance does not decrease unless
`transfer` was called with the correct password, is satisfied by all three
modules; namely, (S3) does not preclude `Mod2`, which allows the
password to be overwritten. On the other hand, (S3), ie the balance
of an account does not decrease ever in the future unless some external
object has access to the account's current password now, is satisfied by the
\"good\" modules `Mod1` and `Mod3` and not by the \"bad\" module `Mod2`.
This is, we argue, sufficient motivation to study Necessity
specifications.

Reviewer D argues further that (S3) is not strong enough when we operate
in an environment where an external module has access to the password.
Indeed, in such a case, all bets are off. However, (S3) does guarantee
that if the account is passed to a context where no external object has
access to the password, then the balance will not be modified. Namely,
the \"active\" external objects in the context of the callee are a
subset of the \"active\" external objects in the context of the caller.
In further work, we plan to extend Hoare logics, so as to make this
guarantee formal.

There are some subtle distinctions between Necessity specifications,
which we summarised in section 3.4.1, but we should explain them in more detail.

In particular, `NecessityBankSpec`$_c$, defined as \
`            ` `from a:Account` $\wedge$ `a.balance==bal to a.balance` < `bal`\
`            ` `onlyIf` $\exists$ `o.[`$\langle$`o external`$\rangle$ $\wedge$ $\langle$`o calls a.transfer(_, _, _)`$\rangle$`]`\
 mandates that if the balance should decrease after any number of
execution steps, then the *first* step was a call to `transfer`. This is
clearly not satisfied by *any* of the three modules; consider, as a
counterexample, the code
`x=x+1; a.transfer(...); c=new Account`.
This code *does* call `transfer`, but not in the first step.

On the other hand, `NecessityBankSpec`$_d$, defined as\
`            ` `from a:Account` $\wedge$ `a.balance==bal to a.balance` < `bal`\
`            ` `onlyThrough` $\exists$ `o.[`$\langle$`o external`$\rangle$ $\wedge$ $\langle$ `calls a.transfer(_, _, _)`$\rangle$`] `,\
is slightly weaker, in that it mandates that if the balance should
decrease after *any* number of execution steps, then the *some* step was
a call to `transfer`. It is satisfied by all three modules.

Finally, we could add a further variation, `NecessityBankSpec`$_e$,
defined as\
`            ` `from a:Account` $\wedge$ `a.balance==bal next a.balance` < `bal`\
`            ` `onlyIf` $\exists$ `o.[`$\langle$`o external`$\rangle$ $\wedge$ $\langle$`o calls a.transfer(_, _, _)`$\rangle$`]`,\
which would mandate that if the balance should decrease after 
*one* execution step, then that step was a call to
`transfer` and the right password was passed. This is satisfied by all
three modules, and is, in fact, the formal description of $(S2)$.

## O2. Concerns

We believe that the reviewers concerns fall into three areas. 
A:  External calls from within internal modules not  yet supported 
B: Novelty, and delta wrt to  Chainmail and VerX. C: Clarity of
presentation.

### O2.A: External Calls
 
Necessity does not --yet-- support calls of external methods from within
internal modules. This is, indeed, a limitation, but is common
in the related literature. For example, VerX [@Permenev] work on
effectively call-back free contracts, while [@Grossman] and  [@Albert]
on drastically restricting the effect of a callback on a contract.
A treatment of external calls in Necessity would bring some further 
complexity, and would detract from the main focus of this paper.

[@Permenev] Anton Permenev, Mimitar I. Dimitrov, Petar Tsankov, Dana Draschler-Cohen, and Martin T. Vechev. VerX: Safety Verification of Smart Contracts, Symposium on Security and Privacy, 2021

[@Grossman] Shelly Grossman, Ittai Abraham, Guy Golan-Gueta, Yan Michalevsky, Noam Rinetzky, Mooly Sagiv, and Yoni Zohar. Online Detection of Deffectively Callback Free Objects with Applications to Smart Contracts. POPL, 2017

[@Albert] Elvira Albert, Shelly Grossman, Noam Rinetzky, Clara Rodrigues-Nunez, Albert Rubio, and Mooly Sagiv. Taming Callbacks for Smart Contract Modularity. OOPSLA, 2020

### O2.B: Novelty

Our Necessity operators are novel and they allow us to develop a
Logic -- something lacking in the competition. Moreover, the
operator `onlyThrough` cannot be encoded into either VerX or Chainmail, or using
traditional temporal logic operators. Neither VerX, Chainmail, or
temporal logic operators, are able to refer to two program states in an
execution, and then another third program state that lies between them.
`onlyThrough` specifications is a core component of Necessity proofs.

While  VerX and Necessity deal with protecting code from unknown
code, VerX is Smart Contracts-specific whereas Necessity is not domain
specific. The technology used is also different: VerX is a model checker
whereas Necessity programs are proven using Coq.

It is true that some of the Necessity definitions, and their encodings,
are inspired by Chainmail [@Drossopoulou], but the contributions of our
paper go much farther. The Necessity language and proof system, the
soundness result, and the proven examples have no equivalents in
Chainmail. For the Coq code both Chainmail and Necessity use Chlipala's
CpdtTactics library [@Chlipala], and use similar definitions for some low level 
properties and common Coq idioms (partial maps, substitution, etc.), 
however they do not share any overlap in the contributions of this paper:
the proof system, its soundness result, or the proof of the bank account
example's adherence to its specification.

[@Drossopoulou] Sophia Drossopoulou, James Noble, Julian Mackay, and Susan Eisenbach, Holistic Specifications for Robust Programs, FASE 2020.

[@Chlipala] Adam Chlipapa, Certified Programming with Dependent Types, `http://adam.chlipala.net/cpdt`, accessed 2021

### O2.C: Clarity 

The reviewers' questions give us guidance where we should explain better.

#### Adaptation 

Adaptation is an important auxiliary concept used in Def. 3.10 and 4.2, but
is not a central contribution. We motivated the adaptation operator
$\triangleleft$ in lines 413-424, but we should have given more detail:
The specification on lines 416-417 talks about three different program
states. That specification only makes sense if variable $a$ denotes the
*same* object in all three states, even though it is possible that in
these states the contents of the variable $a$ has changed (eg through an
assignment of the form $a:=...$, or even because $a$ went out of scope).


Thus, $\triangleleft$ is a variable renaming operator; it ensures that
variable names used at one point in the execution refer to the same
object at a future point in the execution. For example, for any variable
$x \in dom(\sigma)$ we have that $\lfloor x \rfloor_\sigma$ =
$\lfloor x \rfloor_{\sigma' \triangleleft \sigma}$, even though it is
possible that
$\lfloor x \rfloor_\sigma \neq \lfloor x \rfloor_{\sigma'}$, and that
$\lfloor x.f \rfloor_\sigma \neq \lfloor x.f \rfloor_{\sigma' \triangleleft \sigma}$.

#### **Access**

Access is not deep, and only refers to objects that an object has direct
access to via a field or within the context of the current scope. A
transitive definition of access would not be useful in specifying safe
and robust software. The restricted form of access used in Necessity
specifically captures a crucial property of robust programs in the open
world: *access to an object does not imply access to that object's
internal data*. For example, an object may have access to an account
`a`, but a *safe* implementation of the account would never allow that
object to leverage that access to gain direct access to `a.password`.
Necessity is thus concerned with if and how objects are able to gain
direct access to an object, and not deep, transitive access. Indeed, if
access were defined transitively, then many objects would be defined as
having access to objects that they could not gain a direct reference to,
and as such render `<x access y>` as almost meaningless, and any safety
specifications written using access to be prohibitively restrictive.

#### **Assertion encapsulation**

Assertion encapsulation is the property that an assertion may  
be invalidated only by execution of methods from a certain module.
Expressed differently, a piece of code that does not contain calls
to a certain module is guaranteed not to invalidate any assertions 
encapsulated by that module.

Assertion encapsulation has been used in proof systems to solve
the fame problem [@Leino,@Banerjee].

Assertions are therefore not "encapsulated" by some
code, but rather by a module. Taking Reviewer A's example where `C'` = `C; x
:= x`, if `C` contains internal method calls then it may invalidate encapsulated
assertions, and so may `C'`.
A, then so does C'.
 
 [@Leino] Rustan Leino and  Peter Mueller, Object Invariants in Dynamic Contexts, ECOOP 2004.

[@Banerjee] Anindya Banerjee and  David A. Naumann, State Based Ownership, Reentrance, and Encapsulation, ECOOP 2005.



#### **Emergent Behavior**

Reviewer A had difficulty understanding what we meant by emergent
behaviour but surmised that it meant that "no single procedure call is
capable of breaking the necessity specification, but a sequence of calls
can very well be". That is correct.

# Proposed Changes

We propose to make the changes listed below, and all changes suggested by the
reviewers. We are confident that we can accomplish them until February.

## P1. External Calls

We argue that the current work is substantial, and a treatment 
of external calls would be too substantial and would not allow
us to focus on the important aspects of the current work.

But we can outline our current thinking: As a first approach, we
will require that the arguments to external calls do not include
internal objects, except for the receiver and parameters (thus ensuring
that external accessibility of internal methods does not increase); we
would rely on the classical pre- and post- conditions of the internal
methods -- as we currently do. As a more advanced approach, we will
develop extensions to classical Hoare Logics, which would allow us to
reason about points in the code where external calls are being made.
This would be the first time we could be inspecting the code in the
bodies of the functions.

## P2: Novelty

We will strengthen our statements about VerX and Chainmail in line with
what we said above.

## P3: Clarity

P3.1 For adaption, access, and encapsulation we will amend the explanations
as stated above. We will replace the name Adaption with Rename to 
make its purpose clearer.

P3.2 For emergent behaviour we will include the reviewer's statement and also
say that "(S2) does not take account of the module's *emergent
behaviour*. That is, (S2) does not consider the behaviour that emerges
from the interaction between the `transfer` method, and the other
methods of the bank module. What if the module leaks the password?"

P3.3. The bank account example from section proven in Section 5 differs, and
is more complex that `Mod3` in Section 2. We chose the more complex
version, in order to demonstrate some more sophisticated features of Necessity,
namely, the use of ghost fields, and the more complex module and data structures, 
where emergent behavior arises across multiple classes. 

However, the more complex example is probably detracting. 
We will replace the current Bank Account proof with a simpler Coq proof
that matches the straightforward introductory example (`Mod3`). We will put the
current example in an appendix so that we can show reasoning about ghost
fields and more complex data structures.

P3.4 We will move the clarifying examples from section 3.4.1 with the
additional discussion from the overview to Section 2.

P3.5 Moreover, we will implement the detailed suggestions from the reviews

#### Reviewer A

-   Streamline Introduction: we will move the related work to the
    related work section

- Clarify the meaning of the term "emergent behaviour. Namely, write
expand line 70 to

"(S2) does not take account of the module's *emergent behavior*, that is
it does not consider the behaviour that emerges from the
interaction between the `transfer` method, and the other methods of the
bank module. What if the module leaks the password?"

-   Rework Section 2 to be clearer: we will make the outline of the
    proof structure in Section 2 clearer, at a higher level, and more
    concise.

-   We will change the order of $M$ and $M'$ in the definition of
    Arising.

-   We will make clear which state is the original state.

-   We will clarify Def. 3.9, provide a clearer description and
    definition.

-   Ensure consistent usage of Section vs. section.



#### Reviewer B
-   Fix the flow of the paper. Present a "consistent high-level story"

-   Clarify the differences between Necessity and Chainmail and VerX.

-   Be more explicit about the reasons and justifications for
    restricting external method calls

-   Provide better names for Mod1, Mod2, Mod3, etc

-   Emphasize the separation of Necessity from the inspection of code.

-   Clarify why shallow access is necessary

-   Restate NecessityBankSpec in 3.4.1

-   Provide better justification, explanation, and intuition for the
    example specifications in 3.4

-   Include a brief description of the expressiveness earlier in the
    paper than 3.4.3

-   Explain why the restriction on return values is sufficient in
    If1-Inside

#### Reviewer C

-   Replace the liveness discussion in Section 1 by discussion of safety.

-   Rewrite Section 2.4. (While Reviewer B appreciated this, reviewers
    C and A did not) We will follow the proposal to write this part in a 
   "top down" manner.

-   Replace Section 5 with the simpler, original bank account example,
    and move the current one to the appendix.

 

# Response to individual reviews

We provide a reviewer-by-reviewer list of answers to questions. We are
planning to implement as requested answers any questions that have been
omitted.

## Reviewer 30A

*In 36-55, the introduction suddenly becomes/mixes with a part on
related work. To my opinion, this completely distracts from the
description of the problem that this paper is attacking. I'd rather that
this part is moved to the dedicated related work section.* **We will be
re-organising the introduction along with Section 2 to more directly
describe the problem tackled by the paper. Discussion of the related
work will be moved to the related work section.**

*68. At this point (and also many points later), it was completely
unclear to me what \"emergent behaviour\" is supposed to mean. Part of
the reason is certainly that I am not a native English speaker, but when
I translate emergent to my mother tongue, the translation does not make
sense to me. The closest explanation I can find in the English
wiktionary says for emergent \"Having properties as a whole that are
more complex than the properties contributed by each of the components
individually.\" But this is so vague that I am having trouble to imagine
what emergent means in this context.*

*The way I understood what you mean by (unwanted) emergent behaviour is
that no single procedure call is capable of breaking the necessity
specification, but a sequence of calls can very well be. But this is not
what I would have guessed from \"emergent\" or \"Having properties as a
whole that are more complex than the properties contributed by each of
the components individually.\"* **The reviewer is correct in the meaning
of the word emergent. We have proposed a refined and more descriptive
way to introduce "emergent behavior". **

*102: I have two problems with the notion of being 'encapsulated':*

*Maybe a minor comment, actually, but again - I'm sorry - I do not
understand the name \"encapsulated\". The fact that the concept \>\>only
by executing a pice of code C one can invalidate a logical assertion
A\<\< is called \>\>C encapsulates A\<\< does not make much sense to me
because \"encapsulating\" - to me - suggests rather that A is somehow
part of C or that A is somehow wrapped/surrounded by C.*

*More severely, I still cannot get my head around the notion that only
by executing C one can invalidate A. Imagine $C' = C; x:=x$. Obviously
$C' \neq C$, but if $C$ can invalidate A, so can $C'$. How can there be
a piece of code $C$, so that only $C$ but not $C; x:=x$ can invalidate
A?* **We have expanded on the description of "assertion encapsulation".
Hopefully this clears up any misunderstanding.**

*167 Here, one slowly understands that emergent = putting multiple calls
in sequence.*

*176-181: Is what you describe here really inherent to your necessity
logic? Isn't it rather a consequence of - where - you check the validity
of your specifications?* **We are not totally clear chat you mean. What
is inherent to our Necessity specifications is that it concentrates on effects
(here change of balance).**

*182: I find the term \"not monotonic\" misplaced here. Isn't it obvious
that adding more behavior can invalidate more stuff?* **Perhaps this is
obvious, but we thought it was an interesting observation. We would be
happy to remove, or qualify. **

*192: One could draw a comparison to loop invariants: While pushing a
loop invariant through a loop body, the invariant can (and likely will)
also break intermediately. The point is just that it holds before and
after the execution of the loop body, just like you specifications hold
before and after the call.* **excellent point. We can add the comparison,
and also to object invariants.**

*199: \"the executing object (this) is always external\". Without your
formal semantics presented later, this sentence (snippet) is very
confusing. Intuitively, \"this\" is always an internal thing because it
is the name that an objects gives to itself, internally.* **Yes, `this`
is always internal to the executing object, however, in this paper, when
we use the words "internal" and "external", we are generally referring
"internal" or "external" to a specific module. We will amend the paper
to make this clearer.**

*Section 2.4, I must say, I find extremely tedious and very difficult to
follow. I firmly believe that this can be streamlined to that one must
not mentally follow through 9 steps (a - i). Many notions are also only
explained later. E.g. it is not clear (and also does not become apparent
from the explanations in Sec. 2.4) why one needs to construct from
'per-method conditions' the 'single-step conditions'. And is this really
important in order to get an overview of the approach that the paper is
taking?* **We will rewrite 2.4 to present the proof overview from a top down perspective.
this should make the proof easier to follow.**

*In 206, it is again stated that an assertion A, i.e. a logical formula
A, can be encapsulated by a module. Later, in l.211, it is said that
'balance' is encapsulated. But balance is a term, not a formula. What
does it mean to invalidate a term? I don't get it.* **Indeed, `this.balance`
is an expression. What we mean when we say that  `this.balance` is
encapsulated, we mean that the assertion `this.balance=b`
is encapsulated. On the other hand, notice that any expression is an
assertion, therefore saying that  `this.balance` is
encapsulated has the meaning we give it. We will clarify in the next version
of this paper.**

*I214.5: \"Per-method conditions are necessary conditions for given
effect and given single, specified, method call.\" I do not understand
what this sentence is telling me. In particular, I really don't
understand what an effect is here. What exactly is the difference
between call, step, effect, \...?* **Call refers to a method call; step 
is any execution step, e.g. an assignment, an object creation, a method
call, etc. Effect is any change in an object's contents, eg a change 
of password, or an increase in the balance. We will clarify.**

*I243 says \"Note that our proofs of necessity do not inspect method
bodies\" This makes absolutely no sense to me. How can I infer - or
more: 'prove' - anything about an object C (the code) without looking at
C? This needs an explanation. In the explanation that follows you
mention pre and postconditions of methods, but how can I prove pre- and
postconditions of methods, if I cannot look at the methods?* **Necessity
proofs do not inspect method bodies. Necessity does rely on traditional
pre- and post- conditions. Proving the latter of course  requires inspection 
of the code. What we meant is, that because establishing methods'
pre- and post- conditions is a well-searched area, that part
can be ``outsourced'' to existing logics and tools.
In that sense, Necessity is parametric with such a system, and does not impose
further code inspection. We will clarify in the next version.**

*253.5: What is an \"unsurprising\" language?* **We meant that TooL
is a very simple imperative, class based, object oriented language, 
whose semantics should not surprise anyone.**

*I263 following: At this point I was wondering, which of Mod1, Mod2,
Mod3 is internal, what is external? It would be good to refer back to
that example and point out to the reader what is supposed to be internal
and what external.* **Necessity is a specification for programs in the
open world. In this paper we characterize the "internal" as the module
we are specifying, and the "external" as the unknown open world. Under
this characterization, `Mod1`, `Mod2`, and `Mod3` all represent
different implementation of a bank account being specified, and thus are
all "internal".**

*IDef. 3.2: Why would one write Arising(M, M', sigma) iff \... M'; M,
sigma-0 \... Why flip the order of M and M'? ...*
**This is a good point. We will make this change.**

*I 349-350 why should x be fresh in sigma?* **x is fresh in sigma
because it is used to refer to the object being quantified. It is alpha
(the location in the heap) that should not be fresh in sigma.**

*I393-394: \"If an arising state \... then the original state must have
\...\" What is the \"original state\"? The arising one? Or the initial
state that arises from the definition of arising states? If it is the
former, I'd suggest \"If an arising state $\sigma$ \... then $\sigma$
must have\...\".* **Yes, the original state is arising. We will make
this change and clarify this in the text.**

*Def. 3.8: It would be good to ostentatiously clarify that necessity
specifications cannot nest, i.e. the nonterminal S does not appear on
the right-hand side of the grammar. Only nonterminals A and those come
from the language Assert, I suppose.* **Yes, that is correct. We will
make this change to the text.**

*417: It is undefined what - means. There exists a value? For any value?
It depends on the formula?* **Yes, \_ means for any value. Will 
add to the notations in line 302.**

*Def. 3.9: Again, to me this is absolutely central. It definitely needs
- more- explanations and a lot of intuition. **Indeed, we have discussed
it under O3. Thank you for pointing out.**
*Technically, I am not 100% sure what the colon operator does in l.431
and 432. Is that a concatenation of lists? If yes, please say so.*
**No,  While
being very nitpicky: shouldlocal \..., contn\... not be a tuple instead
of a set? Less nitpicky: You primed all names from $\sigma'$ except for
$\psi$. It would be much less distracting $\psi$ was called $\psi'$.*

*442-456: It is totally unclear how/why the $\triangleleft$-operator
does the trick for you necessity modalities. Part of the reason is that
the definition $\triangleleft$ is described/explained in not enough
detail (for me). But I also firmly believe that the definition of the
semantics of the necessity modalities deserves to be provided some
intuition. In particular an intuition of how $\triangleleft$ defines
these semantics.* **We refer the reviewer to the Overview for our explanation of
adaptation.**

*482: I believe that it deserves an explenation why no module satisfies
NecessityBankSpec-c. It is not obvious to me.* **For an account's
balance to change after some number of execution steps, `a.transfer`
must be called in some intermediate state. It is not necessary that that
call to `a.transfer` must occur in the first program state of that chain
(as implied by OnlyIf). More discussion under O1. **

*Sec. 3.4.2: This example is completely inaccessible and handwavy to
me.* **We can easily provide more detail; the final version will have 
an additional 3 pages, which will give us the space.**


*Definition 4.1: I have (almost) the same problem as with l.442-456
here. Why almost? Because here there is the half-sentence \"we have to
interpret one assertion in two different states\" that provides a little
bit of intuition on how $\triangleleft$ helps in this definition. But it
is not enough intuition for me.* **We refer the reviewer to O2.C: Clarity for our
explanation of adaptation.**

## Reviewer 30B

68: the focus on emergent behavior is good. This is why I like the
motivation for this work - emergent behavior is very important in real
software systems, but a lot of verification/PL work does not reason
about it explicitly (or at all).

90: this is the first example I noticed of a weird transition. The
authors go straight from saying that there are three new operators to a
lot of detail on the first of those. The paper here would flow better if
the authors gave an informal description of all three operators (to give
the reader an intuition for what's coming next) rather than going
straight into gory detail. **We will rework the Introduction to be less
technical, and better introduce the concepts within the paper.**

99: the authors state that necessity operators are second-class, but
don't really justify this choice or explore its consequences, and it is
never returned to. I'm not sure if the necessity operators being
second-class is actually the right choice, and especially at this point
in the paper, where I as a reader don't yet fully understand them, this
statement throws me off. **Being second class allows
us to develop a proof logic (line 103-104), while also being expressive enough:
the Necessity language could encode all known Chainmail examples (line
118). We should discuss these two points together.**  

200: when you make an assumption like this one, please justify it to the
reader rather than simply saying "Note \..." Especially for such an
important assumption, as this one, it is unsatisfying as a reader to be
left wondering why you have done this. **We refer the reviewer to O2.C: Clarity for
our explanation of our choice around external method calls.**

205: you refer to Mod1, Mod2, Mod3, etc. many times, but their names are
not descriptive at all. This was the point where I got mildly annoyed at
having to go back and check which implementation Mod3 was. I suggest
renaming the modules to something that describes their properties, e.g.
Mod3 could become "SafePwdSet" or something like that. **We will make
this change.**

243: you might consider emphasizing this point more: it is a strength of
your approach that it doesn't make many assumptions about how these
annotations are checked, and so is compatible with lots of existing
work. **Yes, we will highlight this more when we rework the presentation
of the paper.**

335: thanks for defining your shorthands rather than just using them and
making us guess what they mean :)

351: I have a serious concern about definition 8 (x access y) here. It
seems to me that it is saying that if y's value is exactly the value of
one of x's fields (f), then x can access y. That seems reasonable, but I
don't see any notion of multi-step access paths here, which seems
suspicious to me. After all, intuitively I would expect that (x access
y) would be true if for example the value of the expression x.f.g is the
same as the value of y (and so on for any arbitrary number of field
accesses). Did I miss something about your setup/language that forbids
fields themselves having fields? Or is it the case that (x access y) is
defined to be false in a case like the one I mentioned above? If so,
that seems to me like a "soundness" problem in the sense that it
violates what I as a specification writer would expect that
specification to mean, and therefore might result in
incorrectly-specified code. **We refer the reviewer to the Overview for our
explanation of access.**

382: inside is a very useful concept. I might consider mentioning it
earlier, perhaps by working it into one of the examples in section 2.

459: this is another case where the flow of the text is jarring. There
is no explanation for why now is the appropriate time to consider more
examples of specifications. This might make more sense as a separate
section rather than as a subsection, with a short justification saying
something like "we now present some examples to give the reader an idea
of the expressiveness of our approach"; you didn't explain that that was
the goal of the example section in this draft until the very end of the
section! **Thank you for pointing this out. We will amend this in our
presentation rework.**

463: I suggest re-stating the original NecessityBankSpec here so that
it's easier to compare with the a-d variations. **We will make this
change.**

486: please explain what you want the reader to take away from these
examples! Why is it important that e.g. both Mod2 and Mod3 satisfy b and
d, but neither satisfy c? Explain to the reader why the changes that you
made from the original cause these changes in what can satisfy the
specification, rather than just stating it as fact. Do not make the
reader guess what you want them to understand.

571: I'm not convinced by your claim here that all you need to do is
ensure that objects of a confined type only must never be returned from
method bodies. What if a confined type is accessible from the field of a
returned object? Maybe your type system forbids this (I expect that it
does!), but the presentation of it here is a bit confusing, perhaps just
because you've given so few details. **Indeed, the type system does
forbid it. We will add clarity here.**

619: can you comment on how hard it would be to modify your system to
support this? It seems like it is important if you want to use this
system to validate a realistic program. **It is hard to say how
difficult it would be to add this, but it would likely require some work
developing aspects of a more traditional specification language to
detect and specify certain kinds of external method calls. It is notable
that other work in the area makes the assumption that methods are
"effectively call-back free" [@Permenev]. This would likely guide our
approach as a starting point.**

819: it is not easy to see this unless you introduce another data
structure, like a list, to hold the arbitrarily-many accounts. Since you
don't allow internal code to call into external libraries, you'd have to
define the list yourself, so this would actually be quite the project.
**Technically the restriction does not allow calls to unknown, and thus
unspecifiable, code. If the List library code was known, and specifiable
then we could extend the example. Even if we did allow for external
method calls, it would not be possible to write specifications about
those calls as the effects of such a call would be unknown.**

1036-1042: there seems to be a lot of overlap between the present work
and Chainmail. You might want to spend another sentence or two here
discussing the differences. **We will add this to our revision.**

## Reviewer 30C

Section 1: I'm not sure if paraphrasing liveness and safety is a good
idea because liveness/safety verification in the traditional sense is
also reasoning about sufficient conditions for good things to eventually
happen or for bad things to never happen. The point here is the
distinction between sufficient and necessary conditions about the
behavior of a program.

Section 2.4 doesn't work very well (at least for a first reading)
because it is written in a bottom-up manner. I had no idea why assertion
encapsulation is the first step because I didn't have a big picture how
necessity specification might be verified. Explaining backwards from
Part 4 to 1 may work better (but I'm not sure\...).

It seem to me that it can be hard to show assertion encapsulation
because of universal quantification over all external modules and
states. The existence of a type system and a proof system for assertion
encapusulation, which is discussed in 4.1.3, is nice and plausible but I
find the discussion on Enc(A) handwaving and the derivation in Section
5.1 is hard to follow. I think you should explicitly state that the bank
account example is typed by the assumed simple type system for
confinement.

I'm not sure why Section 5 extends the simple bank account example so
much. Is the extension needed to demonstrate the verification framework,
or you thought the examples in Section 2 would be too simple? Maybe they
are simple but I think it is a good exercise to show verification of the
first examples. It was hard for me to follow the extended example as a
first verification exercise.

## Reviewer 30D

> The direction of this research is important. However, the advances that
this paper makes do not seem strong enough and the work looks rather
premature to me for the following reasons.

We are very happy that you concur with the direction of this research. 
The advances are the identification of the Necessity operators, the semantics
of Necessity, the application to case studies, the Logic for reasoning about 
Necessity specifications, and the application of the latter to an
interesting example. These are, we argue, strong advances. 


> First, the way to connect the \"from\" and \"to\" conditions seems to
involve unnecessary complications, which may restrict the applicability
of the work to other languages. Updating physical states using fresh
variables sounds too restrictive.

We discussed the adaptation operator,  $\triangleleft$,  in some detail in the
overview, and will expand some more here:
We do _not_ update physical state: 
 $\triangleleft$ is not part of
 the execution of the underlying language; it  is applied only _notionally_  
to the state, to give meaning to
 \"from\" and \"to\".

> For example, in assembly, one cannot
create fresh registers. 

Indeed, one cannot create fresh registers, and neither do we 
expect execution to create fresh variables.

> Here it is unclear to me why the authors cannot
use logical auxiliary variables as done in modern separation logics.

The adaptation operator introduces fresh local variables in the 
state -- this would be the counterpart of logical auxiliary variables.


> Second, the allowed control flow between the external and internal
modules is restricted (ie, the internal module cannot invoke external
modules). Since reasoning about the internal module should be
essentially independent of external modules (because external modules
are completely arbitrary), similar reasoning as presented in this paper
should be possible even when the internal module invokes functions of
external modules.

Indeed, Necessity can deduce per-method assertions based on
traditional pre- and post-conditions. However, we expect that
these traditional pre- and post-conditions should be verified 
by traditional Hoare logic based tools, and currently, most traditional
techniques cannot verify calls to unknown code.
This does not of course mean that there is no hope
for external calls -- we have started working on this. Note also,
as argued in the overview, that many other current research works 
either forbid or heavily restrict calls from internal to external modules.

> Finally, more importantly, although the paper claims the (S3) condition
instead of (S2) as an advance over Chainmail, the condition (S3) is not
so convincing. There are two concerns. First, (S3) does not say anything
useful in the presence of an external module that has access to the
password, which is the case in general. 

It is not modules that have access to the password; it is object. Thus,
as we discuss in the overview, if no external objects in a callee's context
have access to the password, then (S3) guarantees that while the
callee is executing, the balance will not decrease. This guarantee holds, 
even if the caller's context contains
external objects which have access to the password. 

>  On the other hand, (S2) implies that external
modules without knowing the correct password cannot change the balance.

This is not true. As argued in the overview, and also lines (67-69) in
the paper, (S2) does not preclude that the password is overwritten 
without prior knowledge. Thus, the "bad" module,  \"Mod2\", satisfies 
(S2). 

> Second, (S3) seems to relying on the setting that the password is an
unforgeable object instead of a string, which is rather artificial. 

Indeed, we do rely on object identities being unforgeable. This is a fundamental
assumption in capability-secure programming,  [Miller 2006], and 
is also required by many works in the literature, eg Swasey et al. [2017].
Relaxing such assumptions would be very interesting further work
proababy requiring probabilistic reasoning.

In summary, (S2) cannot distinguish "good" from the "bad" modules, 
while (S3) can, and this motivates our work.

In the next version of this paper, we will make this argument much crisper.
