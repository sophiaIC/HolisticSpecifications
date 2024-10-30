# HolisticSpecifications
Our work on Holistic Specifications

## Chainmail Model

The Coq model implements Chainmail mostly as described, however, it differs from the formalisation in the paper in a few noticable ways. These differences are outlined here, along with any other parts of the model which may need some explanation.

### Building the Coq Sources
There are several coq models associated with Chainmail, each associated with a different aspect of the project. To compile a coq model, within a root directory of that coq model, first run:

`coq_makefile -f _CoqProject -o CoqMakefile`

followed by:

`make`


### Quantified variables

In the paper, quantifiers precede the name by which that variable should be refered in the quantified expression. However, in the model, no names are provided, and quantified variables are refered to through De Bruijn indices. This greatly simplifies the encoding, allowing for the model to be much simpler, without any meaningful difference in how the model works, since there exists a isomorphism between terms with named quantified variables and terms using De Bruijn indices. These quantified variables can be refered to in `_hole` constructors, where the `nat` refers to the index. <!-- TODO Julian, which way round did you end up doing the indices, there was a point about this earlier? -->

```coq
ex_hole : nat -> expr
av_hole : nat -> a_val
```

### Expanded Loo

The *Loo* language in the paper is purposefully simple to allow encodings of the programs and situations required, without needing to provide a complicated formal model, or rely on a part of the language that reduces the generality of the paper's results. However, using nested encodings for simple values and statements such as numbers and control flow is not as practical in the model, since any proof must step through these encodings, or a vast number of auxilliary lemmas and tactics must be defined for these encodings. To avoid this, *Loo* as presented in the model is a strict superset of that presented in the paper. It expands the paper encoding with if statements `s_if`, integers `v_int`, booleans `v_true` and `v_false`, and null `v_null`. Since these all can be encoded in the paper's formalisation, and the language in the model is a superset, we again suggest this is not problematic as there exists a simple bijection between paper and the model. We provide the encodings for the models extensions as would be required in the paper's definition below:

* `v_int` can be encoded through three classes, `Zero`, `Succ`, and `Negate`, which define arithmetic operations as methods
* `v_null` is encoded through an empty class `Null`
* `v_true` and `v_false` can be encoded through two classes, `True` and `False`
* `s_if` can be encoded through defining a method `if` on `True` and `False`, which takes in an object which defines two methods, `then` and `else`. Every `if`/`else` block is encoded as a seperate class defining these two methods. The True object calls the `then` method, and the `False` object calls the `else` method.

### Operators

The model makes extensive use of unicode operators. This allows the model to closely follow the syntax of the paper, and is designed to make it easier to read. However, it is worth noting the limitations of the proof assistant result in many similar-looking but different codepoints being in use for similar concepts in different use cases, to allow the proof assistant to distiguish between them. If you're reading the model, it is best to ignore the exact unicode characters in use, and instead follow how it mirrors the syntax of the paper. If you are trying to manipulate or make use of the model, be wary that the the unicode characters vary wildly, and it may be beneficial to examine and copy from current examples to avoid accidental mistakes.

A few particular operators of note include:
* `◌` for field access
* `◎` for module pairs and configurations, whereas `∙` for modules and configurations in assertions

### Decoupling

`Decoupling.v` is the latest version of the Chainmail model <!-- TODO Julian you're probably going to rename this all anyway, right? -->, based on the earlier `Chainmail.v`. It removes some of the dependency on the Loo language from the Chainmail specification, and has since been updated with many other improvements. At some point `Decoupling.v` should replace `Chainmail.v` entirely.
