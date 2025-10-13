Dear Reviewers, 

Thank you for recognizing the potential of our work, for your time and effort in reviewing our paper, for  the diversity of your comments, and the perseverance in our discussions. All these discussions and interactions have shown to us what needed to be explained better. 

We are particularly grateful to Reviewer_C for the three separate rounds of discussion, and their patience to explain their views to us.

We now are submitting

- The improved versions of our paper (as two pdfs, with and without the supplementary material),

- A summary of improvements in the current version (next in this pdf),

- A response to the more recent comments from Reviewer_B and Reviewer_C (below in this pdf),

- A diff between the February version and the improved version (as a seperate *pdf).


# Summary of improvements in the current version 

#### Improvements Requested by Reviewers 

1. We ensured that any terms in Section 2 are used only after their definition. 

2. We repaired annoying typos in the Definition of “protected”, and “deep satisfaction”.

3.  We extended the discussion of Stbl, Stbl+, and Enc. We added examples that demonstrate their differences, and explanations why these properties are needed.

4. We clarified how the type system is used in reasoning about protection.

5. We added the definition of well-formed specifications (Def 5.6), explained why the various requirements are made. Moreover in the definition of well-formed modules (line 978), we. reminded the reader about the requirement for well-formed specifications. 

6. We explained how to obtain sound logics for assertions, even though “protection” is a new concept.

7. We replaced the term “scoped satisfaction” by “deep satisfaction” (lines 1033-1044). We improved the explanation that “deep satisfaction” as well as satisfaction (lines 719-723) are based on scoped execution. 

8. We improved the bibliography.

9. We shrunk the subsection on expressiveness to just 4 lines.

10. We discuss the rationale of ghost code in lines 420-425, and give an example where ghost fields are used in Appendix A.3

11. We implemented all further  requests made by the reviewers.


#### Further Improvements -- not Requested by the Reviewers 

12. We introduced the notation $^\sigma\lceil A\rceil$ to substitute all free variables in $A$  by their values in $\sigma$ -- cf. Def. 4.5. This allows us to avoid some clutter in the notations -- cf Def. 5.2.

13. Amalgamated old section 4 into section 3, and old section 6 into old section 5. Now the paper has 8 rather than 10 secretions, and is better balanced.

14. Explained that our approach relies on the platform’s guarantees and could also be used for interlanguage safety -- footnote 4.