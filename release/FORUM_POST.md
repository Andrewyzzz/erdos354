# Mathematical review summary

We present a proof of strong completeness for two dyadic floor sequences,
together with its Lean formalization:

[Manuscript](https://github.com/Andrewyzzz/erdos354/blob/main/proof/FORMALIZED_PROOF.md) ·
[Lean sources](https://github.com/Andrewyzzz/erdos354/tree/main/formalization) ·
[Build and audit records](https://github.com/Andrewyzzz/erdos354/blob/main/formalization/RESULTS.md)

For all positive real numbers $\alpha,\beta$ with irrational ratio,
the set
$\{\lfloor2^n\alpha\rfloor,\lfloor2^n\beta\rfloor:n\ge0\}\setminus\{0\}$
remains complete after every finite deletion, using sums of distinct
remaining values. This implies part (i) of Erdős Problem 354, with base
exactly $2$.

The proof combines permanent descent of modular missing runs, finite-event
decay, digit-budget propagation, and a compactness argument for ratios of
sparse binary sums. The English manuscript follows the formalized argument
and includes the complete finite coefficient certificate.

The Lean project fixes version 4.27.0 and all dependency revisions.
Its complete build and audit cover 381 local theorems, whose transitive
axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`.
GitHub Actions reproduces the build and audit on a hosted Ubuntu runner.

We used Chatgpt-6 Astra in both the mathematical derivation and the Lean
formalization; our
[contribution statement](https://github.com/Andrewyzzz/erdos354/blob/main/CREDITS.md)
describes these roles.

We welcome mathematical examination of the argument, especially the legal
mesh representations, changing-period boundary estimate, and rational-window
construction. Please identify the relevant revision, section, or Lean
declaration in any comments.
