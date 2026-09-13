# Strong completeness of two dyadic floor sequences

[![Lean verification](https://github.com/Andrewyzzz/erdos354/actions/workflows/lean.yml/badge.svg)](https://github.com/Andrewyzzz/erdos354/actions/workflows/lean.yml)

Andrewyzzz and Chatgpt-6 Astra (AI system)

**[English manuscript](proof/FORMALIZED_PROOF.md)** ·
**[PDF](proof/FORMALIZED_PROOF.pdf)** ·
**[Lean formalization](formalization/README.md)** ·
**[Verification records](formalization/RESULTS.md)**

We prove that, for arbitrary positive real numbers $\alpha,\beta$ with
irrational ratio, the set

$$
A_{\alpha,\beta}
=\{\lfloor2^n\alpha\rfloor,\lfloor2^n\beta\rfloor:n\in\mathbb N\}
 \setminus\{0\}
$$

is strongly complete: after deleting any finite set of values, every
sufficiently large integer is a sum of distinct remaining values.
This gives the indexed completeness assertion in
[Erdős Problem 354(i)](https://www.erdosproblems.com/354), with base exactly $2$.

## The argument

We construct finite integer meshes from a certificate of twelve coefficient
chains. Their gap bounds persist under the addition of every subsequent
weight and under projection to each future endpoint modulus. Long
intervals between binary events therefore force permanent descent of a
modular gap invariant.

A complementary argument establishes finite-event decay (FE), digit-budget
propagation (DB), and long sparse rational-approximation windows.
Compactness of ratios of sparse binary sums gives a uniform lower bound
on the event cost of a nontrivial return between exact layers. A geometric
counting argument (BG) contradicts the event-spacing bound forced by
incompleteness. Upward tail normalization gives the finite-deletion result
with distinct values.

The [English manuscript](proof/FORMALIZED_PROOF.md) includes the complete
coefficient table and follows the formalized proofs. It explains the use
of good rational approximants, the FE potential, and the $T^{3/4}$ estimate
in the BG argument.

## Formal statements

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

The [frozen definitions](formalization/Dyadic354/Statements.lean)
distinguish finite-index sums from sums of distinct values. The final
theorems assume only positivity and an irrational ratio. FE, DB, BG,
normalization, and permanent descent are proved within the dependency
chain.

We audit all 381 local theorems. Every transitive axiom set is a subset
of `{propext, Classical.choice, Quot.sound}`.
The certificate is checked by kernel computation; the project uses no
`sorry`, custom axioms, or `native_decide`.
An [extracted-definition adapter](formalization/UPSTREAM.md) proves the
positive part-(i) statement in the upstream definitions.

## Reproduction

We pin Lean 4.27.0, Mathlib, and all transitive dependencies. From a checkout
of this repository, run:

```sh
cd formalization
lake exe cache get
python3 scripts/verify.py --log-directory logs/local
```

The verifier runs `lake build`, executes the complete
`Audit.lean`, checks the theorem inventory and axiom allowlist,
and records source hashes and dependency revisions. For a fresh project
build using the pinned dependency cache:

```sh
python3 scripts/verify.py --fresh --log-directory logs/local
```

Our [GitHub Actions workflow](.github/workflows/lean.yml) performs the
build and audit on a GitHub-hosted Ubuntu runner. Each run publishes its
verification report, build log, and axiom output as an artifact.
The [results](formalization/RESULTS.md) and
[environment record](formalization/ENVIRONMENT.md) describe the recorded checks.

The standalone finite certificate can also be checked with Python 3.10+
from the repository root:

```sh
python3 certificate/check_templates.py
```

This checks all twelve chains symbolically on the whole cone $0<q<p<2q$.
The [finite regression suites](verification/README.md) are supplementary
tests, distinct from the Lean proof of the infinite statements.

## Scope and review

Our theorem addresses the irrational-ratio, base-$2$ statement and its
strong-completeness strengthening. Hegyvári's broader conjecture also
includes rational ratios other than powers of two; part (ii) asks about
a base in $(1,2)$. These are separate mathematical questions.

For mathematical discussion, please identify the relevant section or
Lean declaration and the revision examined in a
[repository issue](https://github.com/Andrewyzzz/erdos354/issues).

English is the primary language of the maintained exposition and documentation.
The [original English manuscript](proof/PROOF.md), its
[Chinese counterpart](proof/PROOF.zh-CN.md), and the
[frozen source](archive/FROZEN_20260912.zh-CN.md) preserve the development
record. Their preparation-time descriptions refer to those original versions.
[MANIFEST.sha256.json](MANIFEST.sha256.json) records the listed file hashes.

## Contributions

We used **Chatgpt-6 Astra** in both the mathematical derivation and the Lean
formalization, as detailed in [CREDITS.md](CREDITS.md).

## Licensing

We license our code and scripts under [Apache-2.0](LICENSE), and our
manuscripts and explanatory documentation under [CC BY 4.0](LICENSE-CC-BY-4.0).
Third-party materials retain their original licenses and notices.
[LICENSING.md](LICENSING.md) defines the component scope and attribution;
[NOTICE](NOTICE) records the project and upstream notices.
