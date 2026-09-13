# Contributions and AI disclosure

Project contributors: **Andrewyzzz and Chatgpt-6 Astra (AI system)**.

## Mathematical development

We used Chatgpt-6 Astra throughout the mathematical development, including
the exploration of proof strategies, derivation of intermediate arguments,
construction of finite certificates, examination of objections, and revision
of the exposition. Its contribution was substantive and extended beyond
language editing.

## Lean formalization

We also used Chatgpt-6 Astra to develop the Lean proofs, formulate auxiliary
lemmas, adapt the mathematical arguments to the library interfaces, and
iterate on the code through compilation and correction. We used the same
model to develop the verification scripts and to prepare the English
documentation and its correspondence with the formal proof.

We verify the resulting declarations with Lean 4.27.0 and the pinned
dependencies. The complete theorem inventory, source hashes, compilation
logs, and transitive axiom audits are described in
[the verification record](formalization/RESULTS.md).

## Responsibility and attribution

Andrewyzzz is the human maintainer and responsible contact for this work,
including its mathematical presentation, software, and responses to review.
Chatgpt-6 Astra is identified as an AI system in our contributor attribution.
Contact: [Andrewyzzz on GitHub](https://github.com/Andrewyzzz).

The upstream-derived definitions retain the attribution and Apache 2.0
notice of The Formal Conjectures Authors; see
[definition provenance](formalization/UPSTREAM.md) and
[LICENSE.upstream](formalization/LICENSE.upstream).
