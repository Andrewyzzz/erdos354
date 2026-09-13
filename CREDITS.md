# AI assistance and provenance

This work was developed with assistance from ChatGPT and OpenAI Codex, using GPT-6 (Astra).

## Mathematical development

We used these systems throughout the mathematical development, including
the exploration of proof strategies, derivation of intermediate arguments,
construction of finite certificates, examination of objections, and revision
of the exposition. Their contribution was substantive and extended beyond
language editing.

## Lean formalization

We also used these systems to develop the Lean proofs, formulate auxiliary
lemmas, adapt the mathematical arguments to the library interfaces, and
iterate on the code through compilation and correction. We used them
to develop the verification scripts and to prepare the English
documentation and its correspondence with the formal proof.

We verify the resulting declarations with Lean 4.27.0 and the pinned
dependencies. The complete theorem inventory, source hashes, compilation
logs, and transitive axiom audits are described in
[the verification record](formalization/RESULTS.md).

## Upstream attribution

The upstream-derived definitions retain the attribution and Apache 2.0
notice of The Formal Conjectures Authors; see
[definition provenance](formalization/UPSTREAM.md) and
[LICENSE.upstream](formalization/LICENSE.upstream).

## Licensing

We license our software contributions under
[Apache-2.0](LICENSE), and our manuscripts and explanatory documentation
under [CC BY 4.0](LICENSE-CC-BY-4.0), to the extent that we hold the relevant
rights. Third-party rights and notices are preserved.
The component scope and manuscript attribution are specified in
[LICENSING.md](LICENSING.md) and [NOTICE](NOTICE).
