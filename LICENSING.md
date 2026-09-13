# Licensing

Copyright 2026 Andrewyzzz.

We license our original contributions under the component-specific terms
below, to the extent that we hold the relevant rights. Third-party
materials retain their existing licenses and notices.

## Scope

| Material | Applicable license |
|---|---|
| Our Lean source files, Python scripts, build and workflow configuration, and associated machine-readable certificate data | [Apache License 2.0](LICENSE) |
| Our mathematical manuscripts and explanatory documentation, including the English and Chinese Markdown texts | [Creative Commons Attribution 4.0 International](LICENSE-CC-BY-4.0) |
| Upstream-derived definitions, source snapshots, and other identified third-party material | Their original licenses and attribution notices |

This is a division by component, not a choice of two licenses for the same
material. The Apache-2.0 text in the root `LICENSE` applies to the software
components; it does not replace the CC BY 4.0 license for the prose.

### Software

Apache-2.0 applies to our software contributions throughout
`formalization/`, `certificate/`, `verification/`, `release/`, and
`.github/`. This includes `.lean` and `.py` files, project-authored
build and workflow configuration, and the certificate data in
`certificate/templates.json`. Code excerpts in our documentation are
also offered under Apache-2.0, separately from the surrounding prose.

The complete, unmodified license text is in [LICENSE](LICENSE).
[NOTICE](NOTICE) records attribution for our contributions and the
upstream definitions.

### Manuscripts and documentation

We license our mathematical exposition and explanatory prose under
CC BY 4.0. This includes:

- [The formalization-aligned English manuscript](proof/FORMALIZED_PROOF.md).
- The original English and Chinese manuscripts under `proof/` and our
  frozen manuscript under `archive/`.
- Our explanatory Markdown documents at the repository root and under
  `formalization/`, `verification/`, `review/`, and `release/`.

The complete, unmodified license text is in
[LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0). The official
[CC BY 4.0 summary](https://creativecommons.org/licenses/by/4.0/)
describes its permissions and attribution requirements.

For the manuscript, the attribution information is:

> *Erdős Problem 354(i): Strong Completeness of Two Dyadic Floor Sequences*,
> 2026. Source:
> [Andrewyzzz/erdos354](https://github.com/Andrewyzzz/erdos354).
> Licensed under CC BY 4.0. Copyright 2026 Andrewyzzz.

When sharing an adaptation, identify your changes and retain the required
attribution, license information, and supplied notices in accordance with
CC BY 4.0. Including the source revision helps readers identify the version
used. Our [contribution statement](CREDITS.md) records the AI system's role.

The license applies to the copyrightable expression of our work; we claim
no exclusive rights over mathematical facts or results. This scope statement
does not add restrictions to either standard license.

## Third-party materials

The definitions adapted or extracted from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/tree/a748dd915c908b21c4d864abf239f61049fa9d96)
retain the notice:

> Copyright 2025 The Formal Conjectures Authors.

Their Apache-2.0 license is preserved in
[formalization/LICENSE.upstream](formalization/LICENSE.upstream).
This includes the upstream-derived portions of
[Statements.lean](formalization/Dyadic354/Statements.lean), the extracted
[UpstreamDefinitions.lean](formalization/Dyadic354/UpstreamDefinitions.lean),
and the source snapshots under `formalization/upstream/`.
[UPSTREAM.md](formalization/UPSTREAM.md) identifies their exact provenance
and the local adaptations.

Third-party quotations, notices, and source excerpts retain their own
rights and terms; the CC BY 4.0 grant covers our contribution to the
surrounding prose. Verification logs and provenance records preserve the
attribution and licensing of any source material they reproduce.

Dependencies obtained through Lake, including Mathlib, retain their own
licenses. Their source and compiled caches are not included in this
repository. Neither this licensing statement nor our attribution notice
replaces a third-party license.

## Versioned sources

We apply these licenses through this repository-level statement without
rewriting the frozen proof inputs, upstream snapshots, or historical build
records. The licensing statement accompanies those files in this revision.
Earlier descriptions of the package's licensing status refer to their
preparation-time versions.

Canonical license texts:
[Apache-2.0](https://www.apache.org/licenses/LICENSE-2.0.txt) and
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/legalcode.txt).
