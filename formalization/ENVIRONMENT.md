# Verification environment

We record the toolchain, dependency revisions, and source provenance used
to verify the formalization. Local verification was performed on
13 September 2026; command logs use UTC.

## Toolchain and dependencies

| Component | Recorded version |
|---|---|
| Lean | 4.27.0 |
| Lean commit | `db93fe1608548721853390a10cd40580fe7d22ae` |
| Lake | `5.0.0-src+db93fe1` |
| Mathlib | `a3a10db0e9d66acbebf76c5e6a135066525ac900` |
| Local host | macOS 26.5.1, Apple Silicon / arm64 |
| Public CI runner | GitHub-hosted Ubuntu 24.04 |

[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json) fix the project environment.
The manifest pins nine dependencies. The verifier checks each actual
dependency Git revision against the manifest and requires clean tracked
dependency sources.

The local project uses an existing cache of the same pinned dependencies.
Its cache link is excluded by Git. Fresh checkouts obtain the dependencies
with `lake exe cache get`; no machine-specific path is required by the
project configuration.

## Frozen mathematical inputs

| File | SHA-256 |
|---|---|
| Original English manuscript, `proof/PROOF.md` | `8662891ac64f4ed2805a889d087afc7848667b1519192bf368ebdefba30bbdd2` |
| Original Chinese manuscript, `proof/PROOF.zh-CN.md` | `a424bb9c470e0303bf9529add146911c1b2717375ecb458b4a0cafae450aa618` |
| Certificate, `certificate/templates.json` | `3293a4fb061ba625ba1f11788dca751920a182d26d60d6298b31a058c065c048` |
| Certificate checker, `certificate/check_templates.py` | `862b5ddbb55d134336029977961c4cf0391ff67024f2946b039ca584cab1b98d` |
| Frozen targets, `Dyadic354/Statements.lean` | `623b20bab06c99013dcbefed752aa80ce29a879930eefc1d069e4944bc5ceb0e` |

The [current English exposition](../proof/FORMALIZED_PROOF.md) describes the
formalized argument, including its proved alternatives to the original
manuscript. Its hash is recorded separately in the repository manifest.
The original manuscripts and certificate retain the bytes listed above.

## Build and audit records

The complete Lean proof was recorded at source commit
[59e5957](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e).
The ordinary and fresh-source checks audit all 381 local theorems:

- [Ordinary build report](logs/verification.json),
  [build output](logs/build.log), and [axiom output](logs/axioms.log).
- [Fresh-source report](logs/fresh-verification.json),
  [build output](logs/fresh-build.log), and [axiom output](logs/fresh-axioms.log).
- [Fresh-source comparison](logs/final-clean-source-match.log).
- [Pinned upstream provenance check](logs/upstream-provenance-online.log).

The fresh-source build uses a new project directory and the pinned Mathlib
dependency cache. It compiles our sources without reusing our project
artifacts. Both local reports record identical source hashes and
individual theorem axiom dependencies.

The [public workflow](../.github/workflows/lean.yml) installs the pinned
toolchain, retrieves the dependency cache, builds the project, and runs
the complete audit. Its artifact includes the actual source commit,
platform, source hashes, dependency revisions, and CI run URL.
See [RESULTS.md](RESULTS.md) for the verification record.

## Provenance of development logs

The logs preserve compilation and correction iterations from all eight
development batches, followed by the complete build and fresh-source
audit. Earlier failure records retain their diagnostic context and exit
status; the acceptance reports identify the completed builds.

The historical input-integrity logs refer to the listed package files at
their recorded revisions. Later documentation changes are tracked in Git
and in the updated repository manifest. Source hashes within historical
reports continue to identify the scripts and Lean files used for those runs.

We publish logs with machine-local paths replaced by symbolic locations.
The [redaction record](logs/REDACTION.md) describes this formatting
transformation and preserves the provenance of the original records.
