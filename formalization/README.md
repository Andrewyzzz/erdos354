# Lean formalization of Erdős Problem 354(i)

We prove indexed completeness and strong set completeness for two dyadic
floor sequences with arbitrary positive real parameters and irrational ratio:

```lean
Dyadic354.erdos354_part_i : Dyadic354.PartI
Dyadic354.erdos354_strong_completeness : Dyadic354.StrongCompleteness
```

The [English manuscript](../proof/FORMALIZED_PROOF.md) gives the mathematical
argument. The [theorem map](STATUS.md) identifies the main formal declarations,
and [RESULTS.md](RESULTS.md) records the builds and axiom audits.

## Statements and representations

We freeze the targets in [Statements.lean](Dyadic354/Statements.lean).
The sequences take values in the integers and have base exactly 2.

- `PartI` represents every sufficiently large integer using a finite set
  of natural-number indices. Each index occurs at most once.
- `StrongCompleteness` deletes an arbitrary finite set of values from
  the original nonzero value set and represents every sufficiently large
  integer as a sum of distinct remaining values.

The [final proofs](Dyadic354/Main.lean) have precisely the positivity and
irrational-ratio hypotheses in these definitions. Normalization, FE, DB, BG,
permanent descent, and the existence of the required windows are proved
dependencies. Our [upstream adapter](UPSTREAM.md) proves the positive
part-(i) target using seven verbatim extracted definitions.

## Reproduction

With Lean's Elan toolchain manager, Git, and Python 3.10+ available, run
from the repository root:

```sh
cd formalization
lake exe cache get
python3 scripts/verify.py --log-directory logs/local
```

The core Lean commands executed by the verifier are:

```sh
lake build
lake env lean Dyadic354/Audit.lean
```

To rebuild the project in a new source directory and repeat the audit:

```sh
python3 scripts/verify.py --fresh --log-directory logs/local
```

The fresh build reuses the pinned dependency cache and rebuilds our project
sources without reusing our compiled artifacts. Local output under
`logs/local/` is ignored by Git. The toolchain, Lake configuration, and
all nine dependency revisions are fixed; [ENVIRONMENT.md](ENVIRONMENT.md)
records their provenance.

## GitHub-hosted build

Our [GitHub Actions workflow](../.github/workflows/lean.yml) runs on a
GitHub-hosted Ubuntu 24.04 runner. It checks the package manifest and finite
certificate, installs the pinned toolchain, executes `lake exe cache get`,
and runs the verifier, including `lake build` and the complete axiom audit.
No compiled artifacts of this project are restored from a prior run.

Each run publishes a `lean-verification-<commit>` artifact containing
the environment record, build output, axiom output, and
`verification.json`. The report identifies the source commit, source
hashes, platform, dependency-cache policy, and CI run URL.

## Verification criteria

The default root module imports the entire proof chain and
[Audit.lean](Dyadic354/Audit.lean). We audit every one of the 381 local
theorems, including the two final theorems and both upstream conclusions.
The verifier requires:

1. An unchanged frozen statement file and a complete, duplicate-free theorem inventory.
2. Successful source generation checks, upstream definition checks, and
   agreement between all actual dependency revisions and the lockfile.
3. Successful compilation of the root target and a separate execution of the audit.
4. Exactly one axiom record for each audited theorem, with dependencies
   contained in `{propext, Classical.choice, Quot.sound}`.

Missing records, extra records, duplicate records, unapproved axioms, or
failed commands cause a nonzero exit. A previous PASS report is cleared
before a new run begins. We also scan the compiled project sources for
placeholders and mechanisms excluded by our verification policy.

The certificate is evaluated by `decide +kernel`. Its generic soundness
theorem proves the mathematical meaning of acceptance for all
`0 < q < p < 2*q`; it does not extrapolate from finitely many sampled
ratios. The project uses no `sorry`, custom axioms, or `native_decide`.

The [release-guard tests](scripts/test_release_checks.py) exercise rejection
of missing and malformed audit output, disallowed axioms, duplicate entries,
and missing final targets. They also test public-log path substitutions.

## Proof organization

| Component | Main sources |
|---|---|
| Frozen definitions and finite subset sums | Statements, Basic |
| Twelve coefficient chains and soundness | CertificateData, Certificate |
| Cyclic gaps and finite meshes | CyclicGaps, Mesh, CoefficientInterval |
| Legal representations and initial mesh | Representations, NodeRepresentations, InitialMesh |
| Actual floor sequences and permanent descent | FloorSequence, PairReindex, ExactBlock, PermanentMesh, FloorDescent, BlockLength |
| Completeness and event spacing | UnitMesh, LowGap, EventGaps, EventInfinitude |
| Prefix bounds and FE | PrefixMesh, PrefixBounds, FECounting, FEMissingRuns, FEShift, PeriodChange, EventBoundary, FERecurrence, EventDecay, FE, FER |
| Finite coefficient windows and DB | DBPhases, DBWindows, DBDigits, DBCover, DB |
| Rational windows and BG | RationalWindows, CubicGrowth, DBScale, BGWindowBounds, BGWindows, BGExactLayers, BGSparseCompact, BGBinaryRatio, BGReturns, BGGeometric, BGCapacity, BG |
| Original-parameter and upstream conclusions | Normalization, SetBridge, Main, UpstreamDefinitions, UpstreamBridge |

The [theorem map](STATUS.md) also records the precise alternatives to the
original manuscript: a generous block-length constant, well-founded
descent, an FE potential, good rational crossings, direct interval coverage,
and the geometric capacity estimate. These arguments are included in the
current English exposition.

## Records

[RESULTS.md](RESULTS.md) links the acceptance records.
Historical compilation logs retain the development iterations and complete
diagnostics; their mathematical content and exit statuses are preserved.
Machine-local paths are replaced by symbolic locations according to the
[public-log policy](logs/REDACTION.md).

## Licensing

We license our Lean code and verification scripts under
[Apache-2.0](../LICENSE), and our explanatory documentation under
[CC BY 4.0](../LICENSE-CC-BY-4.0). Upstream-derived definitions retain
their existing Apache-2.0 notice. See [LICENSING.md](../LICENSING.md)
for the scope and [NOTICE](../NOTICE) for attribution.
