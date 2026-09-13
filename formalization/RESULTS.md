# Verification results

The frozen part-(i) and strong-completeness targets have passed the full
Lean build and transitive axiom audit locally and on a GitHub-hosted Ubuntu
runner. The local checks also include a fresh-source rebuild. We audit
all 381 local theorems.

## Mathematical conclusions

- `Dyadic354.erdos354_part_i : PartI`: for arbitrary positive real
  parameters with irrational ratio, every sufficiently large integer is
  a finite-index sum of the two interleaved dyadic floor sequences.
- `Dyadic354.erdos354_strong_completeness : StrongCompleteness`: after
  deleting any finite set of values from the original nonzero value set,
  every sufficiently large integer is a sum of distinct remaining values.
- `UpstreamBridge.erdos354_part_i_upstream` and
  `UpstreamBridge.erdos354_strong_upstream`: the corresponding conclusions
  in the exact extracted upstream definitions.

The final definitions are unchanged from the initial frozen statements.
The final theorems add no FE/DB/BG, normalization, event-spacing,
permanent-descent, or long-window hypotheses.

## Recorded local checks

| Check | Result |
|---|---|
| Full default build and all-theorem audit | PASS, 381 theorems; [report](logs/verification.json) |
| Fresh-source rebuild and repeated audit | PASS, 381 theorems; [report](logs/fresh-verification.json) |
| Source hashes and individual axiom sets in the two runs | Identical |
| Fresh directory versus delivery source comparison | Exit code 0; [log](logs/final-clean-source-match.log) |
| Original package integrity at the verification revision | All 36 listed hashes matched; [log](logs/eighth-batch-input-integrity.log) |
| Pinned upstream source and extracted definitions | Byte comparison and definition checks passed; [log](logs/upstream-provenance-online.log) |

The verified Lean source commit is
[59e5957](https://github.com/Andrewyzzz/erdos354/commit/59e5957ac8bf28623318cebec6c67b1a672ad49e).
Subsequent publication edits retain these Lean sources and their target
definitions. Historical reports identify the verification scripts used
at their recorded revisions.

Every theorem's transitive axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`.
The compiled project uses no `sorry`, custom axioms, or `native_decide`.
The actual final types and axiom dependencies appear in
[axioms.log](logs/axioms.log) and
[fresh-axioms.log](logs/fresh-axioms.log).

## Public reproducibility

The [public run at 038ec88](https://github.com/Andrewyzzz/erdos354/actions/runs/34732546472)
completed successfully on 13 September 2026. Its artifact reports PASS for
all 381 theorems on the clean commit
`038ec88d64a4fa815f73c4c7784862ba6ddabb87`. We checked the downloaded report
against the release sources: every Lean source hash and dependency-lock
hash agrees, and every reported axiom set satisfies the allowlist.

The [Lean verification workflow](https://github.com/Andrewyzzz/erdos354/actions/workflows/lean.yml)
runs the manifest and certificate checks, `lake exe cache get`,
`lake build`, and the complete axiom audit on a GitHub-hosted Ubuntu
runner. Each run attaches the actual build output and
`verification.json` in a commit-labelled artifact.

The workflow's audit rejects missing, duplicate, or additional theorem
records and every axiom outside the three-element allowlist. The report
records the exact commit, source hashes, platform, and CI run URL.

## Environment and exposition

We use Lean 4.27.0 and pinned Mathlib dependencies. The fresh local build
recompiles this project while reusing the pinned dependency cache.
The upstream adapter compiles the extracted definitions under this same
environment; [UPSTREAM.md](UPSTREAM.md) gives their provenance.

The [English manuscript](../proof/FORMALIZED_PROOF.md) follows the
formalized proof, including the good-rational crossing argument, FE
potential, and BG capacity estimate.
[STATUS.md](STATUS.md) maps its principal steps to Lean declarations.
[ENVIRONMENT.md](ENVIRONMENT.md) records toolchain and input hashes,
and the [README](README.md) gives reproduction commands.
