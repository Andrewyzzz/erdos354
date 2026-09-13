# Review package and reproducibility

The repository is
[Andrewyzzz/erdos354](https://github.com/Andrewyzzz/erdos354).
Our primary review materials are:

- [English mathematical manuscript](../proof/FORMALIZED_PROOF.md).
- [Formal statement definitions](../formalization/Dyadic354/Statements.lean)
  and [final proofs](../formalization/Dyadic354/Main.lean).
- [Theorem map](../formalization/STATUS.md) and
  [verification records](../formalization/RESULTS.md).
- [Contribution and AI disclosure](../CREDITS.md).
- [Mathematical review summary](FORUM_POST.md).

For a stable reference, link the commit examined together with the manuscript
section or Lean declaration. The original manuscripts, certificate data,
and development records are preserved in the repository history.

## Release checks

From the repository root:

```sh
python3 verification/check_manifest.py
python3 certificate/check_templates.py
python3 formalization/scripts/check_publication.py
python3 formalization/scripts/sanitize_logs.py --check
python3 -m unittest discover -s formalization/scripts -p 'test_*.py' -v
cd formalization
lake exe cache get
python3 scripts/verify.py --log-directory logs/local
```

The [GitHub-hosted workflow](../.github/workflows/lean.yml) runs the release checks
and Lean verification. Each successful run provides a commit-labelled
artifact containing the build log, final statement output, all-theorem
axiom audit, and source hashes.

The current package uses English for its maintained exposition and
documentation. Original Chinese inputs are identified by `.zh-CN.md`.
The [public-log policy](../formalization/logs/REDACTION.md) records the
machine-path substitutions applied to historical logs.
