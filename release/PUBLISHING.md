# Publishing this package without a preprint

Target repository: `https://github.com/Andrewyzzz/erdos354`.
Proposed version tag: `v0.1.0-candidate`.

This package is a repository release candidate, not an arXiv or journal submission.
The package's date does not claim that it was publicly uploaded on that date.

## Before linking from the forum

1. Upload the package to the intended repository and make sure the intended files
   are publicly readable. Do not disclose unrelated private research files.
2. Run `python3 verification/run_checks.py --full` from a clean checkout. Keep the
   revision note and frozen source. Do not label the run as a complete formal proof.
3. Confirm attribution, the precise part-(i) statement, and the repository's license
   policy. No license has been imposed by the package-preparation step.
4. Freeze the public version with an actual commit/tag. Link a fixed revision when
   requesting review; do not silently rewrite a version under discussion.
5. Post the short draft in `FORUM_POST.md` once, in the appropriate Problem 354
   discussion/submission location. Follow the site's current account/comment rules.

The website's current posting form and moderation requirements could not be checked
in the preparation session: the problem and forum pages returned HTTP 403. The
community guidance linked below recommends doing due diligence, sharing relevant
links and a summary, and allowing the community to evaluate the submission. It is
not a promise of an unmoderated post or automatic recognition as solved.

No forum post was made by creating this package. No arXiv submission or GitHub
release/tag should be described as completed unless its actual public URL exists.

## Upload from a local authenticated Git checkout

The optional helper `publish_to_github.py` requires only Python and Git. It clones
the exact target repository into a **new** local directory, checks for conflicting
files, and prepares a commit. It never force-pushes, changes visibility, creates
an account, changes permissions, deletes remote files, or bypasses branch protection.
It refuses to overwrite a differing remote file.

```sh
python3 release/publish_to_github.py --destination ../erdos354-upload
# Inspect the staged changes/commit, then upload with:
python3 release/publish_to_github.py --destination ../erdos354-upload --push
```

Your local Git must already have access to `Andrewyzzz/erdos354`; no credentials
are included in this package. When using the connected GitHub app instead, ensure
that this exact repository is included in its authorized repositories.

## Guidance sources checked during preparation

- GitHub REST troubleshooting, including 404 responses for inaccessible private
  repositories: https://docs.github.com/en/rest/using-the-rest-api/troubleshooting-the-rest-api
- Erdős-project community guidance (page says last updated 30 June 2026):
  https://github.com/teorth/erdosproblems/wiki/What-to-do-when-I-think-I-managed-to-get-AI-to-solve-an-Erd%C5%91s-problem%3F
- Target problem: https://www.erdosproblems.com/354

The community wiki is guidance, not a verified statement of the website's current
moderation policy. A public claim and an accepted solution remain different states.
