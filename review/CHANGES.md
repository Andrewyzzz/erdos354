# Post-review clarification record

Version: v0.1.0-candidate. Original frozen proof date: 12 September 2026.

This release incorporates clarifications into the complete proof rather than
asking readers to reconstruct it from review discussions. The original source is
preserved unchanged. The Chinese text diff is [`revision.patch`](revision.patch).
The English proof is a new rendering of the same argument, not an independently
reviewed second proof.

## Incorporated

1. Define events by the **arrival layer**: an event at `t` is
   `(u[t-1],v[t-1]) != (0,0)`. Explicitly distinguish the elements in `P_n` from
   the last conversion counted by `K_n`.
2. Prove normalization using nonnegative upward shifts of each sequence, followed
   by a common upward shift. No arbitrary real or downward scaling is used.
3. Prove that an irrational ratio forces infinitely many joint events.
4. Give the two endpoint points proving the wraparound case of mesh projection.
5. Display the full arithmetic giving `64d-42 >= 22d`, including `d=1`.
6. Define the permanent object `W_t = W + P(a_i,b_i : r <= i < t)` and its span
   and gap invariants explicitly.
7. Explain why `m-n` exact pairs and update depth `m+3` follow from arrival indices.
8. Check the last point of the FE nonwrapping range against the **new** period.
9. Expand the final single-event error and the weighted geometric-series sum in FE.
10. Spell out finite coefficient legality in DB, and the strict integer rounding
    from `R_n < 2 DeltaK + 5` to `R_n <= 2 DeltaK + 4`.
11. Expand the whole-window nonexact-layer count as `h K_T + h`, explicitly paying
    the final `h` layers.

## Proposed numerical changes not adopted

| Suggestion | Decision and reason |
|---|---|
| Replace `64d-42` by `64d-44` | Not needed: integer `S <= d(p+q)-1` supplies the missing 2. |
| Replace the first `2b` terms by `2b-1` | Not correct for this proof: the relevant period is `2L+1+v`, and the last point is `2L`, still inside it. |
| Replace the DB constant `+4` by `+5` | Not needed: the preceding inequality is strict and `R_n` is an integer. |
| Shift the whole update from `m+3` to `m+4` | Not adopted: the explicit arrival-layer convention matches the original formulas. |
| Restrict exact-layer choices to `[0,T-h]` | Not needed: the error budget already includes the final `h` layers. |

No main theorem is added beyond the frozen candidate's claim. The appendix mask
chains and legacy mathematical verifier code are unchanged. A portable runner and
second certificate implementation have been added. Historical run logs are separate
from fresh release runs.

The supplied reports were scoped reviews, not formal certification. No claim is
made that their original private checkers were reproduced as part of this release.
