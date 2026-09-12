# Suggested post: Candidate proof of part (i) — two dyadic floor sequences

**Posting instruction (do not include this instruction in the post):** first verify
that the repository is public and the proof/checker links can be opened while logged
out. Post once in the existing Problem 354 discussion or the site's appropriate
claim-submission interface, following the current comment policy. The text below
is a draft, not evidence of a submitted or accepted forum post. No statement that
moderation is unnecessary has been verified.

---

I am sharing a complete **candidate proof of part (i)** for independent checking:

https://github.com/Andrewyzzz/erdos354

The precise claim is that, for all positive real numbers $\alpha,\beta$ with
$\alpha/\beta\notin\mathbb Q$, the set
$\{\lfloor2^n\alpha\rfloor,\lfloor2^n\beta\rfloor:n\ge0\}\setminus\{0\}$
is strongly complete. The base is fixed at 2; this is separate from the choice-of-base
question in part (ii).

The repository includes full English and Chinese Markdown proofs, the original
frozen version, an explicit finite coefficient certificate, a separately implemented
certificate checker, and reproducible finite regression tests.

The central step constructs an actual integer mesh after a sufficiently long exact
block. Its improved maximum gap persists through every future weight and hence
bounds missing runs modulo changing endpoint gcds. This gives finite descent unless
event-position ratios are eventually bounded. A second argument, using a finite-event
decay estimate, digit-budget propagation, and continued-fraction return costs,
rules out the bounded-ratio case for irrational $\alpha/\beta$.

The main points I would especially appreciate having challenged are Sections 3.2–5
(window coverage and permanence) and Section 8.1 (the changing-period estimate),
as well as the event-index and same-parameter interfaces.

The work was developed by Andrewyzzz with substantial assistance from Chatgpt-6 Astra.
The finite symbolic certificate is machine-checked, but the **whole proof is not
Lean-formalized, peer reviewed, or claimed to be independently professionally
certified**. The included finite tests do not prove the infinite theorem. I would
welcome an explicit counterexample, the earliest false lemma, or a precise missing
implication. Please state the scope of any review.
