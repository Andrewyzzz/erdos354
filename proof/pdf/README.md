# Typeset manuscript

The [PDF](../FORMALIZED_PROOF.pdf) is generated directly from the
[English manuscript](../FORMALIZED_PROOF.md). There is no separately edited
mathematical text. The converter preserves the numbered equations and all
125 certificate nodes, and wraps the appendix table for print.

## Reproduction

Use Python 3.10 or later and Tectonic 0.16.9. From the repository root:

```sh
python3 proof/scripts/check_math.py
python3 proof/scripts/build_pdf.py \
  --build-dir /tmp/erdos354-pdf-build \
  --output proof/FORMALIZED_PROOF.pdf
```

The build directory receives the generated TeX, compiler log, and a JSON
record of the source and PDF hashes. Tectonic retrieves standard TeX
packages into its local cache when necessary. PDF metadata can vary between
builds; the source hash identifies the manuscript being typeset.

The [typesetting record](build-record.json) identifies the distributed PDF.
Its 90 display formulas, 405 inline formulas, and 23 equation labels have
been checked for delimiter and grouping integrity. The rendered pages have
been inspected for clipping, missing glyphs, and table overflow. The PDF
appendix reproduces all 125 mask triples in their original order.

GitHub uses fenced `math` blocks, protected inline delimiters, and explicit
relation and brace commands. Row breaks prevent Markdown from altering
alignment syntax. Equation labels remain inside the GitHub expression;
the PDF places them in the conventional right margin. The CI guard
checks these conventions and rejects a PDF whose recorded source hash no
longer matches the manuscript. Typesetting checks are distinct from the
[Lean build and axiom audit](../../formalization/RESULTS.md).
