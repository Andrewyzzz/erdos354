#!/usr/bin/env python3
"""Build the review PDF from FORMALIZED_PROOF.md, without a second manuscript.

Requires Tectonic 0.16.9. The converter supports the deliberately small
Markdown subset used by this manuscript and rejects unexpected constructs.
No Lean source is read or modified by the typesetter.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

PROOF = Path(__file__).resolve().parents[1]
SOURCE = PROOF / 'FORMALIZED_PROOF.md'
ROOT = PROOF.parent
REPO_URL = 'https://github.com/Andrewyzzz/erdos354/blob/main/'


def escape(text: str) -> str:
    replacements = {
        '\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
        '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
        '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
        '∎': r'\(\square\)', '§': r'\S{}', '–': '--', '—': '---',
        '−': '-', '‑': '-', '→': r'\(\to\)',
    }
    return ''.join(replacements.get(c, c) for c in text)


def link_url(target: str) -> str:
    if target.startswith(('https://', 'http://')):
        return target
    path, _, anchor = target.partition('#')
    relative = (PROOF / path).resolve().relative_to(ROOT).as_posix()
    return REPO_URL + relative + ('#' + anchor if anchor else '')


INLINE = re.compile(r'\$`([^`]+)`\$|`([^`]+)`|\[([^\]]+)\]\(([^)]+)\)|\*\*([^*]+)\*\*')


def inline(text: str) -> str:
    pieces = []
    end = 0
    for match in INLINE.finditer(text):
        pieces.append(escape(text[end:match.start()]))
        math, code, label, target, bold = match.groups()
        if math is not None:
            pieces.append(r'\(' + math + r'\)')
        elif code is not None:
            pieces.append(r'\texttt{' + escape(code) + '}')
        elif label is not None:
            pieces.append(r'\href{' + link_url(target).replace('%', r'\%') + '}{' + inline(label) + '}')
        else:
            pieces.append(r'\textbf{' + inline(bold) + '}')
        end = match.end()
    pieces.append(escape(text[end:]))
    return ''.join(pieces)


def table(lines: list[str]) -> str:
    rows = [[cell.strip() for cell in line.strip().strip('|').split('|')] for line in lines]
    assert set(''.join(rows[1])) <= set('-: '), 'Malformed table separator'
    if len(rows[0]) == 2:
        spec = r'@{}>{\raggedright\arraybackslash}p{0.34\linewidth}>{\raggedright\arraybackslash}p{0.62\linewidth}@{}'
        body = [r' & '.join(inline(c) for c in row) + r' \\[5pt]' for row in rows[2:]]
    else:
        assert rows[0] == ['First digits', 'Second digits', 'Complete mask chain']
        assert len(rows[2:]) == 12
        spec = r'@{}p{0.12\linewidth}p{0.13\linewidth}p{0.69\linewidth}@{}'
        body = []
        for first, second, raw_chain in rows[2:]:
            chain = ast.literal_eval(raw_chain.strip('`'))
            assert all(isinstance(t, tuple) and len(t) == 3 for t in chain)
            chunks = [chain[i:i+4] for i in range(0, len(chain), 4)]
            chain_tex = r'\newline '.join(
                r'\(' + r',\;'.join('(' + ','.join(map(str, triple)) + ')' for triple in chunk) + r'\)'
                for chunk in chunks
            )
            body.append(inline(first) + ' & ' + inline(second) + ' & ' + chain_tex + r' \\[6pt]')
    if len(rows[0]) == 3:
        header = r'\shortstack[l]{\textbf{First}\\\textbf{digits}} & \shortstack[l]{\textbf{Second}\\\textbf{digits}} & \textbf{Complete mask chain} \\ \midrule'
    else:
        header = ' & '.join(r'\textbf{' + escape(c) + '}' for c in rows[0]) + r' \\ \midrule'
    return '\n'.join([
        r'{\small\setlength{\tabcolsep}{4pt}',
        r'\begin{longtable}{' + spec + '}', r'\toprule', header,
        r'\endfirsthead', r'\toprule', header, r'\endhead',
        r'\bottomrule\endfoot', *body, r'\end{longtable}}',
    ])


def convert(source: str) -> tuple[str, dict]:
    lines = source.splitlines()
    assert lines[0].startswith('# ')
    title, authors, date = lines[0][2:], lines[2], lines[4]
    parts = [r'\title{' + escape(title) + '}', r'\author{' + escape(authors) + '}',
             r'\date{' + escape(date) + '}', r'\maketitle']
    i, display_count, paragraph_count, table_count = 6, 0, 0, 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line == '```math':
            j = i + 1
            while j < len(lines) and lines[j] != '```':
                j += 1
            assert j < len(lines), 'Unclosed math fence'
            formula = '\n'.join(lines[i+1:j])
            assert '$' not in formula, 'Nested math delimiters'
            parts.append('\\[\n' + formula + '\n\\]')
            display_count += 1
            i = j + 1
            continue
        if line.startswith('```'):
            raise ValueError('Unexpected code block')
        if line.startswith('## '):
            heading = line[3:]
            if heading.startswith(('12. Correspondence', 'Appendix A.')):
                parts.append(r'\clearpage')
            parts += [r'\section*{' + inline(heading) + '}',
                      r'\addcontentsline{toc}{section}{' + escape(heading) + '}']
            i += 1
            continue
        if line.startswith('### '):
            parts.append(r'\subsection*{' + inline(line[4:]) + '}')
            i += 1
            continue
        if line.startswith('|'):
            j = i + 1
            while j < len(lines) and lines[j].startswith('|'):
                j += 1
            parts.append(table(lines[i:j]))
            table_count += 1
            i = j
            continue
        if re.match(r'\d+\. ', line):
            items = []
            while i < len(lines) and lines[i].strip():
                match = re.match(r'\d+\. (.*)', lines[i])
                if match:
                    items.append(match[1])
                else:
                    assert lines[i].startswith('   ')
                    items[-1] += ' ' + lines[i].strip()
                i += 1
            parts += [r'\begin{enumerate}[leftmargin=*,itemsep=4pt]',
                      *(r'\item ' + inline(item) for item in items), r'\end{enumerate}']
            continue
        paragraph = [line.strip()]
        i += 1
        while i < len(lines) and lines[i].strip():
            assert not lines[i].startswith(('```', '#', '|')), 'Missing paragraph separator'
            paragraph.append(lines[i].strip())
            i += 1
        text = ' '.join(paragraph)
        assert '$' not in INLINE.sub('', text), 'Unprotected inline formula'
        parts.append(inline(text) + '\n')
        paragraph_count += 1
    body = '\n\n'.join(parts)
    # Keep an introductory sentence in the same TeX paragraph as its display,
    # so a page cannot end with an isolated "Set" or "Then".
    body = re.sub(r'\n{2,}(?=\\\[)', '\n', body)
    return body, {
        'display_formulas': display_count,
        'inline_formulas': len(re.findall(r'\$`[^`]+`\$', source)),
        'paragraphs': paragraph_count, 'tables': table_count,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tex-only', action='store_true')
    args = parser.parse_args()
    source = SOURCE.read_text()
    body, counts = convert(source)
    args.build_dir.mkdir(parents=True, exist_ok=True)
    tex_path = args.build_dir / 'FORMALIZED_PROOF.tex'
    preamble = (PROOF / 'pdf/preamble.tex').read_text()
    digest = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    tex_path.write_text('% Manuscript SHA-256: ' + digest + '\n' + preamble + '\n' + body + '\n\\end{document}\n')
    report = {'source': 'proof/FORMALIZED_PROOF.md', 'source_sha256': digest, **counts}
    if not args.tex_only:
        engine = shutil.which('tectonic')
        if not engine:
            raise SystemExit('Tectonic is required; no PDF was produced.')
        command = [engine, '--keep-logs', '--keep-intermediates', '--outdir', str(args.build_dir), str(tex_path)]
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(result.stdout)
        (args.build_dir / 'build-console.log').write_text(result.stdout)
        if result.returncode:
            raise SystemExit(result.returncode)
        log = (args.build_dir / 'FORMALIZED_PROOF.log').read_text()
        if re.search(r'Overfull|Missing character|Undefined control sequence', log):
            raise SystemExit('Typesetting defect detected; inspect the TeX log before distributing a PDF.')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.build_dir / 'FORMALIZED_PROOF.pdf', args.output)
        report['pdf_sha256'] = hashlib.sha256(args.output.read_bytes()).hexdigest()
        report['tectonic'] = subprocess.check_output([engine, '--version'], text=True).strip()
    (args.build_dir / 'build-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
