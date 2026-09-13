#!/usr/bin/env python3
"""Guard the manuscript's GitHub-safe math delimiters and TeX grouping.

This is a typesetting check, not a mathematical proof checker. TeX compilation
and visual inspection remain part of the PDF production workflow.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

SOURCE = Path(__file__).resolve().parents[1] / 'FORMALIZED_PROOF.md'


def check(source: str) -> dict:
    blocks = re.findall(r'^```math\n(.*?)\n```$', source, re.M | re.S)
    remainder = re.sub(r'^```math\n.*?\n```$', '', source, flags=re.M | re.S)
    inlines = re.findall(r'\$`([^`\n]+)`\$', remainder)
    remainder = re.sub(r'\$`[^`\n]+`\$', '', remainder)
    if '$' in remainder or '```math' in remainder:
        raise ValueError('Unprotected, multiline, or unclosed math delimiters')
    for index, formula in enumerate(blocks + inlines, 1):
        if re.search(r'\\\\\s*\n', formula):
            raise ValueError(f'Formula {index}: use an explicit [0pt] row break to avoid Markdown escaping')
        if '$' in formula or r'\operatorname' in formula:
            raise ValueError(f'Formula {index}: unsupported macro or nested dollar delimiter')
        depth = 0
        for match in re.finditer(r'\\.|[{}]', formula):
            token = match.group()
            if token == '{':
                depth += 1
            elif token == '}':
                depth -= 1
            if depth < 0:
                raise ValueError(f'Formula {index}: unmatched closing brace')
        if depth:
            raise ValueError(f'Formula {index}: unmatched opening brace')
        environments = []
        for command, name in re.findall(r'\\(begin|end)\{([^}]+)\}', formula):
            if command == 'begin':
                environments.append(name)
            elif not environments or environments.pop() != name:
                raise ValueError(f'Formula {index}: mismatched math environment')
        if environments:
            raise ValueError(f'Formula {index}: unclosed math environment')
    tags = re.findall(r'\\tag\{([^}]+)\}', source)
    if len(tags) != len(set(tags)):
        raise ValueError('Repeated equation labels')
    if not blocks or not inlines:
        raise ValueError('Missing math content')
    return {'displays': len(blocks), 'inline_formulas': len(inlines), 'equation_labels': len(tags)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-pdf', action='store_true')
    args = parser.parse_args()
    counts = check(SOURCE.read_text())
    print('PASS: GitHub math delimiters and TeX grouping:', counts)
    if args.check_pdf:
        record = json.loads((SOURCE.parent / 'pdf/build-record.json').read_text())
        for path, key in [(SOURCE, 'source_sha256'),
                          (SOURCE.with_suffix('.pdf'), 'pdf_sha256')]:
            if hashlib.sha256(path.read_bytes()).hexdigest() != record[key]:
                raise SystemExit(f'{path.name}: stale PDF or build record')
        if counts['displays'] != record['display_formulas'] or counts['inline_formulas'] != record['inline_formulas']:
            raise SystemExit('Formula counts differ from the PDF build record')
        print('PASS: PDF and manuscript hashes match the recorded typesetting build.')
