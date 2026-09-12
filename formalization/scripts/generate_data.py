"""Translate the original JSON to Lean data; all mathematical claims are checked in Lean.

The supplied lo/hi fields are untrusted witnesses. EndpointsCheck verifies them
against coefficients recomputed from the masks, including their cone order.
"""
import argparse
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = root.parent / 'certificate' / 'templates.json'
target = root / 'Dyadic354' / 'CertificateData.lean'


def pair(values):
    return '(' + ', '.join('true' if x else 'false' for x in values) + ')'


def generate():
    raw = source.read_bytes()
    records = json.loads(raw)
    lines = [
        '/- Generated from certificate/templates.json by scripts/generate_data.py.',
        'Input SHA-256: ' + hashlib.sha256(raw).hexdigest(),
        'Endpoint witnesses are verified against masks by the Lean checker. -/',
        'import Dyadic354.Certificate',
        '',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 8000000',
        '',
        'namespace Dyadic354.Certificate',
        '',
    ]
    for i, row in enumerate(records):
        assert len(row['first']) == len(row['second']) == 2
        assert all(x in (0, 1) for x in row['first'] + row['second'])
        lines.extend([
            f'def template_{i} : Template :=',
            '  ⟨' + pair(row['first']) + ', ' + pair(row['second']) + ', [',
        ])
        for j, node in enumerate(row['chain']):
            vals = [node['mask0'], node['mask1'], node['third_mask']]
            assert all(type(x) is int for x in vals + node['lo'] + node['hi'])
            entry = ', '.join(map(str, vals))
            entry += ', ⟨' + ', '.join(map(str, node['lo'])) + '⟩'
            entry += ', ⟨' + ', '.join(map(str, node['hi'])) + '⟩'
            lines.append('    ⟨' + entry + '⟩' + (',' if j + 1 < len(row['chain']) else ''))
        lines.extend(['  ]⟩', ''])
    lines.extend([
        'def templates : List Template :=',
        '  [' + ', '.join(f'template_{i}' for i in range(len(records))) + ']',
        '',
        'theorem certificate_checked : checkCertificate templates = true := by',
        '  decide +kernel',
        '',
        'theorem certificate_correct : MathematicallyCorrect templates :=',
        '  checkCertificate_sound templates certificate_checked',
        '',
        'theorem all_templates_checked : ∀ t ∈ templates, ChainChecks t := by',
        '  decide +kernel',
        '',
        'theorem all_templates_correct (t : Template) (ht : t ∈ templates)',
        '    (p q : ℤ) (hqp : q < p) (hpq : p < 2*q) : ChainMeaning t p q :=',
        '  chain_sound t (all_templates_checked t ht) p q hqp hpq',
        '',
        'theorem certificate_counts : templates.length = 12 ∧',
        '    (templates.map (fun t => t.chain.length)).sum = 125 ∧',
        '    (templates.map (fun t => t.chain.length - 1)).sum = 113 := by',
        '  decide +kernel',
        '',
        'end Dyadic354.Certificate',
        '',
    ])
    return '\n'.join(lines)


parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
expected = generate()
if args.check:
    if not target.exists() or target.read_text() != expected:
        raise SystemExit('Generated Lean data differs from the original JSON translation.')
    print('PASS: Lean certificate data exactly matches the original JSON translation.')
else:
    target.write_text(expected)
    print(target)
