"""Fail-closed checks for the project's explicit Lean axiom audit.

This parser is a release guard, not an independent theorem prover. Lean checks
the proof terms; this module checks the declared inventory and reported axioms.
"""
import re

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
TARGETS = frozenset({
    'Dyadic354.erdos354_part_i',
    'Dyadic354.erdos354_strong_completeness',
    'Dyadic354.UpstreamBridge.erdos354_part_i_upstream',
    'Dyadic354.UpstreamBridge.erdos354_strong_upstream',
})


def inventory(sources, audit_source):
    """Check the inventory against this project's top-level theorem syntax."""
    entries = re.findall(r'^#print axioms (\S+)\s*$', audit_source, re.M)
    expected = set(entries)
    if len(entries) != len(expected):
        raise ValueError('Duplicate declaration in the audit inventory')
    if not TARGETS <= expected:
        raise ValueError('The audit inventory omits a final target')
    for target in TARGETS:
        if not re.search(r'^#print ' + re.escape(target) + r'\s*$', audit_source, re.M):
            raise ValueError(f'Final target type is not printed: {target}')
    declared = set()
    for source in sources:
        namespaces = []
        for line in source.splitlines():
            if match := re.match(r'^namespace ([\w.]+)\s*$', line):
                namespaces.append(match[1])
            elif re.match(r'^end(?:\s+[\w.]+)?\s*$', line):
                if namespaces:
                    namespaces.pop()
            elif match := re.match(r'^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)', line):
                declared.add('.'.join(namespaces + [match[1]]))
    if declared != expected:
        raise ValueError('Audit inventory mismatch: '
                         f'missing={sorted(declared-expected)}, '
                         f'extra={sorted(expected-declared)}')
    return expected


def check_output(output, expected):
    if not expected or not TARGETS <= expected:
        raise ValueError('Empty audit or missing final targets')
    pattern = (r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
               r'does not depend on any axioms)\s*$')
    records = {}
    for match in re.finditer(pattern, output, re.M):
        name, axioms = match.groups()
        if name in records:
            raise ValueError(f'Duplicate axiom output: {name}')
        records[name] = {x.strip() for x in (axioms or '').split(',') if x.strip()}
    missing = expected - records.keys()
    extra = records.keys() - expected
    bad = {name: sorted(axioms - ALLOWED) for name, axioms in records.items()
           if axioms - ALLOWED}
    if missing or extra or bad:
        raise ValueError('Axiom audit failed: '
                         f'missing={sorted(missing)}, extra={sorted(extra)}, disallowed={bad}')
    return records
