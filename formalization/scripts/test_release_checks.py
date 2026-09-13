"""Regression tests for failure paths in the release audit and path redaction."""
from pathlib import Path
import unittest

from audit_checks import ALLOWED, TARGETS, check_output, inventory
from public_logs import NOTICE, publish_log, redact


class AuditTests(unittest.TestCase):
    def output(self, axioms='propext, Classical.choice, Quot.sound'):
        return '\n'.join(f"'{name}' depends on axioms: [{axioms}]" for name in sorted(TARGETS))

    def test_allowed_axioms(self):
        self.assertTrue(all(value == ALLOWED for value in check_output(self.output(), set(TARGETS)).values()))

    def test_empty_axioms(self):
        output = '\n'.join(f"'{name}' does not depend on any axioms" for name in TARGETS)
        self.assertTrue(all(not value for value in check_output(output, set(TARGETS)).values()))

    def test_forbidden_axioms(self):
        for axiom in ('sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler', 'unproved_assumption'):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                check_output(self.output(axiom), set(TARGETS))

    def test_missing_output(self):
        with self.assertRaises(ValueError):
            check_output('\n'.join(self.output().splitlines()[1:]), set(TARGETS))

    def test_malformed_output(self):
        with self.assertRaises(ValueError):
            check_output(self.output().replace('depends on axioms:', 'unexpected format:'), set(TARGETS))

    def test_duplicate_output(self):
        with self.assertRaises(ValueError):
            check_output(self.output() + '\n' + self.output(), set(TARGETS))

    def test_extra_output(self):
        with self.assertRaises(ValueError):
            check_output(self.output() + "\n'Unexpected.theorem' depends on axioms: []", set(TARGETS))

    def test_empty_inventory(self):
        with self.assertRaises(ValueError):
            check_output('', set())

    def test_removed_final_target(self):
        with self.assertRaises(ValueError):
            check_output(self.output(), set(TARGETS) - {next(iter(TARGETS))})

    def test_actual_inventory(self):
        root = Path(__file__).resolve().parents[1]
        sources = [path.read_text() for path in sorted((root / 'Dyadic354').glob('*.lean'))]
        audit = (root / 'Dyadic354/Audit.lean').read_text()
        self.assertEqual(len(inventory(sources, audit)), 381)
        with self.assertRaises(ValueError):
            inventory(sources, audit.replace('#print Dyadic354.erdos354_part_i\n', ''))
        with self.assertRaises(ValueError):
            inventory(sources, audit + '\n#print axioms Dyadic354.erdos354_part_i\n')


class PrivacyTests(unittest.TestCase):
    def test_paths_and_diagnostics(self):
        raw = ('CWD: /Users/example/repo/formalization\n'
               '/Users/example/cache/Mathlib/Foo.lean:2: error: failed\n'
               '/var/folders/xx/random/T/erdos354-lean-clean-123/formalization\n'
               '/home/example/.elan/toolchains/tool/lib/lean\n'
               'goal: p < 2*q\nEXIT CODE: 1\n')
        public = publish_log(raw, '/Users/example/repo', '/Users/example/cache')
        self.assertIn('$REPOSITORY/formalization', public)
        self.assertIn('$DEPENDENCY_CACHE/Mathlib/Foo.lean:2: error: failed', public)
        self.assertIn('$FRESH_PROJECT', public)
        self.assertIn('$ELAN_HOME/toolchains/tool/lib/lean', public)
        self.assertIn('goal: p < 2*q\nEXIT CODE: 1', public)
        for private in ('/Users/', '/home/', '/var/folders/', 'example'):
            self.assertNotIn(private, public)
        self.assertEqual(public, publish_log(public))
        self.assertEqual(public.count(NOTICE), 1)

    def test_source_hashes_and_urls_unchanged(self):
        value = 'SHA256: 623b20bab06c99013dcbefed752aa80ce29a879930eefc1d069e4944bc5ceb0e\nhttps://github.com/Andrewyzzz/erdos354\n'
        self.assertEqual(redact(value), value)


if __name__ == '__main__':
    unittest.main()
