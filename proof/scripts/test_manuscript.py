"""Regression checks for the manuscript's restricted typesetting syntax."""
import unittest

from build_pdf import inline, convert, SOURCE
from check_math import check


class MathTests(unittest.TestCase):
    def document(self, formula):
        return '$`x`$\n\n```math\n' + formula + '\n```\n'

    def test_manuscript(self):
        self.assertEqual(check(SOURCE.read_text()),
                         {'displays': 90, 'inline_formulas': 405, 'equation_labels': 23})

    def test_balanced_groups_and_sets(self):
        check(self.document(r'\lbrace x_{n+1}: n\ge 0\rbrace'))

    def test_unbalanced_groups(self):
        with self.assertRaises(ValueError):
            check(self.document(r'\sum_{i<j'))

    def test_unprotected_inline(self):
        with self.assertRaises(ValueError):
            check(self.document('x') + '$x_i$')

    def test_unsupported_operator_macro(self):
        with self.assertRaises(ValueError):
            check(self.document(r'\operatorname{gap}(W)'))

    def test_unclosed_environment(self):
        with self.assertRaises(ValueError):
            check(self.document(r'\begin{aligned}x&=1'))

    def test_duplicate_equation_label(self):
        with self.assertRaises(ValueError):
            check(self.document(r'x\qquad\text{(1)}') + self.document(r'y\qquad\text{(1)}'))

    def test_html_sensitive_relation(self):
        with self.assertRaises(ValueError):
            check(self.document('x<y'))

    def test_floating_equation_tag(self):
        with self.assertRaises(ValueError):
            check(self.document(r'x\tag{1}'))

    def test_bare_row_break(self):
        with self.assertRaises(ValueError):
            check(self.document('x\\\\\ny'))

    def test_converter_inventory(self):
        tex, counts = convert(SOURCE.read_text())
        self.assertEqual(counts['display_formulas'], 90)
        self.assertEqual(counts['inline_formulas'], 405)
        self.assertEqual(counts['tables'], 2)
        self.assertNotIn('$`', tex)
        self.assertNotIn('```', tex)

    def test_inline_math_not_reescaped(self):
        self.assertEqual(inline('$`x_{n+1}`$'), r'\(x_{n+1}\)')

    def test_print_title_line_break(self):
        tex, _ = convert(SOURCE.read_text())
        title = tex.split('\n\n', 1)[0]
        self.assertEqual(title,
                         r'\title{Erdős Problem 354(i):\\' + '\n'
                         + 'Strong Completeness of Two Dyadic Floor Sequences}')

    def test_authorless_manuscript_and_pdf(self):
        source = SOURCE.read_text()
        tex, _ = convert(source)
        self.assertIn(r'\author{}', tex)
        self.assertNotIn('Andrewyzzz and', source)
        self.assertNotIn('Chatgpt-6 Astra', source)
        self.assertIn('with assistance from ChatGPT and OpenAI Codex, using GPT-6 (Astra).', source)
        preamble = (SOURCE.parent / 'pdf/preamble.tex').read_text()
        self.assertIn('pdfauthor={}', preamble)


if __name__ == '__main__':
    unittest.main()
