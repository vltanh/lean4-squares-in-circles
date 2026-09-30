"""Unit tests of source/audit guards. These are not executions of Lean."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('six_audit', ROOT / 'scripts/audit-six-sources.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class SourceAuditTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        source = '/- outer /- sorry -/ axiom -/\n-- unsafe\n"admit"\nlemma x : True := by trivial'
        self.assertIsNone(audit.FORBIDDEN.search(audit.code_only(source)))
        self.assertEqual(source.count('\n'), audit.code_only(source).count('\n'))

    def test_admissions_rejected(self):
        for word in ('sorry', 'admit', 'axiom', 'native_decide', 'unsafe', 'sorryAx'):
            self.assertIsNotNone(audit.FORBIDDEN.search(audit.code_only(f'lemma x := {word}')))

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError): audit.code_only('/- unfinished')

    def test_standard_axioms(self):
        text = "'Example.one' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n" \
               "'Example.two' does not depend on any axioms\n"
        result = audit.validate_axioms(text, ['Example.one', 'Example.two'])
        self.assertEqual(len(result), 2)

    def test_unapproved_axiom_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate_axioms("'Example.one' depends on axioms: [sorryAx]", ['Example.one'])

    def test_missing_record_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate_axioms('', ['Example.one'])

    def test_duplicate_record_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate_axioms("'Example.one' does not depend on any axioms\n"*2, ['Example.one'])

    def test_current_source_tree(self):
        result = audit.source_report(ROOT)
        self.assertEqual(result['source_hygiene'], 'PASS')
        self.assertFalse(result['unrestricted_n6_theorem_proved'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
