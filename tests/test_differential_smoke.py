"""Tests of differential-report classification, not cryptographic proof semantics."""
import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "differential_smoke.py"
SPEC = importlib.util.spec_from_file_location("differential_smoke", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
module = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = module
SPEC.loader.exec_module(module)

class DifferentialSmokeRunnerTests(unittest.TestCase):
    def test_cpp_verdict_requires_exact_terminal_line(self):
        self.assertEqual(module.cpp_verdict(0, "YES"), "YES")
        self.assertEqual(module.cpp_verdict(1, "NO: proof-refused"), "NO")
        self.assertEqual(module.cpp_verdict(0, "proof says YES"), "OTHER")
        self.assertEqual(module.cpp_verdict(5, "YES"), "OTHER")
        self.assertEqual(module.cpp_verdict(1, "YES"), "OTHER")

    def test_rust_inspection_is_not_verification(self):
        self.assertEqual(module.rust_inspection(0, "NOT VERIFIED: unsupported"), "STRUCTURAL_OK")
        self.assertEqual(module.rust_inspection(2, ""), "STRUCTURAL_REJECT")
        self.assertEqual(module.rust_inspection(0, "YES"), "OTHER")
        self.assertEqual(module.rust_inspection(5, "NOT CHECKED"), "OTHER")

    def test_mutations_separate_header_and_body(self):
        source = b"CPPFH821\0\0\0\0" + b"x" * 100
        for case in module.CASES:
            out = module.mutation(source, case.name)
            self.assertEqual(out == source, case.name == "honest")
            if case.expected_rust_inspection == "STRUCTURAL_OK":
                self.assertEqual(out[:12], source[:12])
            else:
                self.assertNotEqual(out[:12], source[:12])

if __name__ == "__main__":
    unittest.main()
