import pathlib
import tempfile
import unittest

from scripts.check_lean_sources import check_sources, has_module_header, physical_lines


class LeanSourceTests(unittest.TestCase):
    def test_module_header_after_plain_comments(self):
        self.assertTrue(has_module_header("-- note\n/- outer /- inner -/ -/\nmodule\n"))
        for source in ("/-! docs -/\nmodule", "/-- docs -/\nmodule", "moduleName", "module.foo", "moduleα", "\ufeffmodule", "/- open\nmodule"):
            with self.subTest(source=source):
                self.assertFalse(has_module_header(source))

    def test_physical_lines(self):
        for source, expected in (("", 0), ("module\n", 1), ("module\r\n\r\n", 2), ("module\n-- tail", 2), ("a\rb", 1)):
            with self.subTest(source=source):
                self.assertEqual(physical_lines(source), expected)

    def test_checks_unused_and_nested_sources_but_skips_caches(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for name in ("Unused.lean", "nested/Main.lean", ".lake/Bad.lean", ".git/Bad.lean"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("import Mathlib\n")
            errors = check_sources(root)
            self.assertEqual(len(errors), 2)
            self.assertTrue(any("Unused.lean" in error for error in errors))
            self.assertTrue(any("nested/Main.lean" in error for error in errors))

    def test_source_line_limit_includes_lakefile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "Main.lean").write_text("module\n" + "\n" * 9999)
            (root / "lakefile.lean").write_text("import Lake\n")
            self.assertEqual(check_sources(root), [])
            (root / "lakefile.lean").write_text("import Lake\n" + "\n" * 10000)
            self.assertIn("10,000", " ".join(check_sources(root)))

    def test_challenge_line_and_byte_limits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            challenge = root / "Challenge.lean"
            challenge.write_text("module\n" + "\n" * 1000)
            self.assertIn("1,000", " ".join(check_sources(root)))
            challenge.write_text("module\n-- " + "α" * 51200)
            self.assertIn("100 KiB", " ".join(check_sources(root)))

    def test_rejects_lean_symlinks_and_invalid_utf8(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "Main.lean").write_text("module\n")
            (root / "Link.lean").symlink_to("Main.lean")
            (root / "Invalid.lean").write_bytes(b"\xff")
            errors = check_sources(root)
            self.assertEqual(len(errors), 2)
            self.assertIn("symbolic link", " ".join(errors))
            self.assertIn("UTF-8", " ".join(errors))


if __name__ == "__main__":
    unittest.main()
