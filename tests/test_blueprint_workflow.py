import pathlib
import shlex
import subprocess
import sys
import unittest


class BlueprintWorkflowTests(unittest.TestCase):
    def test_pip_install_commands_use_supported_options(self):
        workflow = pathlib.Path(__file__).parents[1] / ".github/workflows/blueprint.yml"
        commands = [
            shlex.split(line.strip())[2:]
            for line in workflow.read_text().splitlines()
            if line.strip().startswith("pip install ")
        ]
        self.assertTrue(commands)
        for args in commands:
            with self.subTest(args=args):
                result = subprocess.run(
                    [
                        sys.executable,
                        "-c",
                        "from pip._internal.commands import create_command; "
                        "import sys; create_command('install').parse_args(sys.argv[1:])",
                        *args,
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
