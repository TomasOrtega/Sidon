import os
import pathlib
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


class BlueprintWorkflowTests(unittest.TestCase):
    def test_api_docs_cache_is_saved_before_blueprint_build(self):
        workflow = pathlib.Path(__file__).parents[1] / ".github/workflows/blueprint.yml"
        steps = re.split(r"(?=^      - name:)", workflow.read_text(), flags=re.MULTILINE)
        saves = [i for i, step in enumerate(steps) if "uses: actions/cache/save@v4" in step]
        self.assertEqual(len(saves), 1, "Save API docs before later publishing steps can fail")
        restore = next(i for i, step in enumerate(steps) if "uses: actions/cache/restore@v4" in step)
        build = next(i for i, step in enumerate(steps) if "build Sidon:docs" in step)
        blueprint = next(i for i, step in enumerate(steps) if "uses: xu-cheng/texlive-action" in step)
        save = saves[0]
        self.assertLess(restore, build)
        self.assertLess(build, save)
        self.assertLess(save, blueprint)
        self.assertIn("id: mathlib_docs_cache", steps[restore])
        self.assertIn("steps.mathlib_docs_cache.outputs.cache-hit != 'true'", steps[save])
        self.assertIn("key: ${{ steps.mathlib_docs_cache.outputs.cache-primary-key }}", steps[save])
        paths = [
            steps[i].split("          path: |\n", 1)[1].split("          key:", 1)[0].strip()
            for i in (restore, save)
        ]
        self.assertEqual(paths[0], paths[1])
        self.assertIn(".lake/build/api-docs.db", paths[0])
        self.assertIn(".lake/build/doc-data", paths[0])
        self.assertIn("!.lake/build/doc-data/Sidon*", paths[0])

    def test_graphviz_plugin_can_be_linked_and_loaded(self):
        compiler = shutil.which("cc")
        if compiler is None:
            self.skipTest("C compiler is required")
        workflow = pathlib.Path(__file__).parents[1] / ".github/workflows/blueprint.yml"
        exports = [
            line.strip()
            for line in workflow.read_text().splitlines()
            if line.strip().startswith("export LDFLAGS=")
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            plugins = root / "graphviz"
            plugins.mkdir()
            source = root / "plugin.c"
            source.write_text("int graphviz_plugin_fixture(void) { return 7; }\n")
            suffix = ".dylib" if sys.platform == "darwin" else ".so"
            library = plugins / f"libgvplugin_core{suffix}"
            command = [compiler, "-shared", "-fPIC", str(source), "-o", str(library)]
            if sys.platform == "darwin":
                command.extend(["-Wl,-install_name,@rpath/" + library.name])
            subprocess.run(command, capture_output=True, text=True, check=True)
            program = root / "main.c"
            program.write_text(
                "int graphviz_plugin_fixture(void);\n"
                "int main(void) { return graphviz_plugin_fixture() != 7; }\n"
            )
            executable = root / "check-plugin"
            script = "\n".join(exports).replace("/usr/lib/graphviz", str(plugins))
            script += "\n" + shlex.join([compiler, str(program)])
            script += " $LDFLAGS -lgvplugin_core -o " + shlex.quote(str(executable))
            environment = os.environ.copy()
            for key in ("LDFLAGS", "LIBRARY_PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
                environment.pop(key, None)
            linked = subprocess.run(
                ["/bin/sh", "-c", script],
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(linked.returncode, 0, linked.stderr)
            loaded = subprocess.run(
                [str(executable)], env=environment, capture_output=True, text=True, check=False
            )
            self.assertEqual(loaded.returncode, 0, loaded.stderr)

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
