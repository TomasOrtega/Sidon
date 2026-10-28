import hashlib
import pathlib
import re
import subprocess
import sys
import tempfile
import unittest
import zipfile


class MetadataWorkflowTests(unittest.TestCase):
    def test_python_selects_a_wheel_allowed_by_palomar_hashes(self):
        workflow = pathlib.Path(__file__).parents[1] / ".github/workflows/lean_action_ci.yml"
        metadata = re.search(
            r"^  metadata:\n(.*?)(?=^  \S|\Z)", workflow.read_text(), re.MULTILINE | re.DOTALL
        ).group(1)
        setup = re.search(
            r"uses: actions/setup-python@[^\n]+\n(?:(?!      - ).*\n)*?"
            r"\s+python-version: ['\"]?([\d.]+)",
            metadata.split("python3 -m venv", 1)[0],
        )
        # The failed Ubuntu job used Python 3.12 without an explicit setup step.
        version = setup.group(1) if setup else "3.12"
        abi = "cp" + "".join(version.split(".")[:2])

        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            wheels = {}
            # Model the pinned hash list, which permits the Linux cp311 wheel only.
            for tag in ("cp311", "cp312"):
                wheel = root / f"PyYAML-6.0.3-{tag}-{tag}-manylinux2014_x86_64.whl"
                with zipfile.ZipFile(wheel, "w") as archive:
                    archive.writestr(
                        "PyYAML-6.0.3.dist-info/METADATA",
                        "Metadata-Version: 2.1\nName: PyYAML\nVersion: 6.0.3\n",
                    )
                    archive.writestr(
                        "PyYAML-6.0.3.dist-info/WHEEL",
                        "Wheel-Version: 1.0\nRoot-Is-Purelib: false\n"
                        f"Tag: {tag}-{tag}-manylinux2014_x86_64\n",
                    )
                    archive.writestr("PyYAML-6.0.3.dist-info/RECORD", "")
                wheels[tag] = wheel
            requirements = root / "requirements.txt"
            digest = hashlib.sha256(wheels["cp311"].read_bytes()).hexdigest()
            requirements.write_text(f"PyYAML==6.0.3 --hash=sha256:{digest}\n")
            result = subprocess.run(
                [
                    sys.executable, "-m", "pip", "--isolated", "--disable-pip-version-check",
                    "--no-cache-dir", "download", "--no-index", "--find-links", str(root),
                    "--require-hashes", "--only-binary=:all:", "--no-deps",
                    "--platform", "manylinux2014_x86_64", "--implementation", "cp",
                    "--python-version", version, "--abi", abi,
                    "--dest", str(root / "download"), "-r", str(requirements),
                ],
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
