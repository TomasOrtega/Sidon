"""Check Palomar source limits before building; Lean checks the full syntax."""

import os
import re
from pathlib import Path

# Header scanner adapted from PalomarRegistry/PalomarTemplate (Apache-2.0).
COMMENT_MARKER = re.compile(r"/-|-/")
ID_LETTER_LIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
)
ID_FIRST = rf"A-Za-z_{ID_LETTER_LIKE}"
ID_REST = rf"{ID_FIRST}0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENTIFIER_CONTINUATION = re.compile(rf"[{ID_REST}]|\.[{ID_FIRST}«]")


def has_module_header(text: str) -> bool:
    index = 0
    while index < len(text):
        if text[index] in " \r\n":
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index + 2)
            index = len(text) if end < 0 else end + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            # Lean consumes one character after a plain comment opener.
            index += 3
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    return False
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def check_sources(root: Path) -> list[str]:
    errors = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if not name.endswith(".lean"):
                continue
            relative = path.relative_to(root)
            if path.is_symlink():
                errors.append(f"{relative}: must be a regular file, not a symbolic link")
                continue
            if not path.is_file():
                continue
            data = path.read_bytes()
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError:
                errors.append(f"{relative}: source is not valid UTF-8")
                continue
            if name != "lakefile.lean" and not has_module_header(text):
                errors.append(f"{relative}: must start with a module header")
            limit = 1000 if relative == Path("Challenge.lean") else 10000
            if physical_lines(text) > limit:
                errors.append(f"{relative}: exceeds {limit:,} lines; split the file")
            if relative == Path("Challenge.lean") and len(data) > 100 * 1024:
                errors.append(f"{relative}: exceeds 100 KiB")
    return errors


if __name__ == "__main__":
    errors = check_sources(Path(__file__).resolve().parents[1])
    for error in errors:
        print(error)
    raise SystemExit(bool(errors))
