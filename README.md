# Extremal Sidon sets

A Lean formalization of Miquel Ortega and Sean Prendiville,
[*Extremal Sidon sets are Fourier uniform, with applications to partition
regularity*](https://arxiv.org/abs/2110.13447).

Near-maximal Sidon sets have small Fourier discrepancy. This gives
bounds for counts in progressions and Bohr sets, and monochromatic solutions
to partition regular linear equations in at least five variables.
The project also proves the largest-set Fourier rate and sharp obstruction
constructions. These results concern additive combinatorics and Ramsey theory.

- [Challenge.lean](Challenge.lean): the 12 submitted statements and their definitions.
- [Solution.lean](Solution.lean): connects the statements to the checked proofs in `Sidon/`.
- [comparator.json](comparator.json): the declarations checked by Comparator.
- [formalization.yaml](formalization.yaml): sources, authorship, AI use, and review status.
- [Website and blueprint](https://TomasOrtega.github.io/Sidon/): detailed proof accounts.
- [Proof status](docs/progress.md) and [reuse notes](THIRD_PARTY_NOTICES.md).

The formalization gives explicit constants. It corrects the small cases in
Lemma 3.2 and the dimension dependence in Lemma 4.1. A separate smoothing
proof recovers the Bohr corollaries. The Challenge states the conventions;
solution tuples may repeat entries. No independent human mathematical review
is recorded.

The repo uses [Apache 2.0](LICENSE). Cite it with [CITATION.cff](CITATION.cff).
[Recorded AI usage](docs/usage.md) covers the original formalization.

## Check the project

Lean and Mathlib are pinned to `v4.35.0`. `lake-manifest.json` records exact
dependency revisions.

```bash
python3 scripts/check_lean_sources.py
python3 -m unittest discover -s tests -p 'test_*.py'
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

`Challenge.lean` has deliberate theorem holes. The proof library and Solution
have no proof holes or added axioms. CI checks the source rules and allowed axioms.
On Linux, with `bubblewrap` installed, also run:

```bash
bash scripts/verify-comparator.sh
```

This checks the Challenge against the Solution with Lean, NanoDa, and con-ron.
It also runs in CI. It cannot run on macOS.

To build the blueprint, install `leanblueprint==0.0.20`, then run
`leanblueprint pdf`, `leanblueprint web`, and
`lake exe checkdecls blueprint/lean_decls`.

## Submit to Palomar

Follow [Palomar's submission guide](https://palomar-registry.org/how-to-submit).
Commit and push the final changes, then wait for all CI checks to pass. Submit
`TomasOrtega/Sidon` with the full SHA from `git rev-parse HEAD`. Use the root
project, `comparator.json`, and `formalization.yaml`; the form's default paths
already select them. Uncommitted or unpushed changes are not part of a submission.
