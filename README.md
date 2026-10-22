# Extremal Sidon sets

A Lean formalization of Miquel Ortega and Sean Prendiville,
[*Extremal Sidon sets are Fourier uniform, with applications to partition
regularity*](https://arxiv.org/abs/2110.13447).

The expanded [blueprint](blueprint/src/content.tex) gives detailed natural-language
proofs before their Lean implementation. It records rounding, empty-set cases,
normalizations, explicit constants, and dependencies. A blueprint proof is not a
claim of completed formalization: only checked declarations receive `leanok`.

- [Project website and blueprint](https://TomasOrtega.github.io/Sidon/)
- [Reusable Lean results and remaining gaps](docs/reuse-scout.md)
- [Core implementation plan](docs/core-formalization-plan.md)
- [Applications implementation plan](docs/applications-formalization-plan.md)
- [Measured usage and elapsed time](docs/usage.md), with [pricing assumptions](docs/pricing.md)

The project uses the latest stable Lean and mathlib releases, `v4.35.0`,
with matching doc-gen4 and leanblueprint `0.0.20`. Exact revisions are recorded in
`lake-manifest.json` and the [tooling audit](docs/blueprint-upgrade-research.md). Project proofs use neither option overrides nor native
evaluation to discharge theorems. There are no proof placeholders or added axioms.

```bash
lake build
python3 -m unittest discover -s tests -p 'test_*.py'
leanblueprint pdf
leanblueprint web
lake exe checkdecls blueprint/lean_decls
lake env lean scripts/CheckAxioms.lean
```

The main Fourier-uniformity theorem (Theorem 1.2, with constant 16), its finite
combinatorial foundations, the sharp Appendix A interval bound, Cilleruelo's
interval estimate, improved Fourier bound (constant 36), and progression
equidistribution (Theorem 3.1) are checked. The smooth and regular Bohr
corollaries also check with absolute constants. Partition regularity
(Theorem 1.15) is checked end to end, including quantitative Rado counting and
the colouring dense model. Bose–Chowla and the sharp asymptotic obstruction constructions are checked.
The largest-set rate in Corollary 1.4 is checked unconditionally through a proved
prime-interval theorem, with all analytic zeta inputs included. See the
[status table](docs/progress.md) for the distinction between expanded arguments
and checked Lean results. Work is checkpointed at least every two hours while active.

The blueprint declaration list can also be checked without a native Lake executable:

```bash
lake env lean --run scripts/CheckDeclarations.lean blueprint/lean_decls
```
