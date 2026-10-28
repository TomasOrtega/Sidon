# Formalization status

This records the proof checkpoint from 22 October 2026. The Palomar entry points
are now [Challenge.lean](../Challenge.lean) and [Solution.lean](../Solution.lean),
with sources and scope in [formalization.yaml](../formalization.yaml).

The paper's main theorems, corollaries, obstruction constructions, and Rado necessity
have checked Lean proofs. The blueprint records the corrections to Lemmas 3.2 and
4.1; the literal dimension-uniform bandwidth claim is refuted by a checked counterexample.
Only declarations compiled by Lean are marked `leanok`. The complete project build passed on Lean/mathlib `v4.35.0`.
Matching doc-gen4, leanblueprint `0.0.20`, the complete API documentation, PDF,
web blueprint, declaration audit, and theorem dependency audit also pass. No project theorem uses proof placeholders, added axioms, option
overrides, or native evaluation.

Final local validation covers all 429 project modules (54,805 Lean lines), all
368 declarations referenced by the blueprint, and the 68-page rendered PDF.
All source files are reachable from `Sidon.lean`; there are no unchecked orphan modules.

Implementation commit `8db3e61812d5af1ddfa599041f44a9c90cddd79b` passed
[Lean CI](https://github.com/TomasOrtega/Sidon/actions/runs/39801407725) and
[blueprint/API generation and Pages deployment](https://github.com/TomasOrtega/Sidon/actions/runs/39801407688).

| Component | Expanded natural-language argument | Lean implementation |
| --- | --- | --- |
| Sidon definitions and unique nonzero differences | Complete | Checked |
| Integer intervals and translation | Complete | Basic interface checked |
| Finite Fourier sums and indicator norms | Complete | Checked |
| Discrete Fejer probability kernel | Complete | Checked, including triangular closed form |
| Correlations and van der Corput | Complete | Checked |
| Erdos–Turan size bound, Appendix A | Complete with explicit constant | Checked |
| Main Fourier uniformity, Theorem 1.2 | Complete with constant 16 | Checked in pointwise and supremum-norm forms |
| Cilleruelo interval estimate and Section 6 | Complete from a finite variance identity | Interval estimate checked with constant 16; improved Fourier estimate checked with constant 36 |
| Progressions, Section 3 | Complete, including lengths zero and one | Theorem 3.1 and normalized interval/residue corollaries checked, including all endpoint conventions |
| Smooth and regular Bohr corollaries | Complete with a dimension-uniform smoothing repair | Checked with absolute constants 48000 and 48100 |
| Literal dimension-uniform bandwidth in Lemma 4.1 | Corrected dimension-dependent tensor argument; original uniform cutoff refuted by a counterexample | Corrected tensor approximation and unconditional failure of a uniform cutoff both checked |
| Dual norms and dense models, Appendix C | Complete with real modulation and polynomial approximation | Checked, including simultaneous models and completion to a full dense colouring |
| Quantitative Rado/Frankl–Graham–Rodl input | Complete reduction to checked Hales–Jewett | Checked from finite Deuber extraction, integer kernel parametrization and fiber counting |
| Partition regularity transfer, Theorem 1.15 | Complete, including the quantitative counting argument | Checked end to end, with all constants chosen before the ambient interval and colouring |
| Rado necessity, Remark 1.16 | Complete first-digit colouring proof | Checked on positive natural and integer tuples, with one fixed finite colouring |
| Bose–Chowla finite-field construction | Complete proof accompanies the construction | Checked: every prime p gives p integer Sidon points in [p²−1] |
| Sharp asymptotic obstruction constructions, Proposition 1.13 and Remark 1.14 | Complete from Bose–Chowla and a proved prime number theorem | Checked for every sufficiently large N, with the sharp leading coefficients |
| Largest-set Corollary 1.4 | Complete Ingham density proof and positive smoothed-detector argument | Checked unconditionally, including actual Weyl/Vinogradov–Korobov inputs, exact explicit formula, uniform zero density and the required prime-interval theorem |

The blueprint records definitions, quantifier order, positive denominators, finite
support, all four Fourier correlation errors, integer rounding, and small cases.
The reuse audit distinguishes code that was actually inspected from search
nonresults, and records differences in versions, normalizations, and licenses.

Build and generated-document validation are repeated before each pushed checkpoint.
The usage report is a timestamped snapshot of locally recorded team inference
counters, with inherited child history removed. Its API-equivalent estimate is
not the user's actual subscription bill.

The dependency audit in `scripts/CheckAxioms.lean` checks twenty-seven public endpoints,
including the imported weak prime number theorem, the bandwidth counterexample,
the actual zeta estimates, the exact smoothed explicit formula, uniform zero density,
the short-prime-interval theorem, and the unconditional maximum-set Fourier rate.
It permits only `propext`, `Classical.choice`, and `Quot.sound`.
