# Formalization status

This is an active formalization, not a completed proof of the paper. Only declarations
compiled by Lean are marked `leanok` in the blueprint. The original Lean/mathlib pins
are retained, and no project theorem uses proof placeholders, added axioms, option
overrides, or native evaluation.

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
| Literal dimension-uniform bandwidth in Lemma 4.1 | Corrected dimension-dependent tensor argument; original uniform cutoff refuted by a counterexample | Pending |
| Dual norms and dense models, Appendix C | Complete with real modulation and polynomial approximation | Checked, including simultaneous models and completion to a full dense colouring |
| Quantitative Rado/Frankl–Graham–Rodl input | Complete reduction to checked Hales–Jewett | Checked from finite Deuber extraction, integer kernel parametrization and fiber counting |
| Partition regularity transfer, Theorem 1.15 | Complete, including the quantitative counting argument | Checked end to end, with all constants chosen before the ambient interval and colouring |
| Bose–Chowla finite-field construction | Complete proof accompanies the construction | Checked: every prime p gives p integer Sidon points in [p²−1] |
| Largest-set and asymptotic construction corollaries | Reduction explicit; Singer and prime-gap inputs remain dependencies | Pending |

The blueprint records definitions, quantifier order, positive denominators, finite
support, all four Fourier correlation errors, integer rounding, and small cases.
The reuse audit distinguishes code that was actually inspected from search
nonresults, and records differences in versions, normalizations, and licenses.

Build and generated-document validation are repeated before each pushed checkpoint.
The usage report is a timestamped snapshot of locally recorded team inference
counters, with inherited child history removed. Its API-equivalent estimate is
not the user's actual subscription bill.

The axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
