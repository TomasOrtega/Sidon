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
| Discrete Fejer probability kernel | Complete | Basic identities checked; triangular closed form pending |
| Correlations and van der Corput | Complete | Checked |
| Erdos–Turan size bound, Appendix A | Complete with explicit constant | Checked |
| Main Fourier uniformity, Theorem 1.2 | Complete with constant 16 | Checked in pointwise and supremum-norm forms |
| Cilleruelo interval estimate and Section 6 | Complete from a finite variance identity | Pending |
| Progressions, Section 3 | Complete, including lengths zero and one | Pending |
| Smooth and regular Bohr corollaries | Complete with a dimension-uniform smoothing repair | Pending |
| Literal dimension-uniform bandwidth in Lemma 4.1 | Corrected dimension-dependent tensor argument; original uniform cutoff refuted by a counterexample | Pending |
| Dual norms and dense models, Appendix C | Complete with real modulation and explicit polynomial approximation | Pending |
| Quantitative Rado/Frankl–Graham–Rodl input | Complete reduction to checked Hales–Jewett | Pending |
| Partition regularity transfer, Theorem 1.15 | Complete, including an expanded quantitative counting argument | Pending |
| Largest-set and asymptotic construction corollaries | Reduction explicit; Singer and prime-gap inputs remain dependencies | Pending |

The blueprint records definitions, quantifier order, positive denominators, finite
support, all four Fourier correlation errors, integer rounding, and small cases.
The reuse audit distinguishes code that was actually inspected from search
nonresults, and records differences in versions, normalizations, and licenses.

Build and generated-document validation are repeated before each pushed checkpoint.
The usage report is a timestamped snapshot of locally recorded team inference
counters, with inherited child history removed. Its API-equivalent estimate is
not the user's actual subscription bill.

The axiom audit for `Sidon.sidon_fourier_uniformity`, `Sidon.vanDerCorput`, and
`IsSidonSet.addEnergy_eq` reports only `propext`, `Classical.choice`, and `Quot.sound`.
