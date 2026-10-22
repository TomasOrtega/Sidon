---
layout: default
usemathjax: true
---

# Extremal Sidon sets are Fourier uniform

This project formalizes [Ortega and Prendiville's paper](https://arxiv.org/abs/2110.13447)
in Lean. The main goals are Fourier uniformity, equidistribution in progressions
and Bohr neighbourhoods, and partition regularity for equations in at least five
variables.

The formalization is **in progress**. The blueprint expands the paper's arguments
into detailed natural-language proofs. A completed informal proof is distinct
from a checked Lean theorem; only verified declarations are marked complete in
the blueprint.

- [Read the blueprint]({{ site.url }}/blueprint/)
- [Download the blueprint PDF]({{ site.url }}/blueprint.pdf)
- [Explore the dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
- [Browse the Lean declarations]({{ site.url }}/docs/)

The checked Lean development proves **Theorem 1.2 in supremum norm, with
absolute constant 16**. Its foundations include unique nonzero differences,
exact Sidon additive energy, finite Fourier sums and fourth moments, the
discrete Fejer kernel, unrestricted-window van der Corput, and the sharp
Appendix A interval-size bound. The independent Cilleruelo interval estimate
and **Theorem 3.1 for arbitrary finite arithmetic progressions** also check,
including the normalized interval and residue-class corollaries.
The improved Fourier estimate checks with **constant 36**. The smooth and
regular Bohr corollaries check with absolute constants **48000 and 48100**.
**Theorem 1.15 on partition regularity is checked end to end.** Its inputs
include full finite Deuber extraction from Hales--Jewett, quantitative Rado
counting, the colouring dense model, and the Fourier counting-transfer bound.
Bose–Chowla, Proposition 1.13, and the modular obstruction in Remark 1.14
are checked, including their sharp asymptotic densities for every sufficiently
large interval. The largest-set rate in Corollary 1.4 still needs its
power-saving prime interval input.
The project uses the latest stable Lean and mathlib **v4.35.0**, matching
doc-gen4, and leanblueprint **0.0.20**.

The proof audit gives explicit constants for the Fourier bounds and a full
finite-variance proof of the Cilleruelo interval estimate. It corrects the small
cases of the progression estimate and the real-valued dual-norm argument.
An alternate smoothing proof establishes dimension-uniform Bohr corollaries;
a counterexample shows that the paper's literal dimension-uniform finite-bandwidth
approximation statement needs correction. The counterexample and the corrected
dimension-dependent tensor approximation are both checked in Lean. The quantitative counting input now has
a checked proof from Hales–Jewett.

The [reuse audit](https://github.com/TomasOrtega/Sidon/blob/master/docs/reuse-scout.md)
records results found in mathlib, Lean Pool, Tau Ceti, and other Lean projects,
including version, normalization, and licensing constraints.
The [usage report](https://github.com/TomasOrtega/Sidon/blob/master/docs/usage.md)
records measured team tokens and elapsed time, with Standard and Fast
API-equivalent cost estimates from official pricing. Those estimates do not
establish actual subscription charges.

Source and progress are available in the
[repository](https://github.com/TomasOrtega/Sidon).
