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
Appendix A interval-size bound. The improved estimate and the
partition-regularity and equidistribution applications remain in progress.

The proof audit gives explicit constants for the Fourier bounds and a full
finite-variance proof of the Cilleruelo interval estimate. It corrects the small
cases of the progression estimate and the real-valued dual-norm argument.
An alternate smoothing proof establishes dimension-uniform Bohr corollaries;
a counterexample shows that the paper's literal dimension-uniform finite-bandwidth
approximation statement needs correction. The quantitative counting input now has
an expanded proof from Hales–Jewett, with its Lean implementation in progress.

The [reuse audit](https://github.com/TomasOrtega/Sidon/blob/master/docs/reuse-scout.md)
records results found in mathlib, Lean Pool, Tau Ceti, and other Lean projects,
including version, normalization, and licensing constraints.
The [usage report](https://github.com/TomasOrtega/Sidon/blob/master/docs/usage.md)
records measured team tokens and elapsed time, with Standard and Fast
API-equivalent cost estimates from official pricing. Those estimates do not
establish actual subscription charges.

Source and progress are available in the
[repository](https://github.com/TomasOrtega/Sidon).
