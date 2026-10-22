# Short prime intervals: exact dependency and source audit

Status: the Bose–Chowla construction and all reductions to Corollary 1.4
are checked. A power-saving prime-in-interval theorem is still a genuine
analytic dependency. No new axiom, placeholder proof, or replacement by a
weaker relative-gap theorem has been added.

## Required statement

The sufficient input is

```lean
Sidon.PrimeIntervalBound ((2 : ℝ) / 3) C X
```

with `0 ≤ C`. Its definition quantifies over **every real** `x ≥ X` and
requires a natural prime `p` satisfying
`x - C*x^(2/3) ≤ p ≤ x`. An infinitely-often bound or a statement only on
an unbounded subsequence does not imply this input.

The exact source theorem quoted by the paper is stronger: Baker, Harman,
and Pintz, *The difference between consecutive primes, II*, Proc. London
Math. Soc. (3) 83 (2001), 532–562, Theorem 1, proves that every sufficiently
large interval `[x - x^(21/40), x]` contains a prime. The threshold is not
specified numerically. The opening page explains that the proof uses
Harman's sieve and mean-value estimates for Dirichlet polynomials.
[Primary paper](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf).

`PrimeIntervalBound.two_thirds_of_bhp` checks the weakening: enlarge the
threshold to at least one; then `x^(21/40) ≤ x^(2/3)`, so the BHP interval
is contained in the required interval. This is a proved implication, not
a proof of its BHP premise.

## Primary Lean source audit, 22 October 2026

- **Mathlib, latest revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.**
  `NumberTheory/ArithmeticFunction/VonMangoldt.lean` contains
  nonnegativity, prime-power support, prime values, and the divisor-sum
  identity. `NumberTheory/Chebyshev.lean` additionally proves
  `psi-theta=O(sqrt x)`, and `NumberTheory/LSeries/ZetaZeros.lean` proves
  actual zero-set discreteness and finite compact intersections.
  `NumberTheory/LSeries/Dirichlet.lean`
  identifies its L-series with `-ζ'/ζ` for `Re(s)>1`. There is no checked
  all-length power-saving prime-gap theorem in this dependency graph.
- **Tau Ceti** at
  [`880c9f509f8f680d9ace828c756d6abaa03f912f`](https://github.com/TauCetiProject/TauCeti/tree/880c9f509f8f680d9ace828c756d6abaa03f912f)
  and **Lean Pool** were searched for `Hoheisel`, `Ingham`, `prime_gap`, and
  `prime_in_interval`. No relevant checked theorem was located. This is a
  search result, not a claim that every possible synonymous declaration
  has been excluded.
- **PrimeNumberTheoremAnd** at
  [`127b50e33f6033e2147921167a117af96d9ba4ea`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea)
  has useful reductions in
  [`IEANTN/PrimeInInterval.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/PrimeInInterval.lean).
  Its relative and logarithmic short-interval surfaces do not provide the
  required power rate; several deeper cited inputs are explicit `sorry`
  declarations, including the Ramaré–Saouter surface in `TMEEMT.lean`.
  They cannot be imported as unconditional checked dependencies.
- **IEANTN** at
  [`ec66e388e6e117c6881367f38665f310edf7cacf`](https://github.com/teorth/IEANTN/tree/ec66e388e6e117c6881367f38665f310edf7cacf)
  records the Ramaré–Saouter statement in
  [`Conclusions.lean`](https://github.com/teorth/IEANTN/blob/ec66e388e6e117c6881367f38665f310edf7cacf/IEANTN/Nodes/RamareSaouter2003/v1/Conclusions.lean)
  as `def prime_in_short_interval : Prop`. This is a proposition recording
  a target, and its interval width is proportional to `x`. Neither fact
  supplies a proof of a power-saving all-length interval theorem.
- **Atlas Lean** at
  [`52908d9ef815f49572bc720c6991c7cbc25e52e0`](https://github.com/facebookresearch/atlas-lean/tree/52908d9ef815f49572bc720c6991c7cbc25e52e0)
  has exactly relevant statements in
  [`ThickBhSetsWanted.lean`](https://github.com/facebookresearch/atlas-lean/blob/52908d9ef815f49572bc720c6991c7cbc25e52e0/WantedExt/Combinatorics/Additive/ThickBhSetsWanted.lean):
  primes between sufficiently large consecutive cubes, BHP intervals,
  and the resulting extremal `B_h` estimates. These declarations use
  `theorem_wanted`; they are requested results, not reusable proofs.
- **Expdb** at
  [`c8eda5e4f1f51024b6cbf70c7bef6c33da74c691`](https://github.com/teorth/expdb/tree/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691)
  discusses Ingham, Huxley, and the zero-density-to-prime-gap implication
  in [`primes.tex`](https://github.com/teorth/expdb/blob/c8eda5e4f1f51024b6cbf70c7bef6c33da74c691/blueprint/src/chapter/primes.tex).
  Its Lean tree at this revision contains exponential-sum, oscillatory,
  Fourier, and asymptotic infrastructure; no Lean zero-density or
  prime-gap implementation was located. Blueprint and Python literature
  hypotheses must not be confused with Lean proofs.
- **Lean Genius** at
  [`8c99ab46dcd9f0beae034620c675816f6aecc4a5`](https://github.com/rjwalters/lean-genius/tree/8c99ab46dcd9f0beae034620c675816f6aecc4a5)
  explicitly declares `axiom baker_harman_pintz` in
  [`Erdos1138OQ03.lean`](https://github.com/rjwalters/lean-genius/blob/8c99ab46dcd9f0beae034620c675816f6aecc4a5/proofs/Proofs/Erdos1138OQ03.lean).
  Downstream localisation theorems inherit that axiom. Its finite
  threshold `25` is not the primary theorem's unspecified asymptotic
  threshold, so even the statement must not be reused without audit.
- **The Golden Algebra** scratch zero-density files at
  [`7569f12202041f8759a6274651de86361f183b98`](https://github.com/TristenHarr/thegoldenalgebra/tree/7569f12202041f8759a6274651de86361f183b98)
  define `ZeroDensityInput` and `ModernZeroDensityExponent` as hypotheses
  and derive conditional displacement estimates. They do not prove the
  analytic density input itself.

A GitHub code search restricted to Lean was also inspected for `Ingham`,
`Hoheisel`, `Huxley`, and `Pintz`. Relevant hits were the targets and
conditional inputs listed above, rather than a checked all-length power
gap. Generic web pages calling a result “formalized” were not accepted
without reading its actual theorem and dependencies.

## Checked combinatorial and Fourier reductions

`Sidon/Constructions/Extremal.lean` proves the following chain.

1. The finite power set of `[N]` has at least one admissible Sidon subset,
   the empty set. Maximizing cardinality over its admissible members gives
   `exists_maximum_sidon`.
2. A prime `p ≤ sqrt(N)` satisfies `p²≤N`. Bose–Chowla supplies a Sidon set
   of cardinality `p` inside `[p²−1]`, hence inside `[N]`.
3. Apply the explicit gap input at `x=sqrt(N)`. Since
   `(sqrt(N))^(2/3)=N^(1/3)`, the resulting admissible set has cardinality
   at least `sqrt(N)-C*N^(1/3)`.
4. A maximum Sidon set has at least this cardinality. The checked sharp
   upper bound is `sqrt(N)+4*N^(1/4)`. For `N≥1`, division by the positive
   square root therefore gives
   `sidonDeviation N S ≤ (C+4)*N^(-1/6)`.
5. The baseline Fourier theorem gives discrepancy at most
   `16*sqrt(C+5)*sqrt(N)*N^(-1/12)`. Eventually
   `C*N^(-1/6)≤1/2`, so the lower cardinality bound gives `sqrt(N)≤2*|S|`.
   Finally `‖fourierSum(indicatorFinsupp S)‖=|S|` by the triangle inequality
   and evaluation at zero. This proves the paper's exact exponent in
   `largest_sidon_fourier_uniformity_of_prime_interval`.

All five steps are checked. The final theorem retains `hgap` in its type.
It is not marked as an unconditional proof of Corollary 1.4.

## Analytic work still required

A weaker historical route than BHP would suffice: Ingham's power saving
below `2/3`, rather than the much sharper exponent `21/40`. An explicit
implementation can separate the following obligations.

- Define and count the nontrivial zeta zeros, including multiplicities.
- Prove a uniform zero-density bound with an exponent `A<3`, for example
  the classical `8/3` bound coming from Weyl growth of zeta. The uniform
  constants and logarithmic factors must be stated, not hidden in a
  separate bound for each fixed `σ`.
- Prove a sufficiently strong zero-free region. A width `b(T)` with
  `b(T)*log(T)/log(log(T))→∞` absorbs any fixed logarithmic factor in the
  density estimate. A fixed-width multiple of `1/log(T)` does not by
  itself give this limit.
- Establish a truncated explicit formula for `ψ(x)-ψ(x-h)` whose remainder
  is bounded uniformly by `O(x*log(x)^2/T)` at the chosen endpoints, or
  first smooth the endpoints and control the smoothing error.
- Remove nonprime powers: their total Mangoldt weight below `x` is
  `O(sqrt(x)*log(x)^2)=o(x^(2/3))`.

For parameter bookkeeping, inflate the density exponent to `11/4` and
choose `T=x^(7/20)`, `h=x^(2/3)`. Then
`(11/4)*(7/20)=77/80<1`, and the truncation has power
`x/T=x^(13/20)=o(h)`. If `ρ=β+iγ`, the contribution of one zero to the
interval formula is at most `2*h*x^(β−1)` once `h≤x/2`. Partition the
real parts into strips of width `1/log(x)`; the density bound makes the
strip contributions a geometric series with ratio at most
`exp(-(1-77/80))`. The zero-free region removes all initial strips up to
order `b(T)*log(x)`, so the remaining series, including fixed logarithmic
factors, is `o(1)`. Hence the total zero contribution is `o(h)` and the
Mangoldt increment is positive after nonprime powers are removed.

This is an explicit dependency plan, not a claim that these analytic
obligations have already been formalized. The zeta growth, zero-density,
zero-free-region, and explicit-formula arguments require their own
expanded proofs and checked modules before the remaining input can be
removed.


## New primary-source hit after the latest upgrade

[RiemannGaussian at `6e969fd6e9c639eed280c595732248c106187603`](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603),
Apache 2.0, Lean 4.34.1, contains a literal actual-zeta VK region in
`ZetaVinogradovSummedZeroFree.exists_eventual_strip`; its theorem type
retains no growth or zero-free hypothesis. This is a new promising
source, not yet an imported Sidon dependency. The raw local import
closure has 1067 files and 266100 lines; it contains option-bearing
unrelated modules, so semantic extraction, current-toolchain compilation,
and an axiom audit are required before reuse. The search found no
Ingham density theorem in that tree.

The full expanded Ingham route, including the precise analytic
obligations and checked finite interfaces, is now in
[ingham-prime-interval-proof.md](ingham-prime-interval-proof.md).
`ZetaZeroCount.lean` builds actual finite zero occurrences with their
finite positive analytic multiplicity. `ZeroDensityLayers.lean` bridges
uniform real-part density to the weighted zero sum, including clipped
negative thresholds and exact floor losses. These are checked finite
lemmas, not assumptions asserting the eventual analytic density theorem.
