# Third-party source notices

The Apache 2.0 license text for the following adapted source is included in
[LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt). This notice records the scope
of those adaptations; it does not assign a license to the rest of the repository.

## mathlib

`Sidon/Analysis/TorusFourier.lean` preserves the public Sidon interface while
using mathlib's finite-torus Fourier declarations. Its earlier implementation
adapted David Loeffler's character-density and Hilbert-basis arguments.

- Copyright (c) 2023 David Loeffler. All rights reserved.
- [Upstream source at the current mathlib release](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Fourier/AddCircleMulti.lean).
- Modifications: probability-Haar specialization to `Fin d`, Sidon declaration
  names, and bridges to the upstream Fourier API.

## PrimeNumberTheoremAnd

`Sidon/NumberTheory/Tauberian/` contains a proof-only adaptation of source from
[PrimeNumberTheoremAnd at commit 127b50e](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/127b50e33f6033e2147921167a117af96d9ba4ea),
released under Apache 2.0 by its contributors.

- Adapted upstream paths under `PrimeNumberTheoremAnd/`: `Sobolev.lean`,
  `Fourier.lean`, `Wiener.lean` through `WeakPNT`, the first smooth-cutoff lemma
  in `SmoothExistence.lean`, `Mathlib/Analysis/Asymptotics/Asymptotics.lean`,
  and the initial prime-number-theorem consequences in `Consequences.lean`.
- Upstream has no root `NOTICE` file or copyright headers in these Lean files.
  `RelativePrimeIntervals.lean` is an independent project proof.
- Modifications: namespace isolation, project import paths, removal of unused
  branches and metadata, and explicit elaboration of arguments previously
  controlled by local transparency settings.
- The extracted proof is checked against the project's toolchain. It does not
  import optional later sections or external proof certificates.

## RiemannGaussian

`Sidon/NumberTheory/RiemannGaussian/` contains a proof-only extraction from
[dbsanfte/RiemannGaussian at commit 6e969fd](https://github.com/dbsanfte/RiemannGaussian/tree/6e969fd6e9c639eed280c595732248c106187603),
released under Apache 2.0.

- Copyright (c) 2026 David Sanftenberg. All rights reserved.
- Authors: David Sanftenberg. Upstream has a standard Apache 2.0 `LICENSE`
  and no root `NOTICE` file. Original copyright headers are retained;
  extracted files without an original header carry the same repository
  attribution.
- The [extraction manifest](docs/rg-extraction-manifest.json) lists all 275
  original paths, selected declarations, immutable upstream revision, source
  and adapted file hashes, and import changes.
- Modifications: declaration-level dependency slicing, removal of unused
  source and option commands, project module paths, and elimination of
  Mathlib imports already supplied by selected dependencies. Every module's
  complete Mathlib import set is preserved transitively.
- Two positivity tactic calls in `ZetaVinogradovBalancedScale` and
  `ZetaVinogradovCubicScale` use explicit positive real-power proofs for
  compatibility with Lean 4.35.0. Definitions and theorem statements are
  preserved. Two real parameters previously inferred automatically are
  declared explicitly for the project binder policy. Declaration namespaces
  remain `RiemannGaussian`.
- Qualitative Poisson comparison, reciprocal norm-square summability, and
  zero-primitive integrability replace unused numerical zero-mass estimates.
  The exact transforms and smoothed explicit formula keep their statements.
  The indicator-integrability proof uses the current null-measurability API.
- The complete 275-module closure passed the actual project build with its
  binder policy enabled. Post-rewrite audits of the VK/Weyl bounds, exact
  formula, zero mass, conjugation, and nonreality contain only `propext`,
  `Classical.choice`, and `Quot.sound`. The umbrella imports every adapted
  source file.

`Sidon/NumberTheory/ZetaCrudeCount.lean` also adapts the xi-growth and Jensen
arguments from `GaussianXiSubquadraticGrowth.lean` and
`GaussianXiSubquadraticCounting.lean` at the same immutable revision. It keeps
the stronger four-thirds Mellin exponent and independently connects the result
to this project's finite zero occurrences and analytic multiplicities.
