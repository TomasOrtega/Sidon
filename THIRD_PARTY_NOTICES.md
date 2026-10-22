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
