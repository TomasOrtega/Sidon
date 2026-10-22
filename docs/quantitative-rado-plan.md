# Quantitative Rado: closing the counting dependency

The expanded proof is in `blueprint/src/chapters/quantitative-rado.tex`. It proves the exact single-equation counting input needed for paper Lemma 5.2, starting from a theorem already present in the pinned mathlib source. No arithmetic removal lemma or new unproved Ramsey input is needed. The separate bandwidth issue in Appendix B is resolved by the counterexample `app:no-uniform-bandwidth` and by an alternate proof of both Bohr corollaries; it does not enter this combinatorial argument.

## Primary sources and checked starting point

- Frankl, Graham and Rödl, *Quantitative Theorems for Regular Systems of Equations*, J. Combin. Theory A **47** (1988), 246–261, [author-hosted PDF](https://fanchung.ucsd.edu/ron/papers/88_05_systems.pdf), Theorem 1, pages 251–252. Its Deuber variant is reference [5], an unpublished manuscript. The source was read, including the formula pages as rendered images.
- The finite row-focusing proof is the Leeb/Prömel argument, fully presented by Joel Moreira in [*A proof of Deuber’s theorem using Hales–Jewett’s theorem*](https://joelmoreira.wordpress.com/2014/10/14/a-proof-of-deubers-theorem-using-hales-jewett/) (14 October 2014). The blueprint expands the argument and adds the embedding data and multiplicity analysis required for the quantitative conclusion.
- The existing checked input is `Combinatorics.Line.exists_mono_in_high_dimension` in `.lake/packages/mathlib/Mathlib/Combinatorics/HalesJewett.lean:442`. It returns a finite coordinate type and a monochromatic combinatorial line for every colouring. Reindex by `Fintype.equivFin`; its nonempty variable set ensures the coordinate cardinality is positive. The same file also provides `Combinatorics.Subspace.exists_mono_in_high_dimension_fin`, but the one-dimensional theorem suffices here.

## Complete proof structure

1. A Deuber pattern with generators `z₀,…,zₘ` is the union of rows `c*zⱼ + Σ_{i<j} λᵢ*zᵢ`, where `|λᵢ| ≤ p`.
2. One Hales–Jewett step makes one more final row monochromatic while preserving previously monochromatic final rows. If `k < m`, use alphabet `[-p,p]^(m-k)`, word length `h`, source last index `M=h*(m-k)+k`, coefficient bound `P=max(p²,p*c,c²)`, and leading coefficient `C=c²`.
3. Track the new generators as an integer matrix with nonempty pairwise-disjoint row supports. The early generators use variable word positions, the middle generator uses fixed positions and a new leading coordinate, and the late generators use individual fresh coordinates. Every possible line gives one matrix; hence only finitely many matrices can arise before seeing any seed values.
4. Iterate the step backwards from a target with `r*(q-1)+1` rows, then forwards through the actual colouring. Every final row becomes monochromatic. Pigeonhole selects `q` rows of one colour. Composition and row selection preserve the disjoint-support property.
5. For a coefficient vector `a` with a zero-sum nonempty subset, construct an injective integer kernel matrix `B : ℚ^(s-1) → ℚ^s` whose every row has last nonzero coefficient equal to one common positive integer `c`. Start a rational kernel basis with the indicator of the zero-sum subset and, when needed, a vector equal to 1 on its complement; clear denominators and reverse columns. Each coordinate of `B*y` is an entry of the target Deuber pattern.
6. Choose `M` seed generators independently in geometrically separated intervals `[L*R^j, 2*L*R^j]`, where `R=4*P+2`, `H=(2*C+1)*R^M`, and `L=floor(N/H)`. For `N≥2H` this supplies at least `(N/(2H))^M` seed vectors. Every source pattern entry is positive and at most `N`, including those with negative earlier coefficients.
7. Each seed produces a monochromatic tuple `x=B*T*Y`. For a fixed output `x`, injectivity of `B` fixes `T*Y`. For fixed `T`, select one pivot coordinate from each of its disjoint nonempty row supports. Prescribing the remaining `M-(s-1)` seed coordinates determines each pivot uniquely. Therefore each output has at most `|𝔽|*N^(M-(s-1))` seed preimages, where `𝔽` is the fixed finite matrix family.
8. Dividing seed count by multiplicity, then by `r`, gives one colour at least `δ₀*N^(s-1)` solution tuples, with `δ₀ = 1/(r*|𝔽|*(2H)^M) > 0`.

This supplies a full natural-language proof of the quantitative input, rather than leaving FGR as a cited black box. The matrix/finite-word reductions still need Lean implementations.

## Proposed Lean interface and placement

| Blueprint label | Proposed file / declarations | Key implementation requirements |
| --- | --- | --- |
| `qr:deuber-pattern` | `Sidon/Combinatorics/Deuber/Basic.lean`: `deuberRow`, `deuberPattern`, `IsRowRegular` | Use `Fin (m+1)` indices and finite coefficient vectors with `|λ| ≤ p`. Keep all arithmetic in `ℤ`. Positivity is a condition on the numerical pattern; it implies positive generators. |
| `qr:block-embedding`, `qr:block-composition` | same: `IsBlockEmbedding`, `IsBlockEmbedding.mul`, `IsBlockEmbedding.selectRows` | Define supports by nonzero integer matrix coefficients. Disjoint supports make every product entry have at most one nonzero summand, preventing cancellation. |
| Hales–Jewett bridge | `Sidon/Combinatorics/Deuber/Extraction.lean`: `exists_fin_wordLength`, `deuber_oneStep` | Import `Mathlib.Combinatorics.HalesJewett`; use the verified line theorem, `Fintype.equivFin`, and `Combinatorics.Line.idxFun`. Enumerate all nonempty-variable words over the finite alphabet, so the family of possible matrices is finite. |
| `qr:one-step` | same: `deuber_oneStep`, `deuber_oneStep_rows`, `deuber_oneStep_blockEmbedding` | Prove high-row containment, the middle-row HJ identification, and low-row containment using the maximum variable position. Do not omit the low-row containment, which ensures positivity of all new generators. |
| `qr:finite-deuber` | same: `exists_finite_deuber_extraction` | A finite recursion of depth `r*(q-1)`; the case `q=1` is a singleton. Produce `M,P,C,𝔽` before quantifying over numerical seeds and colourings. Every matrix in `𝔽` must have the block property, including matrices that happen not to be selected by a particular colouring. |
| `qr:kernel-matrix` | `Sidon/Combinatorics/QuantitativeRado/Kernel.lean`: `exists_fullRank_firstEntry_kernelMatrix` | Solve a nonzero one-row equation over `ℚ`, extend an independent list to a basis, clear finitely many denominators, reverse columns. Return injectivity explicitly; a rank equality can be a corollary. |
| `qr:positive-box` | `Sidon/Combinatorics/QuantitativeRado/Counting.lean`: `positiveSeedBox`, `card_positiveSeedBox_ge`, `deuberPattern_subset_interval` | Explicit geometric bounds and floor estimate `floor(N/H) ≥ N/(2H)` for `N≥2H`. The seed coordinates all lie in `[N]`, which is needed in the fiber bound. |
| `qr:multiplicity` | same: `card_blockEmbedding_fiber_le`, `card_finiteFamily_fiber_le` | Choose distinct pivot coordinates from row supports; restriction to their complement is injective. Count the complement as `M-q`, then union over the finite family. No determinant estimate or congruence uniqueness is required. |
| `qr:many-monochromatic` | `Sidon/Combinatorics/QuantitativeRado.lean`: `exists_many_monochromatic_linearSolutions` | Assemble extraction, kernel matrix, positive box, fiber estimate, and pigeonhole over colours. Return `∃ N₀, ∃ δ₀>0, ∀ N≥N₀, ∀ colouring, ∃ colour, …` with solution count allowing repeated coordinates. |

## Why the modified count is useful

The original proof selects seed coordinates in residue classes to recover each embedding from its output. A finite family of embeddings makes that recovery unnecessary: take a finite union bound over all patterns, losing only a constant depending on the coefficients and the number of colours. This also avoids needing a delicate balanced-base injectivity statement.

The original source's upper bound on each seed coordinate is insufficient by itself to ensure that every signed Deuber combination is positive. The explicit separated intervals above guarantee both lower and upper containment, while retaining a full `M` degrees of freedom.

The target is the single-equation theorem needed by Sidon, not an unproved generalization to arbitrary matrix systems. The only algebraic property required is the specific zero-sum subset condition and the nonvanishing of every coefficient. The construction works already for `s≥2`; the Sidon transference argument separately needs `s≥5` for its fourth-moment bound.

## Integration with the applications chapter

Replace the external proof marker at `app:fgr-dependency` with a reference to `qr:many-monochromatic`. Paper Lemma 5.2 follows by selecting a colour with weight at least `1/r` at each point; its exact extra loss remains `r^(-s)`. The rest of the partition-regularity proof and its parameter choices are unchanged.

No declarations in this plan are asserted to exist in the repository until implemented and checked. Do not add an axiom, a `sorry`, `set_option`, or `native_decide` to bridge any of the reductions.
