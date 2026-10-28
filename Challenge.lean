module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Int.Interval

/-!
# Extremal Sidon sets

Statements from Ortega and Prendiville, *Extremal Sidon sets are Fourier uniform,
with applications to partition regularity* (2023), DOI: 10.5802/jtnb.1239.
The interval is `{1, ..., N}`. Fourier sums use the positive exponential and
have no normalization. Norms of continuous maps are supremum norms.
The product torus has the maximum metric. Solution tuples may repeat entries.

The theorem holes are deliberate. `Solution` proves the same statements.
The concrete definitions below are part of the statement being checked.
-/

@[expose] public section
noncomputable section

open scoped BigOperators
open Filter Topology

namespace SidonSubmission

/-- Pair sums in a Sidon set determine the unordered pair. Repeated entries are allowed. -/
def IsSidonSet {M : Type*} [AddCommMonoid M] (s : Set M) : Prop :=
  ∀ a b c d, a ∈ s → b ∈ s → c ∈ s → d ∈ s →
  a + b = c + d → ({a, b} : Set M) = ({c, d} : Set M)

/-- The integers from `1` to `N`, including both endpoints. -/
def interval (N : ℕ) : Finset ℤ := Finset.Icc 1 N

/-- The complex indicator of a finite set of integers. -/
def indicatorFinsupp (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.indicator s fun _ _ => 1

/-- The sum of `f(n) exp(2πinα)`, as a continuous function of `α`. -/
def fourierSum (f : ℤ →₀ ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  f.sum fun n c => c • fourier n

/-- The distance of `|S| / √N` from one. -/
def sidonDeviation (N : ℕ) (S : Finset ℤ) : ℝ :=
  |(S.card : ℝ) / Real.sqrt N - 1|

/-- A Sidon subset of the interval with largest possible cardinality. -/
def IsMaximumSidon (N : ℕ) (S : Finset ℤ) : Prop :=
  IsSidonSet (S : Set ℤ) ∧ S ⊆ interval N ∧
    ∀ T : Finset ℤ, IsSidonSet (T : Set ℤ) → T ⊆ interval N → T.card ≤ S.card

/-- The first `L` terms `a, a+q, ..., a+(L-1)q`. -/
def arithmeticProgression (a q : ℤ) (L : ℕ) : Finset ℤ :=
  (Finset.range L).image fun j : ℕ => a + q * (j : ℤ)

/-- Tuples in `A` that satisfy the homogeneous equation with coefficients `c`. -/
def linearSolutions {ι : Type*} [Fintype ι] (A : Finset ℤ) (c : ι → ℤ) :
    Finset (ι → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => A).filter fun x => ∑ i, c i * x i = 0

/-- Integers in the interval whose torus orbit lies in the closed ball of radius `ρ`. -/
def bohrSet {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) : Finset ℤ :=
  (interval N).filter fun x => ‖x • α‖ ≤ ρ

/-- The size changes by at most `100d|κ|` of its size under a small radius change. -/
def IsRegularBohrSet {d : ℕ} (N : ℕ) (α : Fin d → AddCircle (1 : ℝ)) (ρ : ℝ) : Prop :=
  ∀ κ : ℝ, |κ| ≤ 1 / (100 * (d : ℝ)) →
    |((bohrSet N α ((1 + κ) * ρ)).card : ℝ) - (bohrSet N α ρ).card| ≤
      100 * (d : ℝ) * |κ| * (bohrSet N α ρ).card

/-- The character `exp(2πi ∑ⱼ nⱼβⱼ)` on the product torus. -/
def torusCharacter {d : ℕ} (n : Fin d → ℤ) : C(Fin d → AddCircle (1 : ℝ), ℂ) :=
  UnitAddTorus.mFourier n

/-- A finite linear combination of torus characters with coefficients `a`. -/
def torusPolynomial {d : ℕ} (a : (Fin d → ℤ) →₀ ℂ) :
    C(Fin d → AddCircle (1 : ℝ), ℂ) :=
  a.sum fun n c => c • torusCharacter n

/-- Every coordinate frequency in the support is at most `M` in absolute value. -/
def HasTorusBandwidth {d : ℕ} (a : (Fin d → ℤ) →₀ ℂ) (M : ℕ) : Prop :=
  ∀ n ∈ a.support, ∀ i, |n i| ≤ (M : ℤ)

/-- Theorem 1.2: near-extremal Sidon sets have small Fourier discrepancy, with constant 16. -/
theorem sidon_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    ‖fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
      16 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  sorry

/-- Theorem 6.3: the term inside the square root improves to `N^(-1/4)`, with constant 36. -/
theorem sidon_improved_fourier_uniformity {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    ‖fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
      36 * Real.sqrt N * Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
  sorry

/-- Corollary 1.4: maximum Sidon sets have relative Fourier error `O(N^(-1/12))`. -/
theorem largest_sidon_fourier_uniformity :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, IsMaximumSidon N S →
      ‖fourierSum (indicatorFinsupp S) -
        ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
        K * ‖fourierSum (indicatorFinsupp S)‖ * (N : ℝ) ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- Theorem 3.1: counts in each finite progression are close to the constant-density model. -/
theorem sidon_progression_equidistribution {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (a q : ℤ) (L : ℕ) (hq : q ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    |((S ∩ arithmeticProgression a q L).card : ℝ) -
        ((S.card : ℝ) / N) * (interval N ∩ arithmeticProgression a q L).card| ≤
      (16 * (2 + Real.log 2 + 1 / ε)) * (N : ℝ) ^ ((1 / 2 : ℝ) + ε) *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) := by
  sorry

/-- Corollary 1.7: bounded Lipschitz functions have close averages on the two torus orbits. -/
theorem sidon_smooth_equidistribution {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card)
    (F : C(Fin d → AddCircle (1 : ℝ), ℝ)) (K : ℝ) (hK : 1 ≤ K)
    (hF : LipschitzWith (Real.toNNReal K) F) (hF0 : ∀ β, 0 ≤ F β) (hF1 : ∀ β, F β ≤ 1)
    (α : Fin d → AddCircle (1 : ℝ)) :
    |(𝔼 x ∈ S, F (x • α)) - (𝔼 x ∈ interval N, F (x • α))| ≤
      48000 * K ^ (2 / 3 : ℝ) *
        (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ^ (1 / (8 * (d : ℝ))) := by
  sorry

/-- Corollary 1.11: regular Bohr sets have close relative densities in `S` and in the interval. -/
theorem sidon_regular_bohr_equidistribution {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {S : Finset ℤ} (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N)
    (hm : Real.sqrt N / 100 ≤ S.card) (α : Fin d → AddCircle (1 : ℝ))
    {ρ : ℝ} (hρ : 0 < ρ) (hreg : IsRegularBohrSet N α ρ) :
    |((S ∩ bohrSet N α ρ).card : ℝ) / S.card - (bohrSet N α ρ).card / N| ≤
      48100 * ((d : ℝ) / ρ) *
        (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) ^ (1 / (14 * (d : ℝ))) := by
  sorry

/-- Theorem 1.15: each finite colouring has many solutions when a nonempty coefficient sum is zero. -/
theorem sidon_partition_regularity {s r : ℕ} (hs : 5 ≤ s) (hr : 0 < r)
    (c : Fin s → ℤ) (hc : ∀ i, c i ≠ 0) (I : Finset (Fin s))
    (hIne : I.Nonempty) (hI : ∑ i ∈ I, c i = 0) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℤ,
        IsSidonSet (S : Set ℤ) → S ⊆ interval N →
        |(S.card : ℝ) - Real.sqrt N| ≤ γ * Real.sqrt N →
        ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
          κ * (S.card : ℝ) ^ s / N ≤
            (linearSolutions (S.filter (fun n => χ n = colour)) c).card := by
  sorry

/-- Proposition 1.13: sets of asymptotic size `√(N/2)` can avoid `a+b+c+d=e`. -/
theorem eventually_exists_sharp_odd_obstruction {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℤ, S ⊆ interval N ∧
      (1 / Real.sqrt 2 - δ) * Real.sqrt N ≤ S.card ∧ IsSidonSet (S : Set ℤ) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, a + b + c + d ≠ e := by
  sorry

/-- Remark 1.14: a nonzero total coefficient sum admits Sidon sets of size `Ω(√N)` with no solution. -/
theorem exists_eventually_sharp_residue_obstruction {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (hσ : (∑ i, a i) ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℤ,
      S ⊆ interval N ∧ (1 / Real.sqrt q - δ) * Real.sqrt N ≤ S.card ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ x : ι → ℤ, (∀ i, x i ∈ S) → (∑ i, a i * x i) ≠ 0 := by
  sorry

/-- Remark 1.16: if no nonempty coefficient sum is zero, one finite colouring avoids positive solutions. -/
theorem QuantitativeRado.exists_integer_colouring_without_positive_monochromatic_linearSolution
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℤ)
    (ha : ∀ I : Finset ι, I.Nonempty → (∑ i ∈ I, a i) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ χ : ℤ → Fin r, ∀ x : ι → ℤ,
      (∀ i, 0 < x i) → (∀ i j, χ (x i) = χ (x j)) →
        (∑ i, a i * x i) ≠ 0 := by
  sorry

/-- Correction to Lemma 4.1: one finite bandwidth cannot approximate all dimensions, even at error `1/16`. -/
theorem BandwidthCounterexample.not_exists_uniform_dimension_bandwidth :
    ¬ ∃ M : ℕ, ∀ d : ℕ, 0 < d →
      ∀ F : C(Fin d → AddCircle (1 : ℝ), ℝ),
        (∀ β, F β ∈ Set.Icc (0 : ℝ) 1) → LipschitzWith 1 F →
        ∃ a : (Fin d → ℤ) →₀ ℂ, HasTorusBandwidth a M ∧
          ∀ β, ‖(F β : ℂ) - torusPolynomial a β‖ ≤ 1 / 16 := by
  sorry

/-- Appendix A: a Sidon subset of the interval has size at most `√N + 4N^(1/4)`. -/
theorem IsSidonSet.card_le_sqrt_add_four_mul_rpow {N : ℕ} (hN : 0 < N) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (hSN : S ⊆ interval N) :
    (S.card : ℝ) ≤ Real.sqrt N + 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  sorry

end SidonSubmission
