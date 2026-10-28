module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Data.Int.Interval
public import Sidon.NumberTheory.RiemannGaussian.FiniteAbelVariation
public import Sidon.NumberTheory.RiemannGaussian.LogarithmicShiftPhase
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBlock
public import Sidon.NumberTheory.RiemannGaussian.ZetaFiniteDifferencing
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope

@[expose] public section

namespace RiemannGaussian.VinogradovKorobovDamping
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovKorobovBlock
def abelTransform (w F : ℕ → ℂ) (N : ℕ) : ℂ :=
  w N * F (N + 1) + ∑ n ∈ Finset.range N, (w n - w (n + 1)) * F (n + 1)

theorem weighted_identity (w f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * f n) =
      abelTransform w (block f) N :=
  FiniteAbelVariation.weighted_sum_eq w f N

theorem abel_length_mass (w : ℕ → ℝ) (N : ℕ) :
    w N * (N + 1 : ℕ) +
      (∑ n ∈ Finset.range N, (w n - w (n + 1)) * (n + 1 : ℕ)) =
      ∑ n ∈ Finset.range (N + 1), w n := by
  have h := FiniteAbelVariation.weighted_sum_eq (fun n => (w n : ℂ)) (fun _ => 1) N
  simpa using (congrArg Complex.re h).symm

theorem feature_eq_damped (s : ℂ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    zetaPrimeFeature s (a + n) =
      (zetaPrimeExpWeight s.re (a + n) : ℂ) * dirichletTerm s.im a n := by
  rw [ZetaFiniteDifferencing.feature_polar, dirichletTerm_eq (by exact_mod_cast ha)]
  simp only [basePhase, LogarithmicShiftPhase.phase, Nat.cast_add]

end
end RiemannGaussian.VinogradovKorobovDamping
