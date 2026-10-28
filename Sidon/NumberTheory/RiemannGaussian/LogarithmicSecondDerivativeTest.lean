module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.LogarithmicShiftPhase
public import Sidon.NumberTheory.RiemannGaussian.SecondDerivativeTest

@[expose] public section

namespace RiemannGaussian.LogarithmicSecondDerivativeTest
noncomputable section
open RiemannGaussian.PhaseIncrementInverse RiemannGaussian.LogarithmicShiftPhase
theorem hasDerivAt_first (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ -t / y) (t / x ^ 2) x := by
  convert! (hasDerivAt_const x (-t)).div (hasDerivAt_id x) hx.ne' using 1
  simp only [zero_mul, mul_one, zero_sub, neg_neg, id_eq]

theorem curvature_bounds {t x X : ℝ} (ht : 0 ≤ t) (hX : 0 < X)
    (hl : X ≤ x) (hu : x ≤ 2 * X) :
    t / (4 * X ^ 2) ≤ t / x ^ 2 ∧ t / x ^ 2 ≤ t / X ^ 2 := by
  have hx : 0 < x := hX.trans_le hl
  have hlo : X ^ 2 ≤ x ^ 2 := sq_le_sq₀ hX.le hx.le |>.mpr hl
  have hhi : x ^ 2 ≤ 4 * X ^ 2 := by nlinarith
  exact ⟨div_le_div_of_nonneg_left ht (sq_pos_of_pos hx) hhi,
    div_le_div_of_nonneg_left ht (sq_pos_of_pos hX) hlo⟩

theorem square_root_bound {t X a : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (htX : t ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      (4 * N * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
        2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X := ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have he : 4 * (t / (4 * X ^ 2)) = t / X ^ 2 := by ring
  apply SecondDerivativeTest.square_root_bound (phase t) (fun x ↦ -t / x)
    (fun x ↦ t / x ^ 2) a N (by positivity)
    ((div_le_one (by positivity : 0 < 4 * X ^ 2)).mpr htX) (by norm_num)
    (fun _ hx ↦ hasDerivAt_phase t (hdom hx).1)
    (fun _ hx ↦ hasDerivAt_first t (hdom hx).1)
  intro x hx
  rw [he]
  exact curvature_bounds ht.le hX (hdom hx).2.1 (hdom hx).2.2

end
end RiemannGaussian.LogarithmicSecondDerivativeTest
