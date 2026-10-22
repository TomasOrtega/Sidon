/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.DerivativeOrderComparison
import Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
import Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
import Sidon.NumberTheory.RiemannGaussian.DirichletCriticalRange
import Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters

namespace RiemannGaussian.DirichletTransitionWindows
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.DirichletBlockPowerProfile
theorem profile_on_later_line (r k : ℕ) (t X : ℝ) :
    profile r (line k) t X =
      256 * t ^ alpha r * X ^ (delta k - delta r) +
      64 * t ^ (-alpha r) * X ^ (delta k - amp r + delta r) := by
  unfold profile line delta beta
  congr 2 <;> congr 1 <;> ring

theorem complementary_balance (r k : ℕ) :
    -alpha r + transition r * (delta k - amp r + delta r) =
      alpha r + transition r * (delta k - delta r) := by
  have h := transition_balance r
  have hs : DirichletPowerParameters.slope r = 2 * delta r - amp r := by
    unfold DirichletPowerParameters.slope delta
    ring
  rw [hs] at h
  nlinarith

theorem profile_le_on_window (r k : ℕ) (hrk : r ≤ k) {t X : ℝ}
    (ht : 1 ≤ t) (hX : 0 < X)
    (hlower : t ^ transition (r + 1) ≤ X) (hupper : X ≤ t ^ transition r) :
    profile r (line k) t X ≤ 320 * t ^ alpha k := by
  have htpos : 0 < t := by linarith
  have ha : delta k - delta r ≤ 0 := sub_nonpos.mpr (delta_antitone hrk)
  have hb : 0 ≤ delta k - amp r + delta r := by
    linarith [amp_le_delta r, delta_pos k]
  have hlead := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos htpos (transition (r + 1))) hlower ha
  rw [← Real.rpow_mul htpos.le] at hlead
  have hlead' := mul_le_mul_of_nonneg_left hlead (Real.rpow_nonneg htpos.le (alpha r))
  rw [← Real.rpow_add htpos] at hlead'
  have hlead'' := Real.rpow_le_rpow_of_exponent_le ht (order_comparison r k hrk)
  have hcomp := Real.rpow_le_rpow hX.le hupper hb
  rw [← Real.rpow_mul htpos.le] at hcomp
  have hcomp' := mul_le_mul_of_nonneg_left hcomp (Real.rpow_nonneg htpos.le (-alpha r))
  rw [← Real.rpow_add htpos, complementary_balance] at hcomp'
  have he : alpha r + transition r * (delta k - delta r) ≤ alpha k := by
    have hm := mul_le_mul_of_nonpos_right (transition_succ_le r) ha
    linarith [order_comparison r k hrk]
  have hcomp'' := Real.rpow_le_rpow_of_exponent_le ht he
  rw [profile_on_later_line]
  nlinarith

theorem window_cover (k : ℕ) {t X : ℝ} (hupper : X ≤ t) :
    X ≤ t ^ transition k ∨
      ∃ r < k, t ^ transition (r + 1) ≤ X ∧ X ≤ t ^ transition r := by
  induction k with
  | zero => left; simpa [transition_zero] using hupper
  | succ k ih =>
    by_cases h : X ≤ t ^ transition (k + 1)
    · exact Or.inl h
    · right
      rcases ih with hi | ⟨r, hr, hlo, hhi⟩
      · exact ⟨k, Nat.lt_succ_self k, (lt_of_not_ge h).le, hi⟩
      · exact ⟨r, Nat.lt_succ_of_lt hr, hlo, hhi⟩

theorem exists_order_bound (k : ℕ) {t X : ℝ} (ht : 1 ≤ t) (hX : 0 < X)
    (hupper : X ≤ t) :
    ∃ r ≤ k, profile r (line k) t X ≤ 320 * t ^ alpha k := by
  rcases window_cover k hupper with h | ⟨r, hr, hlo, hhi⟩
  · exact ⟨k, le_rfl, DirichletCriticalRange.profile_le_on_range k
      (by linarith) hX h⟩
  · exact ⟨r, hr.le, profile_le_on_window r k hr.le ht hX hlo hhi⟩

end
end RiemannGaussian.DirichletTransitionWindows
