import Sidon.NumberTheory.SmoothedDetectorEstimate

/-! The fixed smoothing parameters and their decaying spectral errors. -/

noncomputable section

open RiemannGaussian Filter
open scoped Topology

namespace Sidon

def primeDetectorStep (x : ℝ) : ℝ := x ^ ((-1 : ℝ) / 3)
def primeDetectorHeight (x : ℝ) : ℝ := x ^ ((17 : ℝ) / 50)
def primeDetectorTime (x : ℝ) : ℝ := Real.log x - 128 * primeDetectorStep x
def primeDetectorScale (x : ℝ) : ℝ := x * primeDetectorStep x ^ 128

def primeDetectorZeroWeight (x : ℝ) : ℝ :=
  ∑ z ∈ zetaZeroOccurrences (primeDetectorHeight x),
    Real.exp (-Real.log x * (1 - z.1.re))

theorem primeDetectorStep_pos {x : ℝ} (hx : 0 < x) : 0 < primeDetectorStep x :=
  Real.rpow_pos_of_pos hx _

theorem primeDetectorHeight_pos {x : ℝ} (hx : 0 < x) : 0 < primeDetectorHeight x :=
  Real.rpow_pos_of_pos hx _

theorem primeDetectorScale_pos {x : ℝ} (hx : 0 < x) : 0 < primeDetectorScale x :=
  mul_pos hx (pow_pos (primeDetectorStep_pos hx) _)

theorem primeDetector_window (x : ℝ) :
    primeDetectorTime x + 128 * primeDetectorStep x = Real.log x := by
  unfold primeDetectorTime
  ring

theorem primeDetectorScale_eq {x : ℝ} (hx : 0 < x) :
    primeDetectorScale x = x ^ ((-125 : ℝ) / 3) := by
  have hp : primeDetectorStep x ^ 128 = x ^ ((-128 : ℝ) / 3) := by
    unfold primeDetectorStep
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  unfold primeDetectorScale
  rw [hp]
  calc
    _ = x ^ (1 : ℝ) * x ^ ((-128 : ℝ) / 3) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + (-128 : ℝ) / 3) := (Real.rpow_add hx _ _).symm
    _ = _ := by norm_num

theorem primeDetector_high_error_eq {x : ℝ} (hx : 0 < x) (M : ℝ) :
    (x * 2 ^ 128 / primeDetectorHeight x ^ 126) * M =
      primeDetectorScale x * ((2 ^ 128 * M) * x ^ ((-13 : ℝ) / 75)) := by
  have hheight : primeDetectorHeight x ^ 126 = x ^ ((1071 : ℝ) / 25) := by
    unfold primeDetectorHeight
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have hquot : x / x ^ ((1071 : ℝ) / 25) = x ^ ((-1046 : ℝ) / 25) := by
    calc
      _ = x ^ (1 : ℝ) / x ^ ((1071 : ℝ) / 25) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) - 1071 / 25) := (Real.rpow_sub hx _ _).symm
      _ = _ := by norm_num
  rw [hheight, primeDetectorScale_eq hx]
  calc
    _ = (2 ^ 128 * M) * (x / x ^ ((1071 : ℝ) / 25)) := by ring
    _ = (2 ^ 128 * M) * x ^ ((-1046 : ℝ) / 25) := by rw [hquot]
    _ = _ := by
      have hp : x ^ ((-1046 : ℝ) / 25) =
          x ^ ((-125 : ℝ) / 3) * x ^ ((-13 : ℝ) / 75) := by
        rw [← Real.rpow_add hx]
        norm_num
      rw [hp]
      ring

theorem primeDetector_trivial_error_eq {x : ℝ} (hx : 0 < x) :
    (Real.pi ^ 2 / 6) * primeDetectorStep x ^ 126 =
      primeDetectorScale x * ((Real.pi ^ 2 / 6) * x ^ ((-1 : ℝ) / 3)) := by
  rw [primeDetectorScale_eq hx]
  unfold primeDetectorStep
  rw [← Real.rpow_mul_natCast hx.le]
  calc
    _ = (Real.pi ^ 2 / 6) * x ^ ((-42 : ℝ)) := by norm_num
    _ = _ := by
      have hp : x ^ (-42 : ℝ) = x ^ ((-125 : ℝ) / 3) * x ^ ((-1 : ℝ) / 3) := by
        rw [← Real.rpow_add hx]
        norm_num
      rw [hp]
      ring

theorem mul_primeDetectorStep_eq {x : ℝ} (hx : 0 < x) :
    x * primeDetectorStep x = x ^ ((2 : ℝ) / 3) := by
  calc
    _ = x ^ (1 : ℝ) * x ^ ((-1 : ℝ) / 3) := by rw [Real.rpow_one]; rfl
    _ = x ^ ((1 : ℝ) + (-1 : ℝ) / 3) := (Real.rpow_add hx _ _).symm
    _ = _ := by norm_num

theorem tendsto_primeDetectorStep : Tendsto primeDetectorStep atTop (𝓝 0) := by
  change Tendsto (fun x : ℝ => x ^ ((-1 : ℝ) / 3)) atTop (𝓝 0)
  simpa only [neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3))

theorem tendsto_primeDetector_high_ratio (M : ℝ) :
    Tendsto (fun x : ℝ => (2 ^ 128 * M) * x ^ ((-13 : ℝ) / 75)) atTop (𝓝 0) := by
  simpa only [mul_zero, neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 75)).const_mul (2 ^ 128 * M)

theorem tendsto_primeDetector_trivial_ratio :
    Tendsto (fun x : ℝ => (Real.pi ^ 2 / 6) * x ^ ((-1 : ℝ) / 3)) atTop (𝓝 0) := by
  simpa only [primeDetectorStep, mul_zero] using tendsto_primeDetectorStep.const_mul (Real.pi ^ 2 / 6)

end Sidon
