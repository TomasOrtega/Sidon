module

public import Sidon.NumberTheory.Tauberian.Wiener
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

@[expose] public section

/-! # The prime number theorem in Chebyshev's formulation

The Tauberian input is proved in the imported module. These consequences are adapted from
PrimeNumberTheoremAnd/Consequences.lean, commit 127b50e33f6033e2147921167a117af96d9ba4ea,
released under Apache 2.0 by the PrimeNumberTheoremAnd contributors.
-/

noncomputable section

namespace Sidon.NumberTheory

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Real Filter Topology Asymptotics
open scoped Chebyshev

theorem vonMangoldt_sum_Iic_tendsto :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (𝓝 1) := by
  have heq : (fun N : ℕ ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N : ℕ ↦ (∑ n ∈ range N, Λ n) / N + Λ N / N) := by
    ext N
    have hN : N ∈ Iic N := mem_Iic.mpr le_rfl
    rw [← Finset.sum_erase_add _ _ hN, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _
  rw [heq, ← add_zero 1]
  apply Tendsto.add Tauberian.WeakPNT
  convert squeeze_zero (f := fun N : ℕ ↦ Λ N / N)
    (g := fun N : ℕ ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · exact fun N ↦ div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · exact fun N ↦ div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have hlog : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact hlog.comp tendsto_natCast_atTop_atTop

theorem psi_isEquivalent : ψ ~[atTop] (fun x : ℝ ↦ x) := by
  rw [(by rfl : ψ = fun x ↦ ψ x)]
  simp_rw [Chebyshev.psi_eq_sum_Icc]
  apply IsEquivalent.trans (v := fun x : ℝ ↦ (⌊x⌋₊ : ℝ))
  · rw [isEquivalent_iff_tendsto_one]
    · convert! vonMangoldt_sum_Iic_tendsto.comp tendsto_nat_floor_atTop
      infer_instance
    rw [eventually_iff]
    simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
      Set.mem_ofPred_eq]
    exact ⟨1, by simp⟩
  apply IsLittleO.isEquivalent
  rw [← isLittleO_neg_left]
  apply IsLittleO.of_bound
  intro ε hε
  simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
  refine ⟨ε⁻¹, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := ((inv_pos_of_pos hε).trans_le hx).le
  rw [abs_of_nonneg, abs_of_nonneg hx0]
  · exact (by linarith [Nat.lt_floor_add_one x] : x - (⌊x⌋₊ : ℝ) ≤ 1).trans
      ((inv_le_iff_one_le_mul₀' hε).mp hx)
  · exact sub_nonneg.mpr (floor_le hx0)

theorem sqrt_mul_log_isLittleO :
    (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] (fun x ↦ x) := by
  refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (sqrt_ne_zero hx.le).mpr hx.ne'
  · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
    rw [div_sqrt, sqrt_eq_rpow]

theorem theta_isEquivalent : θ ~[atTop] (fun x : ℝ ↦ x) := by
  have herr : (ψ - θ) =o[atTop] (fun x : ℝ ↦ x) := by
    refine IsBigO.trans_isLittleO (g := fun x : ℝ ↦ 2 * x.sqrt * x.log) ?_ ?_
    · rw [isBigO_iff']
      refine ⟨1, one_pos, ?_⟩
      simp only [one_mul, eventually_atTop]
      refine ⟨2, fun x hx ↦ ?_⟩
      have hx0 : 0 ≤ x := by linarith
      have hlog : 0 ≤ log x := log_nonneg (by linarith)
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)
    · simpa only [mul_assoc] using sqrt_mul_log_isLittleO.const_mul_left 2
  convert psi_isEquivalent.sub_isLittleO herr using 1
  funext x
  simp

end Sidon.NumberTheory
