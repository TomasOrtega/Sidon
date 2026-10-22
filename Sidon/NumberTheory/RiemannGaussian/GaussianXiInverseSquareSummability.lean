/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticCounting
import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticGrowth
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaBridge
import Sidon.NumberTheory.RiemannGaussian.GaussianZetaCounting

namespace RiemannGaussian

noncomputable section

open MeromorphicOn Metric Set
def zetaZeroNormDyadicIndex (rho : NontrivialZetaZero) : ℕ :=
  Nat.find
    (pow_unbounded_of_one_lt ‖(rho.1 : ℂ)‖
      (by norm_num : (1 : ℝ) < 2))

theorem norm_lt_two_pow_zetaZeroNormDyadicIndex
    (rho : NontrivialZetaZero) :
    ‖(rho.1 : ℂ)‖ < (2 : ℝ) ^ zetaZeroNormDyadicIndex rho := by
  exact Nat.find_spec
    (pow_unbounded_of_one_lt ‖(rho.1 : ℂ)‖
      (by norm_num : (1 : ℝ) < 2))

theorem two_pow_le_norm_of_zetaZeroNormDyadicIndex_eq_succ
    (rho : NontrivialZetaZero) {n : ℕ}
    (hindex : zetaZeroNormDyadicIndex rho = n + 1) :
    (2 : ℝ) ^ n ≤ ‖(rho.1 : ℂ)‖ := by
  apply le_of_not_gt
  intro hlt
  have hmin := Nat.find_min
    (pow_unbounded_of_one_lt ‖(rho.1 : ℂ)‖
      (by norm_num : (1 : ℝ) < 2))
    (show n < zetaZeroNormDyadicIndex rho by omega)
  exact hmin hlt

theorem zetaZeroNormDyadicShell_finite (n : ℕ) :
    {rho : NontrivialZetaZero |
      zetaZeroNormDyadicIndex rho = n}.Finite := by
  let B : Set ℂ :=
    closedBall (0 : ℂ) ((2 : ℝ) ^ n) ∩ nontrivialZetaZeroSet
  have hB : B.Finite := by
    dsimp [B]
    exact IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) ((2 : ℝ) ^ n))
  have hpre :
      ((fun rho : NontrivialZetaZero => (rho.1 : ℂ)) ⁻¹' B).Finite :=
    hB.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro rho hrho
  change (rho.1 : ℂ) ∈ B
  refine ⟨?_, rho.2⟩
  have hnorm := norm_lt_two_pow_zetaZeroNormDyadicIndex rho
  rw [hrho] at hnorm
  simpa [mem_closedBall] using hnorm.le

theorem tsum_zetaZeroNormDyadicShell_multiplicity_le
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    ∑' rho : {rho : NontrivialZetaZero |
        zetaZeroNormDyadicIndex rho = n},
      (analyticZetaZeroMultiplicity rho.1 : ℝ) ≤
        A * (2 * (2 : ℝ) ^ n + 1) ^ (3 / 2 : ℝ) /
          Real.log 2 := by
  classical
  let shell : Set NontrivialZetaZero :=
    {rho | zetaZeroNormDyadicIndex rho = n}
  let : Fintype shell := (zetaZeroNormDyadicShell_finite n).fintype
  let S : Finset NontrivialZetaZero :=
    Finset.univ.image (fun rho : shell => rho.1)
  have hSinBall :
      ∀ rho ∈ S, ‖(rho.1 : ℂ)‖ ≤ (2 : ℝ) ^ n := by
    intro rho hrho
    rcases Finset.mem_image.mp hrho with ⟨sigma, -, rfl⟩
    have hnorm := norm_lt_two_pow_zetaZeroNormDyadicIndex sigma.1
    rw [sigma.2] at hnorm
    exact hnorm.le
  have hsumEq :
      ∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℝ) =
        ∑ rho : shell,
          (analyticZetaZeroMultiplicity rho.1 : ℝ) := by
    dsimp [S]
    rw [Finset.sum_image]
    simp
  rw [tsum_fintype, ← hsumEq]
  exact (sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor
    S hSinBall).trans
      (jensen_riemannXi_divisor_le_threeHalves hA (by positivity) hbound)

def riemannXiInverseSquareDyadicMajorant (A : ℝ) : ℕ → ℝ
  | 0 => A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2
  | n + 1 =>
      (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
        Real.exp (-(Real.log 2 / 2) * (n : ℝ))

theorem summable_riemannXiInverseSquareDyadicMajorant (A : ℝ) :
    Summable (riemannXiInverseSquareDyadicMajorant A) := by
  have hc : 0 < Real.log 2 / 2 := by positivity
  have h := Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  apply (summable_nat_add_iff 1).mp
  simpa [riemannXiInverseSquareDyadicMajorant] using
    h.mul_left (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2)

theorem two_pow_rpow_threeHalves_div_sq (n : ℕ) :
    ((2 : ℝ) ^ n) ^ (3 / 2 : ℝ) / ((2 : ℝ) ^ n) ^ 2 =
      Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ n) 2]
  rw [← Real.rpow_sub (by positivity : 0 < (2 : ℝ) ^ n)]
  rw [Real.rpow_def_of_pos (by positivity : 0 < (2 : ℝ) ^ n),
    Real.log_pow]
  congr 1
  norm_num
  ring

theorem two_mul_two_pow_succ_add_one_le (n : ℕ) :
    2 * (2 : ℝ) ^ (n + 1) + 1 ≤ 5 * (2 : ℝ) ^ n := by
  have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  nlinarith

theorem tsum_zetaZeroNormDyadicShell_inverseSquare_le
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) :
    ∑' rho : {rho : NontrivialZetaZero |
        zetaZeroNormDyadicIndex rho = n},
      (analyticZetaZeroMultiplicity rho.1 : ℝ) /
        (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤
      riemannXiInverseSquareDyadicMajorant A n := by
  classical
  let shell : Set NontrivialZetaZero :=
    {rho | zetaZeroNormDyadicIndex rho = n}
  let : Fintype shell := (zetaZeroNormDyadicShell_finite n).fintype
  have hcount :
      ∑ rho : shell, (analyticZetaZeroMultiplicity rho.1 : ℝ) ≤
        A * (2 * (2 : ℝ) ^ n + 1) ^ (3 / 2 : ℝ) /
          Real.log 2 := by
    have h :=
      tsum_zetaZeroNormDyadicShell_multiplicity_le hA hbound n
    rw [tsum_fintype] at h
    exact h
  rw [tsum_fintype]
  cases n with
  | zero =>
      calc
        ∑ rho : shell,
            (analyticZetaZeroMultiplicity rho.1 : ℝ) /
              (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤
            ∑ rho : shell,
              (analyticZetaZeroMultiplicity rho.1 : ℝ) := by
          apply Finset.sum_le_sum
          intro rho _hrho
          exact div_le_self (Nat.cast_nonneg _)
            (by nlinarith [sq_nonneg ‖(rho.1.1 : ℂ)‖])
        _ ≤ A * (2 * (2 : ℝ) ^ (0 : ℕ) + 1) ^
              (3 / 2 : ℝ) / Real.log 2 := hcount
        _ ≤ riemannXiInverseSquareDyadicMajorant A 0 := by
          simp only [pow_zero, riemannXiInverseSquareDyadicMajorant]
          norm_num
          apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num))
            (by linarith)
  | succ n =>
      have hlower (rho : shell) :
          (2 : ℝ) ^ n ≤ ‖(rho.1.1 : ℂ)‖ := by
        apply two_pow_le_norm_of_zetaZeroNormDyadicIndex_eq_succ rho.1
        exact rho.2
      have hweighted :
          ∑ rho : shell,
              (analyticZetaZeroMultiplicity rho.1 : ℝ) /
                (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤
            (∑ rho : shell,
              (analyticZetaZeroMultiplicity rho.1 : ℝ)) /
                ((2 : ℝ) ^ n) ^ 2 := by
        calc
          ∑ rho : shell,
              (analyticZetaZeroMultiplicity rho.1 : ℝ) /
                (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤
              ∑ rho : shell,
                (analyticZetaZeroMultiplicity rho.1 : ℝ) /
                  ((2 : ℝ) ^ n) ^ 2 := by
            apply Finset.sum_le_sum
            intro rho _hrho
            apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
              (by positivity)
            have hsquare :
                ((2 : ℝ) ^ n) ^ 2 ≤
                  ‖(rho.1.1 : ℂ)‖ ^ 2 := by
              nlinarith [hlower rho, norm_nonneg (rho.1.1 : ℂ),
                (show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity)]
            nlinarith
          _ = (∑ rho : shell,
                (analyticZetaZeroMultiplicity rho.1 : ℝ)) /
                  ((2 : ℝ) ^ n) ^ 2 := by
            rw [Finset.sum_div]
      calc
        ∑ rho : shell,
            (analyticZetaZeroMultiplicity rho.1 : ℝ) /
              (1 + ‖(rho.1.1 : ℂ)‖ ^ 2) ≤
            (∑ rho : shell,
              (analyticZetaZeroMultiplicity rho.1 : ℝ)) /
                ((2 : ℝ) ^ n) ^ 2 := hweighted
        _ ≤
            (A * (2 * (2 : ℝ) ^ (n + 1) + 1) ^
              (3 / 2 : ℝ) / Real.log 2) /
                ((2 : ℝ) ^ n) ^ 2 :=
          div_le_div_of_nonneg_right hcount (sq_nonneg _)
        _ ≤
            (A * (5 * (2 : ℝ) ^ n) ^ (3 / 2 : ℝ) /
              Real.log 2) / ((2 : ℝ) ^ n) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          apply div_le_div_of_nonneg_right _
            (Real.log_pos (by norm_num)).le
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity)
              (two_mul_two_pow_succ_add_one_le n) (by norm_num))
            (by linarith)
        _ = riemannXiInverseSquareDyadicMajorant A (n + 1) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          rw [show
            A * ((5 : ℝ) ^ (3 / 2 : ℝ) *
                  ((2 : ℝ) ^ n) ^ (3 / 2 : ℝ)) /
                Real.log 2 / ((2 : ℝ) ^ n) ^ 2 =
              (A * (5 : ℝ) ^ (3 / 2 : ℝ) / Real.log 2) *
                (((2 : ℝ) ^ n) ^ (3 / 2 : ℝ) /
                  ((2 : ℝ) ^ n) ^ 2) by ring,
            two_pow_rpow_threeHalves_div_sq]
          simp only [riemannXiInverseSquareDyadicMajorant]

theorem summable_distinct_zetaZeroInverseSquareNorm_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ))) :
    Summable fun rho : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + ‖(rho.1 : ℂ)‖ ^ 2) := by
  let shell : ℕ → Set NontrivialZetaZero := fun n =>
    {rho | zetaZeroNormDyadicIndex rho = n}
  apply (summable_partition
    (f := fun rho : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + ‖(rho.1 : ℂ)‖ ^ 2))
    (fun rho => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (s := shell) (by
      intro rho
      refine ⟨zetaZeroNormDyadicIndex rho, rfl, ?_⟩
      intro n hn
      exact hn.symm)).2
  constructor
  · intro n
    let : Fintype (shell n) := (zetaZeroNormDyadicShell_finite n).fintype
    exact Summable.of_finite
  · apply
      (summable_riemannXiInverseSquareDyadicMajorant A).of_nonneg_of_le
        (fun n => tsum_nonneg fun rho =>
          div_nonneg (Nat.cast_nonneg _) (by positivity))
    intro n
    exact tsum_zetaZeroNormDyadicShell_inverseSquare_le hA hbound n

theorem summable_distinct_zetaZeroInverseSquareNorm :
    Summable fun rho : NontrivialZetaZero =>
      (analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + ‖(rho.1 : ℂ)‖ ^ 2) := by
  rcases riemannXi_threeHalvesGrowth with ⟨A, hA, hbound⟩
  exact summable_distinct_zetaZeroInverseSquareNorm_of_growth hA hbound

end

end RiemannGaussian
