/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
import Sidon.NumberTheory.ZetaZeroCount
import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticGrowth
import Sidon.NumberTheory.RiemannGaussian.GaussianXiSubquadraticCounting

/-! # A crude multiplicity-sensitive zero count

The growth argument adapts the upstream three-halves proof while retaining
its stronger four-thirds Mellin exponent.
-/

noncomputable section

open RiemannGaussian MeromorphicOn Metric Set

namespace Sidon

def RiemannXiFourThirdsGrowth : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ,
    ‖riemannXi z‖ ≤
      Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ))

theorem riemannXi_fourThirdsGrowth : RiemannXiFourThirdsGrowth := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  let K : ℝ := max 1 (2 * C / p)
  let B : ℝ := mellinFourThirdsCoefficient p
  let A : ℝ := K + B + 4
  have hrawK0 : 0 ≤ 2 * C / p := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hrawK_le : 2 * C / p ≤ K := le_max_right _ _
  have hB0 : 0 ≤ B := mellinFourThirdsCoefficient_nonneg hp
  have hA1 : 1 ≤ A := by
    dsimp [A]
    linarith
  refine ⟨A, hA1, ?_⟩
  intro z
  let R : ℝ := ‖z‖ + 1
  let U : ℝ := R ^ (4 / 3 : ℝ)
  let T : ℝ := R ^ (4 / 3 : ℝ)
  let E : ℝ := Real.exp (B * U)
  have hR1 : 1 ≤ R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have hT1 : 1 ≤ T := by
    dsimp [T]
    calc
      (1 : ℝ) = 1 ^ (4 / 3 : ℝ) := by norm_num
      _ ≤ R ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hR1 (by norm_num)
  have hRleT : R ≤ T := by
    dsimp [T]
    calc
      R = R ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ R ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hUleT : U ≤ T := by
    dsimp [U, T]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  have hcompleted : ‖completedRiemannZeta₀ z‖ ≤ K * E := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * C / p) *
            Real.exp
              (mellinFourThirdsCoefficient p *
                (‖z‖ + 1) ^ (4 / 3 : ℝ)) :=
        norm_completedRiemannZeta₀_le_fourThirds hC hp htail z
      _ = (2 * C / p) * E := by simp only [B, E, U, R]
      _ ≤ K * E :=
        mul_le_mul_of_nonneg_right hrawK_le (Real.exp_nonneg _)
  have honeSub : ‖1 - z‖ ≤ R := by
    calc
      ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = R := by simp [R, add_comm]
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    linarith
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ R ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hzR honeSub (norm_nonneg _) hR0
  have hmain :
      ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ K * R ^ 2 * E := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤
          R ^ 2 * (K * E) :=
        mul_le_mul hpoly hcompleted (norm_nonneg _) (sq_nonneg R)
      _ = K * R ^ 2 * E := by ring
  have hRexp : R ≤ Real.exp R := by
    linarith [Real.add_one_le_exp R]
  have hRsqExp : R ^ 2 ≤ Real.exp (2 * R) := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ Real.exp R * Real.exp R :=
        mul_le_mul hRexp hRexp hR0 (Real.exp_nonneg _)
      _ = Real.exp (2 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have htwoExp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hKExp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hexponent : 1 + K + 2 * R + B * U ≤ A * T := by
    have hnonneg : 0 ≤ (K + B + 3) * (T - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [A]
    nlinarith
  have habsorb : 2 * (K * R ^ 2 * E) ≤ Real.exp (A * T) := by
    calc
      2 * (K * R ^ 2 * E) = 2 * K * R ^ 2 * E := by ring
      _ ≤ Real.exp 1 * Real.exp K * Real.exp (2 * R) * E := by
        gcongr
      _ = Real.exp (1 + K + 2 * R + B * U) := by
        simp only [E, ← Real.exp_add]
      _ ≤ Real.exp (A * T) := Real.exp_le_exp.mpr hexponent
  unfold riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ K * R ^ 2 * E + 1 := by
      simpa using add_le_add_right hmain 1
    _ ≤ 2 * (K * R ^ 2 * E) := by
      have hKRE1 : 1 ≤ K * R ^ 2 * E := by
        have hRtwo : 1 ≤ R ^ 2 := by nlinarith
        have hE1 : 1 ≤ E := by
          dsimp [E]
          rw [Real.one_le_exp_iff]
          exact mul_nonneg hB0 (Real.rpow_nonneg hR0 _)
        exact one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hK1 hRtwo) hE1
      linarith
    _ ≤ Real.exp (A * T) := habsorb
    _ = Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ)) := by rfl


theorem jensen_riemannXi_divisor_le_fourThirds
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * (‖z‖ + 1) ^ (4 / 3 : ℝ))) :
    ∑ᶠ u, divisor riemannXi (closedBall 0 r) u ≤
      A * (2 * r + 1) ^ (4 / 3 : ℝ) / Real.log 2 := by
  have hRpos : 0 < 2 * r := mul_pos (by norm_num) hr
  have hM :
      1 ≤ Real.exp (A * (2 * r + 1) ^ (4 / 3 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (le_trans (by norm_num) hA)
      (Real.rpow_nonneg (by positivity) _)
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := riemannXi) (c := (0 : ℂ)) (r := r) (R := 2 * r)
    (M := Real.exp (A * (2 * r + 1) ^ (4 / 3 : ℝ)))
    (by simpa [abs_of_pos hr] using hr)
    (by simp only [abs_of_pos hr, abs_of_pos hRpos]; linarith)
    hM
    (analyticOnNhd_riemannXi.mono (subset_univ _))
    (by norm_num)
    (by
      intro z hz
      have hnorm : ‖z‖ = 2 * r := by
        simpa [mem_sphere, abs_of_pos hRpos] using hz
      simpa [hnorm] using hbound z)
  have hratio : (2 * r) / r = 2 := by
    field_simp [hr.ne']
  rw [abs_of_pos hr] at hJensen
  simpa [riemannXi_zero, hratio, Real.log_exp] using hJensen

theorem isNontrivialZetaZero_of_mem_criticalZetaZeros {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ criticalZetaZeros T) : IsNontrivialZetaZero ρ := by
  obtain ⟨hzero, _, _, him, _⟩ := mem_criticalZetaZeros.mp hρ
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hh := congrArg Complex.im hn
    norm_num at hh
    linarith
  · intro hn
    have hh := congrArg Complex.im hn
    norm_num at hh
    linarith

theorem card_zetaZeroOccurrences (T : ℝ) :
    (zetaZeroOccurrences T).card =
      ∑ ρ ∈ criticalZetaZeros T, analyticOrderNatAt riemannZeta ρ := by
  classical
  unfold zetaZeroOccurrences
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro j k h
      exact (Prod.mk.inj h).2
  · intro ρ _ τ _ hne
    apply Finset.disjoint_left.mpr
    intro z hzρ hzτ
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzρ
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hzτ
    exact hne (congrArg Prod.fst (hj.trans hk.symm))

theorem zetaZeroCount_zero (T : ℝ) :
    zetaZeroCount 0 T = (zetaZeroOccurrences T).card := by
  unfold zetaZeroCount
  congr 1
  exact Finset.filter_true_of_mem fun z hz => (zetaZeroOccurrences_re_bounds hz).1

theorem zetaZeroCount_zero_le_riemannXi_divisor (T : ℝ) :
    (zetaZeroCount 0 T : ℝ) ≤
      ((∑ᶠ u, divisor riemannXi (closedBall 0 (T + 2)) u : ℤ) : ℝ) := by
  classical
  let S := (criticalZetaZeros T).subtype IsNontrivialZetaZero
  have hS : ∀ ρ ∈ S, ‖(ρ.1 : ℂ)‖ ≤ T + 2 := by
    intro ρ hρ
    have hmem : ρ.1 ∈ criticalZetaZeros T := (Finset.mem_subtype.mp hρ)
    obtain ⟨_, hre0, hre1, him0, himT⟩ := mem_criticalZetaZeros.mp hmem
    calc
      ‖(ρ.1 : ℂ)‖ ≤ |ρ.1.re| + |ρ.1.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ T + 2 := by
        rw [abs_of_nonneg hre0, abs_of_nonneg him0.le]
        linarith
  have hsum :
      ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) =
        (zetaZeroCount 0 T : ℝ) := by
    rw [zetaZeroCount_zero, card_zetaZeroOccurrences, Nat.cast_sum]
    exact Finset.sum_subtype_of_mem
      (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))
      (fun _ hρ => isNontrivialZetaZero_of_mem_criticalZetaZeros hρ)
  rw [← hsum]
  exact sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor S hS

theorem zetaZeroCount_zero_le_fourThirds :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (zetaZeroCount 0 T : ℝ) ≤ C * T ^ (4 / 3 : ℝ) := by
  obtain ⟨A, hA, hgrowth⟩ := riemannXi_fourThirdsGrowth
  refine ⟨A * 7 ^ (4 / 3 : ℝ) / Real.log 2, by positivity, ?_⟩
  intro T hT
  have hcount := (zetaZeroCount_zero_le_riemannXi_divisor T).trans
    (jensen_riemannXi_divisor_le_fourThirds hA (by linarith : 0 < T + 2) hgrowth)
  calc
    (zetaZeroCount 0 T : ℝ) ≤
        A * (2 * (T + 2) + 1) ^ (4 / 3 : ℝ) / Real.log 2 := hcount
    _ ≤ A * (7 * T) ^ (4 / 3 : ℝ) / Real.log 2 := by
      gcongr
      linarith
    _ = (A * 7 ^ (4 / 3 : ℝ) / Real.log 2) * T ^ (4 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T)]
      ring

theorem zetaZeroCount_le_fourThirds :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ σ : ℝ, 0 ≤ σ →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (4 / 3 : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := zetaZeroCount_zero_le_fourThirds
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  exact (Nat.cast_le.mpr (zetaZeroCount_antitone T hσ)).trans (hcount T hT)

theorem zetaZeroCount_le_fourThirds_add_one :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ σ : ℝ, 0 ≤ σ →
      (zetaZeroCount σ T : ℝ) ≤ C * (T + 1) ^ (4 / 3 : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := zetaZeroCount_le_fourThirds
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  exact (Nat.cast_le.mpr (zetaZeroCount_mono_height σ (by linarith : T ≤ T + 1))).trans
    (hcount (T + 1) (by linarith) σ hσ)

end Sidon
