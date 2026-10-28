module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! # Gaussian weighted integrals from symmetric cumulative bounds -/

noncomputable section

open Set MeasureTheory

namespace Sidon

def gaussianAnnulus (R : ℝ) (n : ℕ) : Set ℝ :=
  {t | Nat.floor (|t| / R) = n}

theorem measurableSet_gaussianAnnulus (R : ℝ) (n : ℕ) :
    MeasurableSet (gaussianAnnulus R n) := by
  unfold gaussianAnnulus
  have hm : Measurable (fun t : ℝ => |t| / R) := by fun_prop
  exact (Nat.measurable_floor.comp hm) (measurableSet_singleton n)

theorem gaussianAnnulus_bounds {R t : ℝ} (hR : 0 < R) {n : ℕ}
    (ht : t ∈ gaussianAnnulus R n) :
    (n : ℝ) * R ≤ |t| ∧ |t| ≤ ((n : ℝ) + 1) * R := by
  have hnonneg : 0 ≤ |t| / R := div_nonneg (abs_nonneg _) hR.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one (|t| / R)
  change Nat.floor (|t| / R) = n at ht
  rw [ht] at hlo hhi
  exact ⟨(le_div_iff₀ hR).mp hlo, ((div_lt_iff₀ hR).mp hhi).le⟩

theorem gaussianAnnulus_subset {R : ℝ} (hR : 0 < R) (n : ℕ) :
    gaussianAnnulus R n ⊆ Icc (-(((n : ℝ) + 1) * R)) (((n : ℝ) + 1) * R) := by
  intro t ht
  exact abs_le.mp (gaussianAnnulus_bounds hR ht).2

theorem gaussianAnnulus_cover (R : ℝ) : (⋃ n : ℕ, gaussianAnnulus R n) = univ := by
  apply eq_univ_of_forall
  intro t
  exact mem_iUnion.mpr ⟨Nat.floor (|t| / R), rfl⟩

theorem gaussianAnnulus_disjoint (R : ℝ) :
    Pairwise (fun m n => Disjoint (gaussianAnnulus R m) (gaussianAnnulus R n)) := by
  intro m n hmn
  apply disjoint_left.mpr
  intro t htm htn
  exact hmn (htm.symm.trans htn)

theorem gaussian_weight_le_on_annulus {R t : ℝ} (hR : 0 < R) {n : ℕ}
    (ht : t ∈ gaussianAnnulus R n) :
    Real.exp (-2 * t ^ 2 / R ^ 2) ≤ Real.exp (-(n : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hlo := (gaussianAnnulus_bounds hR ht).1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : (0 : ℝ) < R ^ 2 := sq_pos_of_pos hR
  apply (div_le_iff₀ hr).mpr
  have hsq := mul_self_le_mul_self (mul_nonneg hn hR.le) hlo
  rw [← sq, ← sq, sq_abs, mul_pow] at hsq
  by_cases hzero : n = 0
  · rw [hzero]
    norm_num only [Nat.cast_zero, zero_mul, neg_zero]
    nlinarith [sq_nonneg t]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hh : (n : ℝ) ≤ 2 * n ^ 2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hr.le
    nlinarith

theorem summable_gaussianAnnulus_majorant :
    Summable (fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := by
  have h₂ := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1)
  have h₁ := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h₀ := Real.summable_exp_neg_nat
  have hh := h₂.add ((h₁.mul_left 4).add (h₀.mul_left 4))
  convert hh using 1
  funext n
  simp only [neg_mul, one_mul, pow_one]
  ring

theorem gaussian_cumulative_polynomial_le {R N p : ℝ} (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (((n : ℝ) + 1) * R + N) * (1 + ((n : ℝ) + 1) * R) ^ p ≤
      (R + N) * R ^ p * ((n : ℝ) + 2) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlinear : ((n : ℝ) + 1) * R + N ≤ ((n : ℝ) + 2) * (R + N) := by
    nlinarith
  have hbase : 1 + ((n : ℝ) + 1) * R ≤ ((n : ℝ) + 2) * R := by nlinarith
  have hpower : (1 + ((n : ℝ) + 1) * R) ^ p ≤ ((n : ℝ) + 2) * R ^ p := by
    calc
      _ ≤ (((n : ℝ) + 2) * R) ^ p := Real.rpow_le_rpow (by positivity) hbase hp
      _ = ((n : ℝ) + 2) ^ p * R ^ p := Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((n : ℝ) + 2) * R ^ p := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n + 2) hp1
  calc
    _ ≤ (((n : ℝ) + 2) * (R + N)) * (((n : ℝ) + 2) * R ^ p) :=
      mul_le_mul hlinear hpower (by positivity) (by positivity)
    _ = _ := by ring

theorem integral_gaussianAnnulus_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgnonneg : ∀ t, 0 ≤ g t) {K R N p : ℝ} (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, g t) ≤ K * (U + N) * (1 + U) ^ p) (n : ℕ) :
    (∫ t in gaussianAnnulus R n, Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ≤
      (K * (R + N) * R ^ p) *
        (Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := by
  have hR0 : 0 < R := by linarith
  let U : ℝ := ((n : ℝ) + 1) * R
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hsub : gaussianAnnulus R n ⊆ Icc (-U) U := gaussianAnnulus_subset hR0 n
  have hgi : IntegrableOn g (Icc (-U) U) := hg.continuousOn.integrableOn_compact isCompact_Icc
  have hwi : IntegrableOn (fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t)
      (gaussianAnnulus R n) := by
    have hc : Continuous (fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  have hmass : (∫ t in gaussianAnnulus R n, g t) ≤ ∫ t in Icc (-U) U, g t := by
    exact setIntegral_mono_set hgi (Filter.Eventually.of_forall hgnonneg) hsub.eventuallySubset
  calc
    _ ≤ ∫ t in gaussianAnnulus R n, Real.exp (-(n : ℝ)) * g t := by
      apply setIntegral_mono_on hwi ((hgi.mono_set hsub).const_mul _)
        (measurableSet_gaussianAnnulus R n)
      intro t ht
      exact mul_le_mul_of_nonneg_right (gaussian_weight_le_on_annulus hR0 ht) (hgnonneg t)
    _ = Real.exp (-(n : ℝ)) * ∫ t in gaussianAnnulus R n, g t := integral_const_mul _ _
    _ ≤ Real.exp (-(n : ℝ)) * (K * (U + N) * (1 + U) ^ p) := by
      gcongr
      exact hmass.trans (hcum U hU)
    _ ≤ Real.exp (-(n : ℝ)) *
        (K * ((R + N) * R ^ p * ((n : ℝ) + 2) ^ 2)) := by
      have hh := mul_le_mul_of_nonneg_left
        (gaussian_cumulative_polynomial_le hR hN hp hp1 n) hK
      simpa only [U, mul_assoc] using
        mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-(n : ℝ)))
    _ = _ := by ring

def gaussianCumulativeConstant : ℝ :=
  1 + ∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2

theorem gaussianCumulativeConstant_pos : 0 < gaussianCumulativeConstant := by
  unfold gaussianCumulativeConstant
  have hh : 0 ≤ ∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2 :=
    tsum_nonneg (fun _ => by positivity)
  linarith

/-- One absolute constant works for every cumulative exponent between zero and one. -/
theorem gaussian_integral_of_cumulative {g : ℝ → ℝ} (hg : Continuous g)
    (hgnonneg : ∀ t, 0 ≤ g t) {K R N p : ℝ} (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hcum : ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc (-U) U, g t) ≤ K * (U + N) * (1 + U) ^ p) :
    Integrable (fun t : ℝ => Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ∧
      (∫ t : ℝ, Real.exp (-2 * t ^ 2 / R ^ 2) * g t) ≤
        gaussianCumulativeConstant * K * (R + N) * R ^ p := by
  let w : ℝ → ℝ := fun t => Real.exp (-2 * t ^ 2 / R ^ 2) * g t
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hwnonneg (t : ℝ) : 0 ≤ w t := mul_nonneg (Real.exp_nonneg _) (hgnonneg t)
  have hnorm : (fun t => ‖w t‖) = w :=
    funext (fun t => Real.norm_of_nonneg (hwnonneg t))
  have hi (n : ℕ) : IntegrableOn w (gaussianAnnulus R n) := by
    exact (hw.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (gaussianAnnulus_subset (by linarith : 0 < R) n)
  have hfactor : 0 ≤ K * (R + N) * R ^ p := by positivity
  have hmajorant := summable_gaussianAnnulus_majorant.mul_left (K * (R + N) * R ^ p)
  have hs : Summable (fun n : ℕ => ∫ t in gaussianAnnulus R n, w t) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg hwnonneg) _ hmajorant
    intro n
    exact integral_gaussianAnnulus_le hg hgnonneg hK hR hN hp hp1 hcum n
  have hiunion := integrableOn_iUnion_of_summable_integral_norm hi (by
    simpa only [hnorm] using hs)
  have higlobal : Integrable w := by
    simpa only [gaussianAnnulus_cover, integrableOn_univ] using hiunion
  refine ⟨higlobal, ?_⟩
  have heq : (∫ t : ℝ, w t) = ∑' n : ℕ, ∫ t in gaussianAnnulus R n, w t := by
    simpa only [gaussianAnnulus_cover, Measure.restrict_univ] using
      (integral_iUnion (measurableSet_gaussianAnnulus R) (gaussianAnnulus_disjoint R) hiunion)
  calc
    _ = _ := heq
    _ ≤ ∑' n : ℕ, (K * (R + N) * R ^ p) *
        (Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) :=
      Summable.tsum_le_tsum
        (integral_gaussianAnnulus_le hg hgnonneg hK hR hN hp hp1 hcum) hs hmajorant
    _ = (K * (R + N) * R ^ p) *
        (∑' n : ℕ, Real.exp (-(n : ℝ)) * ((n : ℝ) + 2) ^ 2) := tsum_mul_left
    _ ≤ (K * (R + N) * R ^ p) * gaussianCumulativeConstant := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      unfold gaussianCumulativeConstant
      linarith
    _ = _ := by ring

end Sidon
