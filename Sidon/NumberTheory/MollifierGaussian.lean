import Sidon.NumberTheory.MollifierSymmetry
import Sidon.NumberTheory.VerticalL2Interpolation
import Sidon.NumberTheory.RiemannGaussian.ZetaGaussianLocalizer
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # An analytic Gaussian carrier across the zeta pole -/

noncomputable section

open MeasureTheory
open Complex.HadamardThreeLines

namespace Sidon

def poleRemovedMollifierError (N : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta₁ s * dirichletMollifier N s - (s - 1)) / (s + 1)

def gaussianMollifier (N : ℕ) (R : ℝ) (s : ℂ) : ℂ :=
  poleRemovedMollifierError N s * Complex.exp ((s / (R : ℂ)) ^ 2)

theorem poleRemovedMollifierError_eq {N : ℕ} {s : ℂ} (hs : s ≠ 1) :
    poleRemovedMollifierError N s = (s - 1) / (s + 1) * mollifierError N s := by
  rw [poleRemovedMollifierError, RiemannGaussian.riemannZeta₁_eq_sub_one_mul hs,
    mollifierError]
  ring

theorem norm_poleRemovedMollifierError_le {N : ℕ} {s : ℂ} (hs : 0 ≤ s.re)
    (hs1 : s ≠ 1) : ‖poleRemovedMollifierError N s‖ ≤ ‖mollifierError N s‖ := by
  rw [poleRemovedMollifierError_eq hs1, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (RiemannGaussian.ZetaGaussianLocalizer.norm_ratio_le_one hs)

theorem analyticAt_gaussianMollifier (N : ℕ) (R : ℝ) {s : ℂ} (hs : s + 1 ≠ 0) :
    AnalyticAt ℂ (gaussianMollifier N R) s := by
  have hM : AnalyticAt ℂ (dirichletMollifier N) s := by
    unfold dirichletMollifier
    fun_prop
  unfold gaussianMollifier poleRemovedMollifierError
  exact ((((differentiable_riemannZeta₁.analyticAt s).mul hM).sub
    (analyticAt_id.sub analyticAt_const)).div (analyticAt_id.add analyticAt_const) hs).mul
      (by fun_prop)

theorem norm_gaussianMollifier (N : ℕ) {R : ℝ} (hR : R ≠ 0) (s : ℂ) :
    ‖gaussianMollifier N R s‖ = ‖poleRemovedMollifierError N s‖ *
      Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2) := by
  rw [gaussianMollifier, norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

theorem norm_dirichletMollifier_le {N : ℕ} {s : ℂ} (hs : 0 ≤ s.re) :
    ‖dirichletMollifier N s‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖(ArithmeticFunction.moebius n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [norm_mul]
      apply mul_le_one₀ _ (norm_nonneg _) _
      · rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      · rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hs (Real.log_nonneg hn1))
    _ = _ := by simp

theorem norm_poleRemovedMollifierError_le_polynomial {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖poleRemovedMollifierError N s‖ ≤ 8 * (N : ℝ) * (|s.im| + 22) ^ 2 + 1 := by
  have heq : poleRemovedMollifierError N s =
      RiemannGaussian.ZetaGaussianLocalizer.regularized s * dirichletMollifier N s -
        (s - 1) / (s + 1) := by
    unfold poleRemovedMollifierError RiemannGaussian.ZetaGaussianLocalizer.regularized
    ring
  rw [heq]
  calc
    _ ≤ ‖RiemannGaussian.ZetaGaussianLocalizer.regularized s * dirichletMollifier N s‖ +
        ‖(s - 1) / (s + 1)‖ := norm_sub_le _ _
    _ ≤ (8 * (|s.im| + 22) ^ 2) * (N : ℝ) + 1 := by
      rw [norm_mul]
      gcongr
      · exact RiemannGaussian.ZetaGaussianLocalizer.norm_regularized_le hs hs'
      · exact norm_dirichletMollifier_le (by linarith)
      · exact RiemannGaussian.ZetaGaussianLocalizer.norm_ratio_le_one (by linarith)
    _ = _ := by ring

theorem norm_poleRemovedMollifierError_le_quadratic {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖poleRemovedMollifierError N s‖ ≤ (8000 * (N : ℝ) + 1) * (1 + s.im ^ 2) := by
  apply (norm_poleRemovedMollifierError_le_polynomial hs hs').trans
  have hsq : (|s.im| + 22) ^ 2 ≤ 1000 * (1 + s.im ^ 2) := by
    nlinarith [sq_nonneg (|s.im| - 22), sq_abs s.im]
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (N : ℝ) by positivity)
  nlinarith [sq_nonneg s.im]

theorem quadratic_mul_gaussian_le {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (1 + t ^ 2) * Real.exp (-b * t ^ 2) ≤ 1 + 1 / b := by
  have hx : b * t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right
      (show b * t ^ 2 ≤ Real.exp (b * t ^ 2) by linarith [Real.add_one_le_exp (b * t ^ 2)])
      (Real.exp_nonneg (-b * t ^ 2))
    simpa only [← Real.exp_add, add_neg_cancel_left, Real.exp_zero, mul_neg,
      neg_mul, add_neg_cancel] using hh
  have hterm : t ^ 2 * Real.exp (-b * t ^ 2) ≤ 1 / b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have he : Real.exp (-b * t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  nlinarith

def gaussianMollifierEnvelope (N : ℕ) (R : ℝ) : ℝ :=
  (8000 * (N : ℝ) + 1) * Real.exp 3 * (1 + 2 * R ^ 2)

theorem norm_gaussianMollifier_le_decay {N : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖gaussianMollifier N R s‖ ≤
      gaussianMollifierEnvelope N R * Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hu : s.re ^ 2 / R ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  have hquad := quadratic_mul_gaussian_le (b := 1 / (2 * R ^ 2)) (by positivity) s.im
  have hq : (1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2)) ≤ 1 + 2 * R ^ 2 := by
    have he : -(1 / (2 * R ^ 2)) * s.im ^ 2 = -s.im ^ 2 / (2 * R ^ 2) := by ring
    have he' : 1 / (1 / (2 * R ^ 2)) = 2 * R ^ 2 := by simp
    rw [he, he'] at hquad
    exact hquad
  rw [norm_gaussianMollifier N hR0.ne']
  calc
    _ ≤ ((8000 * (N : ℝ) + 1) * (1 + s.im ^ 2)) *
        Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2) := by
      gcongr
      exact norm_poleRemovedMollifierError_le_quadratic hs hs'
    _ = (8000 * (N : ℝ) + 1) * Real.exp (s.re ^ 2 / R ^ 2) *
        ((1 + s.im ^ 2) * Real.exp (-s.im ^ 2 / (2 * R ^ 2))) *
          Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by
      have he : (s.re ^ 2 - s.im ^ 2) / R ^ 2 = s.re ^ 2 / R ^ 2 +
          (-s.im ^ 2 / (2 * R ^ 2)) + (-s.im ^ 2 / (2 * R ^ 2)) := by ring
      rw [he, Real.exp_add, Real.exp_add]
      ring
    _ ≤ (8000 * (N : ℝ) + 1) * Real.exp 3 * (1 + 2 * R ^ 2) *
        Real.exp (-s.im ^ 2 / (2 * R ^ 2)) := by gcongr
    _ = _ := rfl

theorem analyticOnNhd_gaussianMollifier (N : ℕ) (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    AnalyticOnNhd ℂ (gaussianMollifier N R) (verticalClosedStrip a b) := by
  intro s hs
  apply analyticAt_gaussianMollifier N R
  exact RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero (ha.trans hs.1)

theorem bddAbove_gaussianMollifier (N : ℕ) {R : ℝ} (hR : 1 ≤ R)
    {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : b ≤ 3 / 2) :
    BddAbove ((norm ∘ gaussianMollifier N R) '' verticalClosedStrip a b) := by
  refine ⟨gaussianMollifierEnvelope N R, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hh := norm_gaussianMollifier_le_decay (N := N) hR (ha.trans hs.1) (hs.2.trans hb)
  have he : Real.exp (-s.im ^ 2 / (2 * R ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  exact hh.trans (mul_le_of_le_one_right (by unfold gaussianMollifierEnvelope; positivity) he)

theorem integrable_gaussianMollifier_norm_sq (N : ℕ) {R σ : ℝ} (hR : 1 ≤ R)
    (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
  have hR0 : 0 < R := by linarith
  have hc : Continuous (fun t : ℝ => gaussianMollifier N R ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (analyticAt_gaussianMollifier N R ?_).continuousAt.comp (by fun_prop)
    apply RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero
    simpa using (show 0 ≤ σ by linarith)
  have hi := (integrable_exp_neg_mul_sq (b := 1 / R ^ 2) (by positivity)).const_mul
    (gaussianMollifierEnvelope N R ^ 2)
  have hc2 : Continuous (fun t : ℝ => ‖gaussianMollifier N R ((σ : ℂ) + t * Complex.I)‖ ^ 2) := by
    fun_prop
  apply hi.mono' hc2.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := norm_gaussianMollifier_le_decay (N := N) hR
    (s := (σ : ℂ) + t * Complex.I) (by simpa using hσ) (by simpa using hσ')
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, ← Real.exp_nat_mul, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one,
    zero_mul, add_zero, zero_add] at hsquare
  convert hsquare using 1 <;> congr 1 <;> ring

theorem mollifierError_sq_le_poleRemoved_sq {N : ℕ} {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) (ht : 1 ≤ |s.im|) :
    ‖mollifierError N s‖ ^ 2 ≤ 8 * ‖poleRemovedMollifierError N s‖ ^ 2 := by
  have hs1 : s ≠ 1 := by
    intro heq
    have hh := congrArg Complex.im heq
    simp only [Complex.one_im] at hh
    rw [hh] at ht
    norm_num at ht
  have hdenpos : 0 < ‖s + 1‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (RiemannGaussian.ZetaGaussianLocalizer.add_one_ne_zero (by linarith))
  have hden : ‖s + 1‖ ^ 2 ≤ 8 * ‖s - 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, add_zero, sub_zero]
    have ht2 : 1 ≤ s.im ^ 2 := by nlinarith [sq_abs s.im]
    nlinarith [sq_nonneg (s.re - 1)]
  rw [poleRemovedMollifierError_eq hs1, norm_mul, norm_div, mul_pow, div_pow]
  calc
    _ ≤ 8 * (‖s - 1‖ ^ 2 * ‖mollifierError N s‖ ^ 2) / ‖s + 1‖ ^ 2 := by
      apply (le_div_iff₀ hdenpos).mpr
      nlinarith [mul_le_mul_of_nonneg_right hden (sq_nonneg ‖mollifierError N s‖)]
    _ = _ := by ring

theorem mollifierError_sq_le_gaussianMollifier_sq {N : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (ht : 1 ≤ |s.im|) (htR : |s.im| ≤ R) :
    ‖mollifierError N s‖ ^ 2 ≤ 8 * Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2 := by
  have hR0 : 0 < R := by linarith
  have ht2 : s.im ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs s.im]
  have hexp : 1 ≤ Real.exp (2 + 2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) := by
    apply Real.one_le_exp_iff.mpr
    have hh : -1 ≤ (s.re ^ 2 - s.im ^ 2) / R ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hR0)).mpr
      nlinarith [sq_nonneg s.re]
    linarith
  have hpole : ‖poleRemovedMollifierError N s‖ ^ 2 ≤
      Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2 := by
    rw [norm_gaussianMollifier N hR0.ne', mul_pow]
    have heq : (Real.exp ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) ^ 2 =
        Real.exp (2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) := by
      simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul ((s.re ^ 2 - s.im ^ 2) / R ^ 2) 2).symm
    rw [heq]
    calc
      _ ≤ ‖poleRemovedMollifierError N s‖ ^ 2 *
          Real.exp (2 + 2 * ((s.re ^ 2 - s.im ^ 2) / R ^ 2)) :=
        le_mul_of_one_le_right (sq_nonneg _) hexp
      _ = _ := by rw [Real.exp_add]; ring
  calc
    _ ≤ 8 * ‖poleRemovedMollifierError N s‖ ^ 2 :=
      mollifierError_sq_le_poleRemoved_sq hs hs' ht
    _ ≤ 8 * (Real.exp 2 * ‖gaussianMollifier N R s‖ ^ 2) := by gcongr
    _ = _ := by ring

end Sidon
