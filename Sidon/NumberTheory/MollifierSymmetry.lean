module

public import Sidon.NumberTheory.MollifierRightEndpoint
public import Sidon.NumberTheory.MollifierEndpoint

@[expose] public section

/-! # Conjugation and symmetric cumulative mean squares -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Sidon

theorem dirichletMollifier_conj (N : ℕ) (s : ℂ) :
    dirichletMollifier N (conj s) = conj (dirichletMollifier N s) := by
  simp only [dirichletMollifier, map_sum, map_mul, map_intCast,
    ← Complex.exp_conj, map_neg, Complex.conj_ofReal]

theorem mollifierError_conj (N : ℕ) (s : ℂ) :
    mollifierError N (conj s) = conj (mollifierError N s) := by
  simp only [mollifierError, riemannZeta_conj, dirichletMollifier_conj,
    map_sub, map_mul, map_one]

theorem norm_mollifierError_vertical_neg (N : ℕ) (σ t : ℝ) :
    ‖mollifierError N ((σ : ℂ) + (-t : ℝ) * Complex.I)‖ =
      ‖mollifierError N ((σ : ℂ) + t * Complex.I)‖ := by
  have heq : (σ : ℂ) + (-t : ℝ) * Complex.I =
      conj ((σ : ℂ) + t * Complex.I) := by simp
  rw [heq, mollifierError_conj, Complex.norm_conj]

theorem continuous_mollifierError_vertical (N : ℕ) {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => mollifierError N ((σ : ℂ) + t * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (analyticAt_mollifierError N ?_).continuousAt.comp (by fun_prop)
  intro heq
  have hh := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.one_re] at hh
  exact hσ hh

theorem integral_neg_pos_eq_two_of_even {f : ℝ → ℝ} (hf : Continuous f)
    (heven : ∀ t, f (-t) = f t) (T : ℝ) :
    (∫ t in -T..T, f t) = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hneg : (∫ t in -T..(0 : ℝ), f t) = ∫ t in (0 : ℝ)..T, f t := by
    have hh := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := T)
    simpa only [heven, neg_zero] using hh.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-T) 0)
    (hf.intervalIntegrable 0 T), hneg]
  ring

theorem integral_mollifierError_right_symmetric_le {N : ℕ} (hN : 1 ≤ N)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) :
    (∫ t in Set.Icc (-T) T,
      ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) ≤
      4096 * (T / (N : ℝ) + 1) / δ ^ 8 := by
  have hc := (continuous_mollifierError_vertical N (σ := 1 + δ) (by linarith)).norm.pow 2
  have heven : ∀ t : ℝ,
      ‖mollifierError N ((1 + δ : ℝ) + (-t : ℝ) * Complex.I)‖ ^ 2 =
        ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2 := by
    intro t
    rw [norm_mollifierError_vertical_neg]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -T ≤ T by linarith),
    integral_neg_pos_eq_two_of_even (f := fun t =>
      ‖mollifierError N ((1 + δ : ℝ) + t * Complex.I)‖ ^ 2) hc heven]
  have hh := integral_mollifierError_right_norm_sq_le_simple hN hδ hδ1 hT
  calc
    _ ≤ 2 * (2048 * (T / (N : ℝ) + 1) / δ ^ 8) := by gcongr
    _ = _ := by ring

end Sidon
