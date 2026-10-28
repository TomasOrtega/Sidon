module

public import Sidon.NumberTheory.RiemannGaussian.ZetaEulerLineBound
public import Sidon.NumberTheory.ZetaCriticalLine

@[expose] public section

/-! Critical-line Weyl bounds from the checked logarithmic derivative estimates. -/

noncomputable section

namespace Sidon

theorem riemannZeta_critical_line_weyl {s : ℂ} (hσ : s.re = 1 / 2)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ ((1 : ℝ) / 6) * Real.log |s.im| := by
  have hline : s.re = RiemannGaussian.DirichletPowerParameters.line 1 := by
    norm_num [RiemannGaussian.DirichletPowerParameters.line,
      RiemannGaussian.DerivativePowerExponents.alpha]
    exact hσ
  have h := RiemannGaussian.ZetaEulerLineBound.bound_abs 1 (by omega) hline ht
  have hα : RiemannGaussian.DerivativePowerExponents.alpha 1 = (1 : ℝ) / 6 := by
    norm_num [RiemannGaussian.DerivativePowerExponents.alpha]
  simpa only [hα] using h

theorem riemannZeta_critical_line_power {s : ℂ} (hσ : s.re = 1 / 2)
    (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 393216 * |s.im| ^ ((3 : ℝ) / 16) := by
  have hW := riemannZeta_critical_line_weyl hσ ht
  have hlog := sixth_rpow_mul_log_le_three_sixteenths
    (by linarith : (0 : ℝ) < |s.im|)
  nlinarith

theorem exists_riemannZeta_critical_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta (zetaCriticalPoint t)‖ ≤ C * (1 + |t|) ^ ((3 : ℝ) / 16) := by
  apply exists_riemannZeta_criticalPoint_growth_of_tail
    (C := 393216) (by norm_num : (0 : ℝ) ≤ 3 / 16)
  intro t ht
  simpa only [zetaCriticalPoint_im] using
    riemannZeta_critical_line_power (zetaCriticalPoint_re t) (by simpa using ht)

end Sidon
