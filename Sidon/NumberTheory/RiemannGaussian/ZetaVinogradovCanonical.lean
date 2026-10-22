/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Sidon.NumberTheory.RiemannGaussian.VinogradovNearOneBudget
import Sidon.NumberTheory.RiemannGaussian.VinogradovScaleSelection
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneCanonical
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneJensen
import Sidon.NumberTheory.RiemannGaussian.ZetaNearOneLocalDisc
import Sidon.NumberTheory.RiemannGaussian.ZetaVinogradovLocalDisc

namespace RiemannGaussian.ZetaVinogradovCanonical
noncomputable section
open Complex Metric Set MeromorphicOn
open RiemannGaussian.VinogradovNearOneBudget RiemannGaussian.VinogradovScaleSelection RiemannGaussian.ZetaVinogradovLocalDisc
open RiemannGaussian.ZetaNearOneLocalDisc (center)
open RiemannGaussian.ZetaNearOneJensen (center_ne_zero center_log_bound)
open RiemannGaussian.ZetaNearOneCanonical (translated translated_zero)
open RiemannGaussian.AnalyticDiscCanonicalBounds RiemannGaussian.AnalyticDiscSignedDerivative
def allowance (n : ℕ) (x t : ℝ) : ℝ := profile n t + Real.log (1 + 1 / x)

theorem logDeriv_translated (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    logDeriv (translated x t) 0 = logDeriv riemannZeta (center x t) := by
  have hd := (analyticOnNhd_disc n hn ht hx hx' _
    (mem_closedBall_self (div_nonneg (delta_pos n).le (by norm_num)))).differentiableAt
  change logDeriv (riemannZeta ∘ (· + center x t)) 0 = _
  rw [logDeriv_comp (by simpa using hd) (by fun_prop)]
  simp

end
end RiemannGaussian.ZetaVinogradovCanonical
