import Sidon.NumberTheory.LogSmoothing
import Sidon.NumberTheory.SmoothedMangoldt

/-! Compatibility of complex spectral smoothing with the actual arithmetic primitive. -/

noncomputable section

namespace Sidon

theorem fwdDiff_iter_ofReal (f : ℝ → ℝ) (n : ℕ) (h t : ℝ) :
    (fwdDiff h)^[n] (fun u => (f u : ℂ)) t = ((fwdDiff h)^[n] f t : ℝ) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (fwdDiff h)^[n] (fun u => (f u : ℂ)) (t + h) -
        (fwdDiff h)^[n] (fun u => (f u : ℂ)) t = _
      rw [ih, ih]
      exact (Complex.ofReal_sub _ _).symm

theorem logarithmicPrimitive_smoothedMangoldt (j : ℕ) (t : ℝ) :
    logarithmicPrimitive (fun u => (smoothedMangoldt 0 u : ℂ)) j t =
      (smoothedMangoldt j t : ℂ) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
      change (∫ u in (0 : ℝ)..t,
        logarithmicPrimitive (fun v => (smoothedMangoldt 0 v : ℂ)) j u) = _
      simp_rw [ih]
      rw [intervalIntegral.integral_ofReal, integral_smoothedMangoldt]

theorem spectralSmoothing_smoothedMangoldt (j : ℕ) (h t : ℝ) :
    spectralSmoothing j h (fun u => (smoothedMangoldt 0 u : ℂ)) t =
      ((fwdDiff h)^[j + 2] (smoothedMangoldt j) t : ℝ) := by
  have hp : logarithmicPrimitive (fun u => (smoothedMangoldt 0 u : ℂ)) j =
      fun u => (smoothedMangoldt j u : ℂ) :=
    funext (logarithmicPrimitive_smoothedMangoldt j)
  unfold spectralSmoothing
  rw [hp, fwdDiff_iter_ofReal]

end Sidon
