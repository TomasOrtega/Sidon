/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Sidon.NumberTheory.RiemannGaussian.FiniteDiscreteSobolev

namespace RiemannGaussian.FiniteShiftCorrelation
noncomputable section
open Complex Filter Topology
open scoped Classical

def correlation (f : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑' n : ℤ, f (n + h) * starRingEnd ℂ (f n)

def shiftedSum (f : ℤ → ℂ) (H : ℕ) (n : ℤ) : ℂ :=
  ∑ h ∈ Finset.range H, f (n + h)

private theorem finite_shift {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h)) :=
  hf.fun_comp_of_injective (Equiv.addRight h).injective

private theorem finite_pair {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h k : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h) * starRingEnd ℂ (f (n + k))) :=
  (finite_shift hf h).fun_mul_left _

theorem summable_correlation {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Summable (fun n : ℤ ↦ f (n + h) * starRingEnd ℂ (f n)) :=
  summable_of_hasFiniteSupport ((finite_shift hf h).fun_mul_left _)

theorem correlation_re {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    (correlation f h).re = ∑' n : ℤ, (f (n + h) * starRingEnd ℂ (f n)).re :=
  Complex.re_tsum (summable_correlation hf h)

theorem correlation_zero {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) :
    (correlation f 0).re = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  rw [correlation_re hf]
  simp only [add_zero, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem mixed_shift_eq (f : ℤ → ℂ) (h k : ℤ) :
    (∑' n : ℤ, f (n + h) * starRingEnd ℂ (f (n + k))) = correlation f (h - k) := by
  calc
    _ = ∑' n : ℤ, f ((n + k) + (h - k)) * starRingEnd ℂ (f (n + k)) := by
      apply tsum_congr
      intro n
      congr 2
      ring
    _ = _ := (Equiv.addRight k).tsum_eq
      (fun n : ℤ ↦ f (n + (h - k)) * starRingEnd ℂ (f n))

theorem correlation_neg (f : ℤ → ℂ) (h : ℤ) :
    correlation f (-h) = starRingEnd ℂ (correlation f h) := by
  simp only [correlation, Complex.conj_tsum]
  calc
    _ = ∑' n : ℤ, f n * starRingEnd ℂ (f (n + h)) := by
      simpa only [zero_sub, add_zero, correlation] using (mixed_shift_eq f 0 h).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [map_mul, starRingEnd_self_apply, mul_comm]

theorem correlation_neg_re (f : ℤ → ℂ) (h : ℤ) :
    (correlation f (-h)).re = (correlation f h).re := by
  rw [correlation_neg, Complex.conj_re]

theorem shiftedSum_mass {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, shiftedSum f H n) = (H : ℂ) * ∑' n : ℤ, f n := by
  unfold shiftedSum
  rw [Summable.tsum_finsetSum (s := Finset.range H)
    (fun (h : ℕ) _ ↦ summable_of_hasFiniteSupport (finite_shift hf (h : ℤ)))]
  have hshift (h : ℕ) : (∑' n : ℤ, f (n + h)) = ∑' n : ℤ, f n :=
    (Equiv.addRight (h : ℤ)).tsum_eq f
  simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem norm_sq_shiftedSum_eq (f : ℤ → ℂ) (H : ℕ) (n : ℤ) :
    ‖shiftedSum f H n‖ ^ 2 = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
      (f (n + h) * starRingEnd ℂ (f (n + k))).re := by
  calc
    _ = (shiftedSum f H n * starRingEnd ℂ (shiftedSum f H n)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    _ = _ := by
      simp only [shiftedSum, map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Complex.re_sum]

theorem shiftedSum_energy {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hp (h k : ℕ) : Function.HasFiniteSupport
      (fun n : ℤ ↦ (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    (finite_pair hf h k).fun_comp (by simp)
  have hi (h : ℕ) : Summable
      (fun n : ℤ ↦ ∑ k ∈ Finset.range H, (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.sum (hp h) (Finset.range H))
  simp_rw [norm_sq_shiftedSum_eq]
  rw [Summable.tsum_finsetSum (fun h _ ↦ hi h)]
  apply Finset.sum_congr rfl
  intro h _
  rw [Summable.tsum_finsetSum (fun k _ ↦ summable_of_hasFiniteSupport (hp h k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.re_tsum (summable_of_hasFiniteSupport (finite_pair hf h k)), mixed_shift_eq]

theorem shiftedSum_eq_zero_outside {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    ∀ n ∉ Finset.Ico (a - H + 1) (a + N), shiftedSum f H n = 0 := by
  intro n hn
  apply Finset.sum_eq_zero
  intro h hh
  apply hf
  intro hm
  apply hn
  simp only [Finset.mem_Ico] at hm ⊢
  have hh' := Finset.mem_range.mp hh
  omega

theorem norm_sum_sq_le_correlation_matrix {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hH : 0 < H) (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) *
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hfinite : Function.HasFiniteSupport f :=
    (Finset.Ico a (a + N)).finite_toSet.subset (by
      intro n hn
      by_contra h
      exact hn (hf n h))
  let S := Finset.Ico (a - H + 1) (a + N)
  have hs := shiftedSum_eq_zero_outside (H := H) hf
  have hmass : (∑ n ∈ S, shiftedSum f H n) =
      (H : ℂ) * ∑ n ∈ Finset.Ico a (a + N), f n := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ) hs,
      shiftedSum_mass hfinite, tsum_eq_sum hf]
  have henergy : (∑ n ∈ S, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (fun n hn ↦ by rw [hs n hn, norm_zero, zero_pow (by decide)])]
    exact shiftedSum_energy hfinite H
  have hcard : (S.card : ℝ) = (N : ℝ) + H - 1 := by
    have h := Int.card_Ico_of_le (a := a - H + 1) (b := a + N) (by omega)
    have hc : (S.card : ℤ) = (N : ℤ) + H - 1 := by dsimp [S]; linarith
    exact_mod_cast hc
  have h := norm_sum_sq_le_card_mul_sum_norm_sq S (shiftedSum f H)
  rw [hmass, henergy, hcard, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end
end RiemannGaussian.FiniteShiftCorrelation
