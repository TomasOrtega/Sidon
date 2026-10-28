module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Tactic

@[expose] public section

/-! # Probability weights from signed Fourier interpolation -/

noncomputable section

open scoped BigOperators

namespace Sidon.BandwidthCounterexample

variable {ι : Type*} [Fintype ι]

theorem exists_probability_weights_of_signed_moments (M : ℕ)
    (t : ι → AddCircle (1 : ℝ)) (b : ι → ℝ)
    (hmom : ∀ n : ℤ, |n| ≤ M → (∑ i, (b i : ℂ) * fourier n (t i)) = 1) :
    ∃ w : Option ι → ℝ, ∃ v : ι → ℝ,
      (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ 0 < w none ∧
      ∀ n : ℤ, |n| ≤ M →
        (∑ x, (w x : ℂ) * fourier n (Option.elim' 0 t x)) =
          ∑ i, (v i : ℂ) * fourier n (t i) := by
  classical
  let neg : ι → ℝ := fun i => max (-b i) 0
  let pos : ι → ℝ := fun i => b i + neg i
  have hneg (i : ι) : 0 ≤ neg i := le_max_right _ _
  have hpos (i : ι) : 0 ≤ pos i := by
    have h := le_max_left (-b i) 0
    dsimp [pos, neg]
    linarith
  have hsum : ∑ i, b i = 1 := by
    apply Complex.ofReal_injective
    simpa only [fourier_zero, ContinuousMap.one_apply, mul_one, Complex.ofReal_sum,
      Complex.ofReal_one] using hmom 0 (by simp)
  let Z : ℝ := 1 + ∑ i, neg i
  have hZ : 0 < Z := by
    have hnonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hneg i)
    dsimp [Z]
    linarith
  have hsumpos : ∑ i, pos i = Z := by
    simp only [pos, Finset.sum_add_distrib, hsum, Z]
  let w : Option ι → ℝ := Option.elim' (1 / Z) (fun i => neg i / Z)
  let v : ι → ℝ := fun i => pos i / Z
  refine ⟨w, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | none => exact (div_pos zero_lt_one hZ).le
    | some i => exact div_nonneg (hneg i) hZ.le
  · simp only [w, Fintype.sum_option, Option.elim'_none, Option.elim'_some,
      ← Finset.sum_div, ← add_div]
    exact div_self hZ.ne'
  · exact fun i => div_nonneg (hpos i) hZ.le
  · dsimp [v]
    rw [← Finset.sum_div, hsumpos, div_self hZ.ne']
  · exact div_pos zero_lt_one hZ
  · intro n hn
    have hkey : (∑ i, (pos i : ℂ) * fourier n (t i)) =
        1 + ∑ i, (neg i : ℂ) * fourier n (t i) := by
      simp only [pos, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, hmom n hn]
    simp only [w, v, Fintype.sum_option, Option.elim'_none, Option.elim'_some,
      fourier_eval_zero, mul_one, Complex.ofReal_div, Complex.ofReal_one]
    calc
      _ = (1 + ∑ i, (neg i : ℂ) * fourier n (t i)) / (Z : ℂ) := by
        rw [add_div, Finset.sum_div]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (pos i : ℂ) * fourier n (t i)) / (Z : ℂ) := by rw [hkey]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring

end Sidon.BandwidthCounterexample
