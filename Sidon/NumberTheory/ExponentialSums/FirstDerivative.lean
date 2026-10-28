module

public import Sidon.Equidistribution.Progressions
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # A quadratic-gap first derivative estimate for exponential sums -/

noncomputable section

open scoped BigOperators FourierTransform

namespace Sidon.ExponentialSums

theorem sum_mul_sub_next (a z : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), a k * (z (k + 1) - z k)) =
      a n * z (n + 1) - a 0 * z 0 -
        ∑ k ∈ Finset.range n, (a (k + 1) - a k) * z (k + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

theorem norm_inv_sub_inv_le {p q : ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hp : γ ≤ ‖p‖) (hq : γ ≤ ‖q‖) :
    ‖p⁻¹ - q⁻¹‖ ≤ ‖p - q‖ / γ ^ 2 := by
  have hp0 : p ≠ 0 := norm_pos_iff.mp (hγ.trans_le hp)
  have hq0 : q ≠ 0 := norm_pos_iff.mp (hγ.trans_le hq)
  rw [inv_sub_inv hp0 hq0, norm_div, norm_mul, norm_sub_rev]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hγ)
  nlinarith [mul_le_mul hp hq hγ.le (norm_nonneg p)]

theorem norm_sum_le_of_quotient_variation (z q : ℕ → ℂ) (n : ℕ)
    (hz : ∀ k, ‖z k‖ = 1) (hstep : ∀ k, z (k + 1) = q k * z k)
    {γ V : ℝ} (hγ : 0 < γ) (hgap : ∀ k ≤ n, γ ≤ ‖q k - 1‖)
    (hvariation : (∑ k ∈ Finset.range n, ‖q (k + 1) - q k‖) ≤ V) :
    ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ 2 / γ + V / γ ^ 2 := by
  let a : ℕ → ℂ := fun k => (q k - 1)⁻¹
  have ha (k : ℕ) (hk : k ≤ n) : ‖a k‖ ≤ 1 / γ := by
    dsimp [a]
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hγ (hgap k hk)
  have hsum : (∑ k ∈ Finset.range (n + 1), z k) =
      a n * z (n + 1) - a 0 * z 0 -
        ∑ k ∈ Finset.range n, (a (k + 1) - a k) * z (k + 1) := by
    rw [← sum_mul_sub_next]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hne : q k - 1 ≠ 0 := norm_pos_iff.mp (hγ.trans_le (hgap k hk'))
    rw [hstep k]
    dsimp [a]
    rw [show q k * z k - z k = (q k - 1) * z k by ring,
      ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hvar : (∑ k ∈ Finset.range n, ‖a (k + 1) - a k‖) ≤ V / γ ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖q (k + 1) - q k‖ / γ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        have hh := norm_inv_sub_inv_le hγ (hgap (k + 1) (by omega))
          (hgap k (by omega))
        simpa only [a, sub_sub_sub_cancel_right] using hh
      _ = (∑ k ∈ Finset.range n, ‖q (k + 1) - q k‖) / γ ^ 2 :=
        (Finset.sum_div _ _ _).symm
      _ ≤ V / γ ^ 2 := div_le_div_of_nonneg_right hvariation (sq_nonneg _)
  rw [hsum]
  calc
    _ ≤ ‖a n * z (n + 1)‖ + ‖a 0 * z 0‖ +
        ‖∑ k ∈ Finset.range n, (a (k + 1) - a k) * z (k + 1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖a n‖ + ‖a 0‖ + ∑ k ∈ Finset.range n, ‖a (k + 1) - a k‖ := by
      simp only [norm_mul, hz, mul_one]
      gcongr
      simpa only [norm_mul, hz, mul_one] using
        (norm_sum_le (Finset.range n) (fun k => (a (k + 1) - a k) * z (k + 1)))
    _ ≤ 1 / γ + 1 / γ + V / γ ^ 2 :=
      add_le_add (add_le_add (ha n le_rfl) (ha 0 (Nat.zero_le n))) hvar
    _ = _ := by ring

theorem norm_fourierChar_sub_le (x y : ℝ) :
    ‖(𝐞 x : ℂ) - 𝐞 y‖ ≤ 2 * Real.pi * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun t : ℝ => (𝐞 t : ℂ))
    (fun t _ => (Real.hasDerivAt_fourierChar t).hasDerivWithinAt)
    (C := 2 * Real.pi) (fun t _ => by
      simp [Complex.norm_real, Real.norm_eq_abs])
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem fourierChar_eq_circle (x : ℝ) :
    (𝐞 x : ℂ) = fourier 1 (x : AddCircle (1 : ℝ)) := by
  rw [Real.fourierChar_apply, fourier_coe_apply]
  push_cast
  ring_nf

theorem four_mul_le_norm_fourierChar_sub_one {η x : ℝ}
    (hη : 0 ≤ η) (hxlo : η ≤ x) (hxhi : x ≤ 1 - η) :
    4 * η ≤ ‖(𝐞 x : ℂ) - 1‖ := by
  rw [fourierChar_eq_circle]
  by_cases hx : x ≤ 1 / 2
  · have hx0 : 0 ≤ x := hη.trans hxlo
    have hh := four_mul_abs_le_norm_fourier_one_sub_one x (by
      rw [abs_of_nonneg hx0]
      exact hx)
    rw [abs_of_nonneg hx0] at hh
    linarith
  · have hhalf : |x - 1| ≤ (1 : ℝ) / 2 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hcoe : ((x - 1 : ℝ) : AddCircle (1 : ℝ)) = x := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    have hh := four_mul_abs_le_norm_fourier_one_sub_one (x - 1) hhalf
    rw [hcoe, abs_of_nonpos (by linarith : x - 1 ≤ 0)] at hh
    linarith

theorem norm_sum_fourierChar_le_of_monotone_increments (φ : ℕ → ℝ) (n : ℕ)
    {γ : ℝ} (hγ : 0 < γ)
    (hmono : ∀ k < n, φ (k + 1) - φ k ≤ φ (k + 1 + 1) - φ (k + 1))
    (hlo : 0 ≤ φ 1 - φ 0) (hhi : φ (n + 1) - φ n ≤ 1)
    (hgap : ∀ k ≤ n, γ ≤ ‖(𝐞 (φ (k + 1) - φ k) : ℂ) - 1‖) :
    ‖∑ k ∈ Finset.range (n + 1), (𝐞 (φ k) : ℂ)‖ ≤
      2 / γ + 2 * Real.pi / γ ^ 2 := by
  let δ : ℕ → ℝ := fun k => φ (k + 1) - φ k
  let z : ℕ → ℂ := fun k => 𝐞 (φ k)
  let q : ℕ → ℂ := fun k => 𝐞 (δ k)
  have hstep (k : ℕ) : z (k + 1) = q k * z k := by
    dsimp [z, q, δ]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, sub_add_cancel]
  apply norm_sum_le_of_quotient_variation z q n (by intro k; simp [z]) hstep hγ hgap
  calc
    (∑ k ∈ Finset.range n, ‖q (k + 1) - q k‖) ≤
        ∑ k ∈ Finset.range n, 2 * Real.pi * (δ (k + 1) - δ k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      have hm : δ k ≤ δ (k + 1) := hmono k hk'
      simpa only [q, abs_of_nonneg (sub_nonneg.mpr hm)] using
        norm_fourierChar_sub_le (δ (k + 1)) (δ k)
    _ = 2 * Real.pi * (δ n - δ 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ 2 * Real.pi := by
      have hh : δ n - δ 0 ≤ 1 := by simpa only [δ] using sub_le_self _ hlo |>.trans hhi
      nlinarith [Real.pi_pos]

theorem norm_sum_fourierChar_le_quadratic_gap (φ : ℕ → ℝ) (n : ℕ)
    {η : ℝ} (hη : 0 < η)
    (hmono : ∀ k < n, φ (k + 1) - φ k ≤ φ (k + 1 + 1) - φ (k + 1))
    (hlo : ∀ k ≤ n, η ≤ φ (k + 1) - φ k)
    (hhi : ∀ k ≤ n, φ (k + 1) - φ k ≤ 1 - η) :
    ‖∑ k ∈ Finset.range (n + 1), (𝐞 (φ k) : ℂ)‖ ≤
      2 / (4 * η) + 2 * Real.pi / (4 * η) ^ 2 := by
  apply norm_sum_fourierChar_le_of_monotone_increments φ n (by positivity) hmono
    (hη.le.trans (hlo 0 (Nat.zero_le n))) ((hhi n le_rfl).trans (by linarith))
  intro k hk
  exact four_mul_le_norm_fourierChar_sub_one hη.le (hlo k hk) (hhi k hk)

end Sidon.ExponentialSums
