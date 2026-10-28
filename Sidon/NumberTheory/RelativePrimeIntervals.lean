module

public import Sidon.NumberTheory.PrimeNumberTheorem

@[expose] public section

/-! # Relative prime intervals

This input follows here from the proved prime number theorem.
-/

noncomputable section

namespace Sidon

open Filter Topology
open scoped Chebyshev

/-- Every sufficiently large relative interval contains a prime. -/
def RelativePrimeIntervals : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    ∃ p : ℕ, p.Prime ∧ (1 - ε) * x ≤ p ∧ (p : ℝ) ≤ x

theorem exists_prime_of_theta_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hθ : Chebyshev.theta a < Chebyshev.theta b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  classical
  by_contra hnone
  have hb : 0 ≤ b := ha.trans hab
  have hsets :
      (Finset.Icc 0 ⌊a⌋₊).filter Nat.Prime =
        (Finset.Icc 0 ⌊b⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp0, hpa⟩, hp⟩
      exact ⟨⟨hp0, hpa.trans (Nat.floor_mono hab)⟩, hp⟩
    · rintro ⟨⟨hp0, hpb⟩, hp⟩
      have hpbr : (p : ℝ) ≤ b :=
        (Nat.cast_le.mpr hpb).trans (Nat.floor_le hb)
      have hpar : (p : ℝ) ≤ a := by
        by_contra hpa
        exact hnone ⟨p, hp, lt_of_not_ge hpa, hpbr⟩
      exact ⟨⟨hp0, Nat.le_floor hpar⟩, hp⟩
  have heq : Chebyshev.theta a = Chebyshev.theta b := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, hsets]
  exact (ne_of_lt hθ) heq

theorem eventually_prime_in_relative_interval {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ (p : ℝ) ≤ x := by
  have hsmall := NumberTheory.theta_isEquivalent.isLittleO.bound
    (show 0 < ε / 4 by positivity)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hsmall
  obtain ⟨X, hX⟩ := eventually_atTop.mp hsmall
  have hfactor : 0 < 1 - ε := sub_pos.mpr hε1
  refine eventually_atTop.mpr ⟨max 1 (max X (X / (1 - ε))), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxdiv : X / (1 - ε) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have hax : X ≤ (1 - ε) * x := by
    simpa [mul_comm] using (div_le_iff₀ hfactor).mp hxdiv
  have hapos : 0 < (1 - ε) * x := mul_pos hfactor hxpos
  have hboundx := hX x hxX
  have hbounda := hX ((1 - ε) * x) hax
  rw [abs_of_pos hxpos] at hboundx
  rw [abs_of_pos hapos] at hbounda
  have hlow := (abs_le.mp hboundx).1
  have hhigh := (abs_le.mp hbounda).2
  have hεx : 0 < ε * x := mul_pos hε hxpos
  have hεsqx : 0 ≤ ε ^ 2 * x := mul_nonneg (sq_nonneg ε) hxpos.le
  have hθ : Chebyshev.theta ((1 - ε) * x) < Chebyshev.theta x := by
    nlinarith
  apply exists_prime_of_theta_lt hapos.le ?_ hθ
  nlinarith

theorem relativePrimeIntervals : RelativePrimeIntervals := by
  intro ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  filter_upwards [eventually_prime_in_relative_interval hδ hδ1,
    eventually_ge_atTop (0 : ℝ)] with x hx hx0
  obtain ⟨p, hp, hlow, hupp⟩ := hx
  refine ⟨p, hp, ?_, hupp⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hδε 1) hx0).trans hlow.le

end Sidon
