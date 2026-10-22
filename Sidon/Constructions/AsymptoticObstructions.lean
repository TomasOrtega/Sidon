import Sidon.Constructions.Obstructions
import Sidon.NumberTheory.RelativePrimeIntervals

/-! # Sharp asymptotic modular obstructions at every large length -/

noncomputable section

namespace Sidon

open Filter Topology

theorem eventually_exists_prime_construction_below {q : ℕ} (hq : 0 < q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ q * (p ^ 2 - 1) + 1 ≤ N ∧
      (1 / Real.sqrt q - δ) * Real.sqrt N ≤ p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqR
  have hscale : Tendsto (fun N : ℕ ↦ Real.sqrt ((N : ℝ) / q)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hqR)
  have hprimes := relativePrimeIntervals (δ * Real.sqrt q) (mul_pos hδ hsqrtq)
  filter_upwards [hscale.eventually hprimes] with N hN
  obtain ⟨p, hp, hlow, hupp⟩ := hN
  have hratio : 0 ≤ (N : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hqR.le
  have hpow : (p : ℝ) ^ 2 ≤ (N : ℝ) / q := by
    nlinarith [Real.sq_sqrt hratio, Real.sqrt_nonneg ((N : ℝ) / q),
      Nat.cast_nonneg (α := ℝ) p]
  have hprod : (q : ℝ) * (p : ℝ) ^ 2 ≤ N := by
    simpa [mul_comm] using (le_div_iff₀ hqR).mp hpow
  have hprodNat : q * p ^ 2 ≤ N := by exact_mod_cast hprod
  refine ⟨p, hp, (construction_length_le q p hq hp.pos).trans hprodNat, ?_⟩
  rw [Real.sqrt_div (Nat.cast_nonneg N)] at hlow
  have heq :
      (1 / Real.sqrt q - δ) * Real.sqrt N =
        (1 - δ * Real.sqrt q) * (Real.sqrt N / Real.sqrt q) := by
    field_simp
  exact heq.trans_le hlow

/-- Proposition 1.13, with its all-length asymptotic quantifier. -/
theorem eventually_exists_sharp_odd_obstruction {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℤ, S ⊆ interval N ∧
      (1 / Real.sqrt 2 - δ) * Real.sqrt N ≤ S.card ∧ IsSidonSet (S : Set ℤ) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, a + b + c + d ≠ e := by
  filter_upwards [eventually_exists_prime_construction_below (q := 2) (by norm_num) hδ]
    with N hN
  obtain ⟨p, hp, hlength, hcard⟩ := hN
  obtain ⟨S, hSN, hScard, hS, hno⟩ := exists_prime_odd_obstruction p hp
  refine ⟨S, ?_, ?_, hS, hno⟩
  · intro x hx
    obtain ⟨hx0, hxL⟩ := mem_interval.mp (hSN hx)
    exact mem_interval.mpr ⟨hx0, hxL.trans (by exact_mod_cast hlength)⟩
  · simpa only [hScard, Nat.cast_ofNat] using hcard

/-- The modular construction also has its sharp all-length asymptotic density. -/
theorem exists_eventually_sharp_residue_obstruction {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (hσ : (∑ i, a i) ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℤ,
      S ⊆ interval N ∧ (1 / Real.sqrt q - δ) * Real.sqrt N ≤ S.card ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ x : ι → ℤ, (∀ i, x i ∈ S) → (∑ i, a i * x i) ≠ 0 := by
  obtain ⟨q, hq, hqdvd⟩ := exists_prime_not_dvd hσ
  refine ⟨q, hq, ?_⟩
  intro δ hδ
  filter_upwards [eventually_exists_prime_construction_below hq.pos hδ] with N hN
  obtain ⟨p, hp, hlength, hcard⟩ := hN
  obtain ⟨S, hSN, hScard, hS, hno⟩ :=
    exists_prime_residue_obstruction a q hq.pos hqdvd p hp
  refine ⟨S, ?_, ?_, hS, hno⟩
  · intro x hx
    obtain ⟨hx0, hxL⟩ := mem_interval.mp (hSN hx)
    exact mem_interval.mpr ⟨hx0, hxL.trans (by exact_mod_cast hlength)⟩
  · simpa only [hScard] using hcard

end Sidon
