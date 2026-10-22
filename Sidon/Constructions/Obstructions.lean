import Sidon.Constructions.BoseChowla
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Bertrand

/-! # Dense finite Sidon families with modular obstructions -/

noncomputable section

open scoped Classical

namespace Sidon

/-- The affine image contained in the residue class one modulo `q`. -/
def residueImage (q : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.image fun x => (q : ℤ) * x + 1

theorem card_residueImage {q : ℕ} (hq : 0 < q) (S : Finset ℤ) :
    (residueImage q S).card = S.card :=
  card_image_affine S (by exact_mod_cast hq.ne') 1

theorem isSidon_residueImage {q : ℕ} (hq : 0 < q) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) : IsSidonSet (residueImage q S : Set ℤ) := by
  simpa only [residueImage, Finset.coe_image] using
    hS.image_affine (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0) 1

theorem residueImage_subset_interval {q N L : ℕ} (hq : 0 < q)
    (hL : q * L + 1 ≤ N) {S : Finset ℤ} (hS : S ⊆ interval L) :
    residueImage q S ⊆ interval N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hy' := mem_interval.mp (hS hy)
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
  have hbound : (q : ℤ) * y ≤ q * L :=
    mul_le_mul_of_nonneg_left hy'.2 hqpos.le
  have hLN : (q : ℤ) * L + 1 ≤ N := by exact_mod_cast hL
  apply mem_interval.mpr
  constructor <;> nlinarith [hy'.1]

theorem residueImage_no_solution {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (q : ℕ) (S : Finset ℤ) (hσ : ¬(q : ℤ) ∣ ∑ i, a i)
    (x : ι → ℤ) (hx : ∀ i, x i ∈ residueImage q S) :
    (∑ i, a i * x i) ≠ 0 := by
  have hx' : ∀ i, ∃ y ∈ S, (q : ℤ) * y + 1 = x i :=
    fun i => Finset.mem_image.mp (hx i)
  choose y hy hxy using hx'
  have heq : (∑ i, a i * x i) = (q : ℤ) * (∑ i, a i * y i) + ∑ i, a i := by
    calc
      (∑ i, a i * x i) = ∑ i, a i * ((q : ℤ) * y i + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hxy i]
      _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
  intro hz
  apply hσ
  refine ⟨-(∑ i, a i * y i), ?_⟩
  rw [hz] at heq
  linear_combination -heq

theorem exists_prime_not_dvd {σ : ℤ} (hσ : σ ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ¬(q : ℤ) ∣ σ := by
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (σ.natAbs + 1)
  refine ⟨q, hq, ?_⟩
  intro hd
  have hd' : q ∣ σ.natAbs := Int.natCast_dvd.mp hd
  exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hσ) (by omega) hd'

/-- An exact finite version of the parity construction at prime-field lengths. -/
theorem exists_prime_odd_obstruction (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℤ, S ⊆ interval (2 * (p ^ 2 - 1) + 1) ∧ S.card = p ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, a + b + c + d ≠ e := by
  obtain ⟨S₀, hS₀N, hS₀card, hS₀⟩ := BoseChowla.exists_prime_sidon p hp
  refine ⟨oddImage S₀, oddImage_subset_interval le_rfl hS₀N,
    (card_oddImage S₀).trans hS₀card, isSidonSet_oddImage hS₀, ?_⟩
  intro a ha b hb c hc d hd e he
  exact oddImage_no_solution S₀ ha hb hc hd he

/-- The same construction for any modular obstruction to a homogeneous equation. -/
theorem exists_prime_residue_obstruction {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (q : ℕ) (hq : 0 < q) (hσ : ¬(q : ℤ) ∣ ∑ i, a i)
    (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℤ, S ⊆ interval (q * (p ^ 2 - 1) + 1) ∧ S.card = p ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ x : ι → ℤ, (∀ i, x i ∈ S) → (∑ i, a i * x i) ≠ 0 := by
  obtain ⟨S₀, hS₀N, hS₀card, hS₀⟩ := BoseChowla.exists_prime_sidon p hp
  refine ⟨residueImage q S₀, residueImage_subset_interval hq le_rfl hS₀N,
    (card_residueImage hq S₀).trans hS₀card, isSidon_residueImage hq hS₀,
    residueImage_no_solution a q S₀ hσ⟩

theorem construction_length_le (q p : ℕ) (hq : 0 < q) (hp : 0 < p) :
    q * (p ^ 2 - 1) + 1 ≤ q * p ^ 2 := by
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hp2
  nlinarith

theorem construction_card_lower (q p : ℕ) (hq : 0 < q) (hp : 0 < p) :
    Real.sqrt (q * (p ^ 2 - 1) + 1 : ℕ) / Real.sqrt q ≤ (p : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hqpos)).mpr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hqpos.le]
  have hlen : ((q * (p ^ 2 - 1) + 1 : ℕ) : ℝ) ≤ q * (p : ℝ) ^ 2 := by
    exact_mod_cast construction_length_le q p hq hp
  nlinarith

theorem construction_lengths_unbounded (q : ℕ) (hq : 0 < q) (K : ℕ) :
    ∃ p : ℕ, p.Prime ∧ K ≤ q * (p ^ 2 - 1) + 1 := by
  obtain ⟨p, hKp, hp⟩ := Nat.exists_infinite_primes (K + 2)
  refine ⟨p, hp, ?_⟩
  have hp2 : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hsub := Nat.sub_add_cancel hp2
  have hmul : p ^ 2 - 1 ≤ q * (p ^ 2 - 1) := Nat.le_mul_of_pos_left _ hq
  nlinarith

theorem exists_arbitrarily_large_odd_obstruction (K : ℕ) :
    ∃ N : ℕ, K ≤ N ∧ ∃ S : Finset ℤ, S ⊆ interval N ∧
      Real.sqrt N / Real.sqrt 2 ≤ S.card ∧ IsSidonSet (S : Set ℤ) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, a + b + c + d ≠ e := by
  obtain ⟨p, hp, hKN⟩ := construction_lengths_unbounded 2 (by norm_num) K
  obtain ⟨S, hSN, hcard, hS, hno⟩ := exists_prime_odd_obstruction p hp
  refine ⟨2 * (p ^ 2 - 1) + 1, hKN, S, hSN, ?_, hS, hno⟩
  rw [hcard]
  exact construction_card_lower 2 p (by norm_num) hp.pos

theorem exists_arbitrarily_large_residue_obstruction {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (hσ : (∑ i, a i) ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ ∃ S : Finset ℤ,
      S ⊆ interval N ∧ Real.sqrt N / Real.sqrt q ≤ S.card ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ x : ι → ℤ, (∀ i, x i ∈ S) → (∑ i, a i * x i) ≠ 0 := by
  obtain ⟨q, hq, hqdvd⟩ := exists_prime_not_dvd hσ
  refine ⟨q, hq, ?_⟩
  intro K
  obtain ⟨p, hp, hKN⟩ := construction_lengths_unbounded q hq.pos K
  obtain ⟨S, hSN, hcard, hS, hno⟩ := exists_prime_residue_obstruction a q hq.pos hqdvd p hp
  refine ⟨q * (p ^ 2 - 1) + 1, hKN, S, hSN, ?_, hS, hno⟩
  rw [hcard]
  exact construction_card_lower q p hq.pos hp.pos

/-- Bertrand's postulate supplies construction parameters at every sufficiently large length. -/
theorem exists_prime_construction_below {q N : ℕ} (hq : 0 < q) (hN : 4 * q + 1 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ q * (p ^ 2 - 1) + 1 ≤ N ∧ N ≤ 4 * q * p ^ 2 := by
  let M := (N - 1) / q
  have hM : 4 ≤ M := (Nat.le_div_iff_mul_le hq).mpr (by omega)
  let l := Nat.sqrt M
  have hl : 2 ≤ l := Nat.le_sqrt.mpr (by omega : 2 * 2 ≤ M)
  let n := l / 2
  have hn : n ≠ 0 := by dsimp [n]; omega
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  have hpl : p ≤ l := hpn.trans (by dsimp [n]; omega)
  have hpM : p ^ 2 ≤ M := by
    have hsqrt := Nat.sqrt_le M
    change l * l ≤ M at hsqrt
    nlinarith
  have hMl : M < (l + 1) ^ 2 := Nat.lt_succ_sqrt' M
  have hlp : l + 1 ≤ 2 * p := by dsimp [n] at hnp; omega
  have hMp : M + 1 ≤ 4 * p ^ 2 := by nlinarith
  have hdiv : q * M + (N - 1) % q = N - 1 := Nat.div_add_mod (N - 1) q
  have hmod : (N - 1) % q < q := Nat.mod_lt _ hq
  have hNpos : 0 < N := by omega
  have hNm1 := Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)
  have hNupper : N ≤ q * (M + 1) := by nlinarith
  have hMlower : q * M ≤ N - 1 := Nat.mul_div_le _ _
  refine ⟨p, hp, ?_, ?_⟩
  · have hsmall : q * (p ^ 2 - 1) ≤ q * M :=
      Nat.mul_le_mul_left q ((Nat.sub_le _ _).trans hpM)
    omega
  · have hmul := Nat.mul_le_mul_left q hMp
    nlinarith

theorem card_lower_of_square_bound {N q m : ℕ} (hq : 0 < q)
    (hN : N ≤ 4 * q * m ^ 2) : Real.sqrt N / (2 * Real.sqrt q) ≤ (m : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt q)).mpr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hN' : (N : ℝ) ≤ 4 * q * (m : ℝ) ^ 2 := by exact_mod_cast hN
  rw [mul_pow, mul_pow, Real.sq_sqrt hqpos.le]
  nlinarith

/-- The positive-density assertion in Remark 1.14 holds at every sufficiently large length. -/
theorem exists_dense_residue_obstruction {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (hσ : (∑ i, a i) ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ∀ N : ℕ, 4 * q + 1 ≤ N → ∃ S : Finset ℤ,
      S ⊆ interval N ∧ Real.sqrt N / (2 * Real.sqrt q) ≤ S.card ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ x : ι → ℤ, (∀ i, x i ∈ S) → (∑ i, a i * x i) ≠ 0 := by
  obtain ⟨q, hq, hqdvd⟩ := exists_prime_not_dvd hσ
  refine ⟨q, hq, ?_⟩
  intro N hN
  obtain ⟨p, hp, hsmall, hlarge⟩ := exists_prime_construction_below hq.pos hN
  obtain ⟨S, hSN, hcard, hS, hno⟩ := exists_prime_residue_obstruction a q hq.pos hqdvd p hp
  refine ⟨S, ?_, ?_, hS, hno⟩
  · intro x hx
    have hxi := mem_interval.mp (hSN hx)
    exact mem_interval.mpr ⟨hxi.1, hxi.2.trans (by exact_mod_cast hsmall)⟩
  · rw [hcard]
    exact card_lower_of_square_bound hq.pos hlarge

/-- An unconditional positive-density parity obstruction at every large length. -/
theorem exists_dense_odd_obstruction {N : ℕ} (hN : 9 ≤ N) :
    ∃ S : Finset ℤ, S ⊆ interval N ∧ Real.sqrt N / (2 * Real.sqrt 2) ≤ S.card ∧
      IsSidonSet (S : Set ℤ) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, a + b + c + d ≠ e := by
  obtain ⟨p, hp, hsmall, hlarge⟩ := exists_prime_construction_below (q := 2) (by norm_num) hN
  obtain ⟨S, hSN, hcard, hS, hno⟩ := exists_prime_odd_obstruction p hp
  refine ⟨S, ?_, ?_, hS, hno⟩
  · intro x hx
    have hxi := mem_interval.mp (hSN hx)
    exact mem_interval.mpr ⟨hxi.1, hxi.2.trans (by exact_mod_cast hsmall)⟩
  · rw [hcard]
    exact card_lower_of_square_bound (by norm_num) hlarge

end Sidon
