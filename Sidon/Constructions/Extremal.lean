import Sidon.Constructions.BoseChowla
import Sidon.NumberTheory.PrimeIntervals
import Sidon.Combinatorics.SharpIntervalSize
import Sidon.FourierUniformity

/-! # Maximum Sidon sets and the precise short-prime-interval dependency -/

noncomputable section

namespace Sidon

/-- A maximum-cardinality Sidon subset of `[N]`. -/
def IsMaximumSidon (N : ℕ) (S : Finset ℤ) : Prop :=
  IsSidonSet (S : Set ℤ) ∧ S ⊆ interval N ∧
    ∀ T : Finset ℤ, IsSidonSet (T : Set ℤ) → T ⊆ interval N → T.card ≤ S.card

theorem exists_maximum_sidon (N : ℕ) : ∃ S : Finset ℤ, IsMaximumSidon N S := by
  classical
  let A := (interval N).powerset.filter (fun S : Finset ℤ => IsSidonSet (S : Set ℤ))
  have hA : A.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro a b c d ha
    simp at ha
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image A Finset.card hA
  obtain ⟨hSN, hSidon⟩ := Finset.mem_filter.mp hS
  refine ⟨S, hSidon, Finset.mem_powerset.mp hSN, fun T hT hTN => ?_⟩
  exact hmax T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTN, hT⟩)

theorem exists_sidon_of_prime_le_sqrt {N p : ℕ} (hp : p.Prime)
    (hpN : (p : ℝ) ≤ Real.sqrt N) :
    ∃ S : Finset ℤ, IsSidonSet (S : Set ℤ) ∧ S ⊆ interval N ∧ S.card = p := by
  obtain ⟨S, hSN, hcard, hS⟩ := BoseChowla.exists_prime_sidon p hp
  have hpN' : p ^ 2 ≤ N := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hpN 2
    rw [hs] at hsq
    exact_mod_cast hsq
  refine ⟨S, hS, fun n hn => ?_, hcard⟩
  have hh := mem_interval.mp (hSN hn)
  exact mem_interval.mpr ⟨hh.1, hh.2.trans (by exact_mod_cast (show p ^ 2 - 1 ≤ N by omega))⟩

/-- Bose–Chowla transfers the exact `2/3` prime-gap hypothesis to cardinality loss `N^(1/3)`. -/
theorem exists_sidon_near_sqrt_of_prime_interval {N : ℕ} {C X : ℝ}
    (hgap : PrimeIntervalBound ((2 : ℝ) / 3) C X) (hX : X ≤ Real.sqrt N) :
    ∃ S : Finset ℤ, IsSidonSet (S : Set ℤ) ∧ S ⊆ interval N ∧
      Real.sqrt N - C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ S.card := by
  obtain ⟨p, hp, hlow, hupp⟩ := hgap (Real.sqrt N) hX
  obtain ⟨S, hS, hSN, hcard⟩ := exists_sidon_of_prime_le_sqrt hp hupp
  refine ⟨S, hS, hSN, ?_⟩
  rw [hcard]
  have heq : (Real.sqrt (N : ℝ)) ^ ((2 : ℝ) / 3) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    norm_num
  simpa only [heq] using hlow

theorem IsMaximumSidon.card_lower_of_prime_interval {N : ℕ} {S : Finset ℤ}
    (hS : IsMaximumSidon N S) {C X : ℝ}
    (hgap : PrimeIntervalBound ((2 : ℝ) / 3) C X) (hX : X ≤ Real.sqrt N) :
    Real.sqrt N - C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ S.card := by
  obtain ⟨T, hT, hTN, hcard⟩ := exists_sidon_near_sqrt_of_prime_interval hgap hX
  exact hcard.trans (by exact_mod_cast hS.2.2 T hT hTN)

theorem IsMaximumSidon.deviation_le_of_prime_interval {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsMaximumSidon N S) {C X : ℝ} (hC : 0 ≤ C)
    (hgap : PrimeIntervalBound ((2 : ℝ) / 3) C X) (hX : X ≤ Real.sqrt N) :
    sidonDeviation N S ≤ (C + 4) * (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN'
  have hlower := hS.card_lower_of_prime_interval hgap hX
  have hupper := IsSidonSet.card_le_sqrt_add_four_mul_rpow hN hS.1 hS.2.1
  have hquarter : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hpower : (N : ℝ) ^ (-(1 / 6 : ℝ)) * Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN']
    norm_num
  unfold sidonDeviation
  apply abs_le.mpr
  constructor
  · have htarget : (1 - (C + 4) * (N : ℝ) ^ (-(1 / 6 : ℝ))) * Real.sqrt N ≤ S.card := by
      rw [sub_mul, one_mul, mul_assoc, hpower]
      nlinarith [Real.rpow_nonneg hN'.le ((1 : ℝ) / 3)]
    have := (le_div_iff₀ hroot).mpr htarget
    linarith
  · have htarget : (S.card : ℝ) ≤
        (1 + (C + 4) * (N : ℝ) ^ (-(1 / 6 : ℝ))) * Real.sqrt N := by
      rw [add_mul, one_mul, mul_assoc, hpower]
      nlinarith [Real.rpow_nonneg hN'.le ((1 : ℝ) / 3)]
    have := (div_le_iff₀ hroot).mpr htarget
    linarith


/-- The exact Fourier exponent in Corollary 1.4 follows from a `2/3` prime-gap bound. -/
theorem IsMaximumSidon.fourier_uniformity_of_prime_interval {N : ℕ} (hN : 0 < N)
    {S : Finset ℤ} (hS : IsMaximumSidon N S) {C X : ℝ} (hC : 0 ≤ C)
    (hgap : PrimeIntervalBound ((2 : ℝ) / 3) C X) (hX : X ≤ Real.sqrt N)
    (hm : Real.sqrt N / 2 ≤ S.card) :
    ‖fourierSum (indicatorFinsupp S) -
      ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
      (32 * Real.sqrt (C + 5)) * (S.card : ℝ) * (N : ℝ) ^ (-(1 / 12 : ℝ)) := by
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hdev := hS.deviation_le_of_prime_interval hN hC hgap hX
  have hE : sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ)) ≤
      (C + 5) * (N : ℝ) ^ (-(1 / 6 : ℝ)) := by linarith
  have hroot : Real.sqrt ((N : ℝ) ^ (-(1 / 6 : ℝ))) =
      (N : ℝ) ^ (-(1 / 12 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN'.le]
    norm_num
  calc
    _ ≤ 16 * Real.sqrt N *
        Real.sqrt (sidonDeviation N S + (N : ℝ) ^ (-(1 / 6 : ℝ))) :=
      sidon_fourier_uniformity hN hS.1 hS.2.1
    _ ≤ 16 * Real.sqrt N * Real.sqrt ((C + 5) * (N : ℝ) ^ (-(1 / 6 : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) (by positivity)
    _ = (16 * Real.sqrt (C + 5) * (N : ℝ) ^ (-(1 / 12 : ℝ))) * Real.sqrt N := by
      rw [Real.sqrt_mul (by linarith : 0 ≤ C + 5), hroot]
      ring
    _ ≤ (16 * Real.sqrt (C + 5) * (N : ℝ) ^ (-(1 / 12 : ℝ))) * (2 * S.card) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- A conditional all-length version; the short-prime-interval input is visible in its type. -/
theorem largest_sidon_fourier_uniformity_of_prime_interval {C X : ℝ} (hC : 0 ≤ C)
    (hgap : PrimeIntervalBound ((2 : ℝ) / 3) C X) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, IsMaximumSidon N S →
      ‖fourierSum (indicatorFinsupp S) -
        ((S.card : ℝ) / N) • fourierSum (indicatorFinsupp (interval N))‖ ≤
        K * ‖fourierSum (indicatorFinsupp S)‖ * (N : ℝ) ^ (-(1 / 12 : ℝ)) := by
  have hlimit : Filter.Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 6 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let L : ℕ := Nat.ceil ((max X 1) ^ 2)
  refine ⟨max 1 (max M L), le_max_left _ _, 32 * Real.sqrt (C + 5), by positivity,
    fun N hN S hS => ?_⟩
  have hNpos : 0 < N := by omega
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hX : X ≤ Real.sqrt N := by
    apply (le_max_left X 1).trans
    apply Real.le_sqrt_of_sq_le
    have hceil : (max X 1) ^ 2 ≤ (L : ℝ) := Nat.le_ceil _
    have hLN : (L : ℝ) ≤ N := by exact_mod_cast (show L ≤ N by omega)
    exact hceil.trans hLN
  have hlow := hS.card_lower_of_prime_interval hgap hX
  have hsmall : C * (N : ℝ) ^ (-(1 / 6 : ℝ)) < 1 / 2 := hM N (by omega)
  have hpower : (N : ℝ) ^ (-(1 / 6 : ℝ)) * Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN']
    norm_num
  have hprod := mul_le_mul_of_nonneg_right hsmall.le (Real.sqrt_nonneg (N : ℝ))
  rw [mul_assoc, hpower] at hprod
  have hmhalf : Real.sqrt N / 2 ≤ S.card := by linarith
  rw [norm_fourierSum_indicatorFinsupp]
  exact hS.fourier_uniformity_of_prime_interval hNpos hC hgap hX hmhalf

end Sidon
