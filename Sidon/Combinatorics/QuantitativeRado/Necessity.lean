module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # A finite colouring when no coefficient subsum vanishes -/

noncomputable section

namespace Sidon.QuantitativeRado

/-- Colour a positive integer by its first nonzero base-`p` digit. -/
def primeDigitColour (p : ℕ) (hp : 0 < p) (n : ℕ) : Fin p :=
  ⟨n.divMaxPow p % p, Nat.mod_lt _ hp⟩

@[simp]
theorem primeDigitColour_cast {p : ℕ} (hp : 0 < p) (n : ℕ) :
    ((primeDigitColour p hp n).val : ZMod p) = (n.divMaxPow p : ZMod p) := by
  exact ZMod.natCast_mod _ _

theorem exists_subsum_dvd_of_primeDigit_monochromatic
    {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℕ} (hp : p.Prime)
    (a : ι → ℤ) (x : ι → ℕ) (hx : ∀ i, 0 < x i)
    (hmono : ∀ i j, primeDigitColour p hp.pos (x i) = primeDigitColour p hp.pos (x j))
    (heq : ∑ i, a i * (x i : ℤ) = 0) :
    ∃ I : Finset ι, I.Nonempty ∧ (p : ℤ) ∣ ∑ i ∈ I, a i := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let v : ι → ℕ := fun i => padicValNat p (x i)
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  let k := v i₀
  have hk (i : ι) : k ≤ v i := hmin i (Finset.mem_univ _)
  let I := Finset.univ.filter fun i => v i = k
  have hI : I.Nonempty := ⟨i₀, by simp [I, k]⟩
  let y : ι → ℤ := fun i => (p : ℤ) ^ (v i - k) * (x i).divMaxPow p
  have hxy (i : ι) : (x i : ℤ) = (p : ℤ) ^ k * y i := by
    dsimp only [y]
    rw [← mul_assoc, pow_mul_pow_sub _ (hk i)]
    exact_mod_cast (Nat.pow_padicValNat_mul_divMaxPow p (x i)).symm
  have hnormalized : ∑ i, a i * y i = 0 := by
    have hmul : (p : ℤ) ^ k * (∑ i, a i * y i) = 0 := by
      rw [Finset.mul_sum]
      convert heq using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hxy]
      ring
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  let c : ZMod p := ((primeDigitColour p hp.pos (x i₀)).val : ZMod p)
  have hc : c ≠ 0 := by
    dsimp only [c]
    rw [primeDigitColour_cast]
    exact (ZMod.natCast_eq_zero_iff _ _).not.mpr
      (Nat.not_dvd_divMaxPow hp.one_lt (hx i₀).ne')
  have hy (i : ι) : (y i : ZMod p) = if v i = k then c else 0 := by
    by_cases hi : v i = k
    · have hh := congrArg (fun j : Fin p => (j.val : ZMod p)) (hmono i i₀)
      simpa [y, hi, c] using hh
    · have hsub : v i - k ≠ 0 := by have := hk i; omega
      simp [y, hi, hsub]
  have hnormalized_mod : (∑ i, (a i : ZMod p) * (y i : ZMod p)) = 0 := by
    have hh := congrArg (fun z : ℤ => (z : ZMod p)) hnormalized
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using hh
  have hsum : (∑ i, (a i : ZMod p) * (y i : ZMod p)) =
      (∑ i ∈ I, (a i : ZMod p)) * c := by
    rw [Finset.sum_mul]
    dsimp only [I]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [hy]
    split_ifs <;> simp
  have hsubsum : (∑ i ∈ I, (a i : ZMod p)) = 0 :=
    (mul_eq_zero.mp (hsum ▸ hnormalized_mod)).resolve_right hc
  refine ⟨I, hI, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_⟩
  simpa using hsubsum

theorem exists_finite_colouring_without_monochromatic_linearSolution
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℤ)
    (ha : ∀ I : Finset ι, I.Nonempty → (∑ i ∈ I, a i) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ χ : ℕ → Fin r, ∀ x : ι → ℕ,
      (∀ i, 0 < x i) → (∀ i j, χ (x i) = χ (x j)) →
        (∑ i, a i * (x i : ℤ)) ≠ 0 := by
  classical
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes ((∑ i, (a i).natAbs) + 1)
  refine ⟨p, hp.pos, primeDigitColour p hp.pos, fun x hx hmono heq => ?_⟩
  obtain ⟨I, hI, hdvd⟩ := exists_subsum_dvd_of_primeDigit_monochromatic hp a x hx hmono heq
  have hsum : (∑ i ∈ I, a i).natAbs ≤ ∑ i, (a i).natAbs := by
    apply (Int.natAbs_sum_le I a).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun _ _ _ => Nat.zero_le _)
  have hsmall : (∑ i ∈ I, a i).natAbs < (p : ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using lt_of_le_of_lt hsum (by omega)
  exact ha I hI (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall)

theorem exists_integer_colouring_without_positive_monochromatic_linearSolution
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℤ)
    (ha : ∀ I : Finset ι, I.Nonempty → (∑ i ∈ I, a i) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ χ : ℤ → Fin r, ∀ x : ι → ℤ,
      (∀ i, 0 < x i) → (∀ i j, χ (x i) = χ (x j)) →
        (∑ i, a i * x i) ≠ 0 := by
  obtain ⟨r, hr, χ, hχ⟩ := exists_finite_colouring_without_monochromatic_linearSolution a ha
  refine ⟨r, hr, fun n => χ n.toNat, fun x hx hmono heq => ?_⟩
  have hpos (i : ι) : 0 < (x i).toNat := by
    have hi := hx i
    omega
  apply hχ (fun i => (x i).toNat) hpos hmono
  simpa only [Int.toNat_of_nonneg (hx _).le] using heq

end Sidon.QuantitativeRado
