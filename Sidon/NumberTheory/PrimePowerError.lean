module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! # Removing nonprime powers from a Mangoldt interval estimate -/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt

namespace Sidon

def chebyshevPsi (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, Λ n

def chebyshevTheta (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if n.Prime then Real.log n else 0

def nonprimeMangoldtMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if n.Prime then 0 else Λ n

def nonprimePowers (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => IsPrimePow n ∧ ¬n.Prime

theorem nonprimeMangoldtMass_nonneg (N : ℕ) : 0 ≤ nonprimeMangoldtMass N := by
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

theorem chebyshevPsi_sub_theta (N : ℕ) :
    chebyshevPsi N - chebyshevTheta N = nonprimeMangoldtMass N := by
  unfold chebyshevPsi chebyshevTheta nonprimeMangoldtMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · rw [if_pos hn, if_pos hn, ArithmeticFunction.vonMangoldt_apply_prime hn, sub_self]
  · rw [if_neg hn, if_neg hn, sub_zero]

theorem nonprimeMangoldtMass_eq_sum (N : ℕ) :
    nonprimeMangoldtMass N = ∑ n ∈ nonprimePowers N, Λ n := by
  unfold nonprimeMangoldtMass nonprimePowers
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, not_true_eq_false, and_false, if_true, if_false]
  · by_cases hpow : IsPrimePow n
    · simp only [hp, hpow, not_false_eq_true, and_self, if_true, if_false]
    · have hzero : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
      simp only [hzero, ite_self]

theorem nonprimePowers_subset_image (N : ℕ) :
    nonprimePowers N ⊆
      ((Finset.Icc 1 (Nat.sqrt N)) ×ˢ (Finset.Icc 1 (Nat.log 2 N))).image
        (fun a : ℕ × ℕ => a.1 ^ a.2) := by
  intro n hn
  obtain ⟨hnI, hpow, hnotprime⟩ := Finset.mem_filter.mp hn
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpow
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at hpk
    exact hnotprime (hpk ▸ hp)
  have hnp : p ^ k ≤ N := hpk ▸ (Finset.mem_Icc.mp hnI).2
  have hp2 : p ^ 2 ≤ N := (Nat.pow_le_pow_right hp.pos hk2).trans hnp
  have hplower : 1 ≤ p := hp.one_lt.le
  have hpupper : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hp2
  have hkupper : k ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hp.two_le k).trans hnp)
  exact Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hplower, hpupper⟩, Finset.mem_Icc.mpr ⟨hk, hkupper⟩⟩, hpk⟩

theorem card_nonprimePowers_le (N : ℕ) :
    (nonprimePowers N).card ≤ Nat.sqrt N * Nat.log 2 N := by
  apply (Finset.card_le_card (nonprimePowers_subset_image N)).trans
  apply Finset.card_image_le.trans
  simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  rfl

/-- The exact finite error needed when converting a `ψ` estimate into primes. -/
theorem nonprimeMangoldtMass_le {N : ℕ} (hN : 1 ≤ N) :
    nonprimeMangoldtMass N ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N := by
  rw [nonprimeMangoldtMass_eq_sum]
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ ∑ _n ∈ nonprimePowers N, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnI, _, _⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN))
    _ = (nonprimePowers N).card * Real.log N := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast card_nonprimePowers_le N

theorem chebyshevTheta_eq_of_no_prime {M N : ℕ} (hMN : M ≤ N)
    (hno : ¬∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ N) :
    chebyshevTheta M = chebyshevTheta N := by
  unfold chebyshevTheta
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hMN)
  intro n hnN hnM
  have hn : M < n := by
    by_contra h
    apply hnM
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnN).1, by omega⟩
  have hnp : ¬n.Prime := fun hp => hno ⟨n, hp, hn, (Finset.mem_Icc.mp hnN).2⟩
  exact if_neg hnp

/-- A sufficiently large Mangoldt increment contains an actual prime, not just a prime power. -/
theorem exists_prime_of_mangoldt_increment {M N : ℕ} (hMN : M ≤ N) (hN : 1 ≤ N)
    (hinc : (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N <
      chebyshevPsi N - chebyshevPsi M) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ N := by
  by_contra hno
  have htheta := chebyshevTheta_eq_of_no_prime hMN hno
  have hupper := nonprimeMangoldtMass_le hN
  have hzero := nonprimeMangoldtMass_nonneg M
  have hNid := chebyshevPsi_sub_theta N
  have hMid := chebyshevPsi_sub_theta M
  linarith


theorem nat_log_two_le_real_log {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
  have hpow : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

theorem nonprimeMangoldtMass_le_real {N : ℕ} (hN : 1 ≤ N) :
    nonprimeMangoldtMass N ≤ (Real.log 2)⁻¹ * Real.sqrt N * (Real.log N) ^ 2 := by
  have hroot : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le N
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) * Real.log N := nonprimeMangoldtMass_le hN
    _ ≤ Real.sqrt N * (Real.log N / Real.log 2) * Real.log N := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact mul_le_mul hroot (nat_log_two_le_real_log hN) (Nat.cast_nonneg _)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The nonprime-power contribution is negligible at the required `2/3` scale. -/
theorem nonprimeMangoldtMass_isLittleO :
    (fun N : ℕ => nonprimeMangoldtMass N) =o[Filter.atTop]
      (fun N : ℕ => (N : ℝ) ^ ((2 : ℝ) / 3)) := by
  have hlog := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)
  have hlog2 := (hlog.mul hlog).mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => x ^ ((1 : ℝ) / 2)) Filter.atTop)
  have hpow : (fun x : ℝ => x ^ ((1 : ℝ) / 12) * x ^ ((1 : ℝ) / 12) * x ^ ((1 : ℝ) / 2)) =ᶠ[Filter.atTop]
      (fun x => x ^ ((2 : ℝ) / 3)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.rpow_add (by linarith : 0 < x), ← Real.rpow_add (by linarith : 0 < x)]
    norm_num
  have hh := (hlog2.congr' Filter.EventuallyEq.rfl hpow).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hmain := hh.const_mul_left ((Real.log 2)⁻¹)
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun N : ℕ =>
    (Real.log 2)⁻¹ * (Real.log (N : ℝ) * Real.log N * (N : ℝ) ^ ((1 : ℝ) / 2))) _ hmain
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (nonprimeMangoldtMass_nonneg N), one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  convert nonprimeMangoldtMass_le_real hN using 1
  rw [Real.sqrt_eq_rpow]
  ring

end Sidon
