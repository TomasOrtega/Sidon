module

public import Sidon.NumberTheory.DirichletMollifier
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Convolution

@[expose] public section

/-! # The actual absolutely convergent mollifier Dirichlet series -/

noncomputable section

namespace Sidon

/-- Finite Möbius truncation as an arithmetic function. -/
def truncatedMoebius (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ N then (ArithmeticFunction.moebius n : ℂ) else 0, by simp⟩

@[simp] theorem truncatedMoebius_apply (N n : ℕ) :
    truncatedMoebius N n = if n ≤ N then (ArithmeticFunction.moebius n : ℂ) else 0 := rfl

theorem LSeriesHasSum_truncatedMoebius (N : ℕ) (s : ℂ) :
    LSeriesHasSum (truncatedMoebius N) s (dirichletMollifier N s) := by
  have hfinite : ∀ n ∉ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hNn : ¬n ≤ N := by
        intro h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, h⟩)
      simp [LSeries.term, hn0, truncatedMoebius_apply, hNn]
  have hh : HasSum (LSeries.term (truncatedMoebius N) s)
      (∑ n ∈ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n) :=
    hasSum_sum_of_ne_finset_zero hfinite
  have heq : (∑ n ∈ Finset.Icc 1 N, LSeries.term (truncatedMoebius N) s n) =
      dirichletMollifier N s := by
    unfold dirichletMollifier
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp only [LSeries.term, hn0, ite_false, truncatedMoebius_apply, hnN, ite_true]
    rw [div_eq_mul_inv, ← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    congr 2
    ring
  exact heq ▸ hh

/-- The finite divisor coefficient is the actual Dirichlet-convolution coefficient. -/
theorem zeta_mul_truncatedMoebius_apply (N n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * truncatedMoebius N) n =
      (mollifierCoefficient N n : ℂ) := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [mollifierCoefficient, Int.cast_sum, Finset.sum_filter, truncatedMoebius_apply,
    Int.cast_ite, Int.cast_zero]

/-- Absolute convergence justifies the infinite product and its finite coefficients. -/
theorem LSeriesHasSum_mollifierCoefficient {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    LSeriesHasSum (fun n => (mollifierCoefficient N n : ℂ)) s
      (riemannZeta s * dirichletMollifier N s) := by
  have hz : LSeriesHasSum ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ)
      s (riemannZeta s) := ArithmeticFunction.LSeriesHasSum_zeta hs
  have hm : LSeriesHasSum (truncatedMoebius N) s (dirichletMollifier N s) :=
    LSeriesHasSum_truncatedMoebius N s
  have hh := hz.convolution hm
  apply (LSeriesHasSum_congr s (riemannZeta s * dirichletMollifier N s)
    (f := fun n => (mollifierCoefficient N n : ℂ))
    (g := LSeries.convolution
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ℕ → ℂ) (truncatedMoebius N))
    (fun {n} _ => ?_)).mpr hh
  rw [ArithmeticFunction.coe_mul]
  exact (zeta_mul_truncatedMoebius_apply N n).symm

end Sidon
