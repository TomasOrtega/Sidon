import Sidon.NumberTheory.MollifierEndpoint

/-! # The actual finite Möbius mollifier and its Dirichlet coefficients -/

noncomputable section

namespace Sidon

/-- A finite entire Dirichlet polynomial, with the endpoint included. -/
def dirichletMollifier (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))

/-- Coefficient of `n⁻ˢ` in the product `ζ(s) M_N(s)`. -/
def mollifierCoefficient (N n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ N), ArithmeticFunction.moebius d

theorem differentiable_dirichletMollifier (N : ℕ) : Differentiable ℂ (dirichletMollifier N) := by
  unfold dirichletMollifier
  fun_prop

@[simp] theorem mollifierCoefficient_zero (N : ℕ) : mollifierCoefficient N 0 = 0 := by
  simp [mollifierCoefficient]

theorem mollifierCoefficient_eq_one_apply {N n : ℕ} (hnN : n ≤ N) :
    mollifierCoefficient N n = if n = 1 then 1 else 0 := by
  have hfilter : n.divisors.filter (fun d => d ≤ N) = n.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact (Nat.divisor_le hd).trans hnN
  rw [mollifierCoefficient, hfilter]
  have hh := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using hh

theorem mollifierCoefficient_eq_zero {N n : ℕ} (hn : n ≠ 1) (hnN : n ≤ N) :
    mollifierCoefficient N n = 0 := by
  rw [mollifierCoefficient_eq_one_apply hnN, if_neg hn]

theorem abs_mollifierCoefficient_le (N n : ℕ) :
    |mollifierCoefficient N n| ≤ (n.divisors.card : ℤ) := by
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ N), |ArithmeticFunction.moebius d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ N), (1 : ℤ) :=
      Finset.sum_le_sum fun _ _ => ArithmeticFunction.abs_moebius_le_one
    _ = ((n.divisors.filter (fun d => d ≤ N)).card : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ N)

theorem dirichletMollifier_critical (N : ℕ) (t : ℝ) :
    dirichletMollifier N ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = criticalMollifier N t := by
  unfold dirichletMollifier criticalMollifier logarithmicPolynomial finiteFrequencySum
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hreal : Real.exp (-(1 / 2 : ℝ) * Real.log n) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have hcomplex : Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) =
      (Real.sqrt n : ℂ)⁻¹ := by
    calc
      _ = (Real.exp (-(1 / 2 : ℝ) * Real.log n) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      _ = _ := by rw [hreal, Complex.ofReal_inv]
  have heq : -((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log n : ℂ) =
      -(1 / 2 : ℂ) * (Real.log n : ℂ) + ((-Real.log n : ℝ) : ℂ) * t * Complex.I := by
    push_cast
    ring
  rw [heq, Complex.exp_add, hcomplex]
  unfold frequencyChar
  ring

/-- The checked critical-line bound for the literal complex-variable mollifier. -/
theorem integral_dirichletMollifier_critical_norm_sq_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ‖dirichletMollifier N ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) ≤
        12 * (T + N) * (1 + Real.log N) := by
  simp_rw [dirichletMollifier_critical]
  exact integral_criticalMollifier_norm_sq_le hN hT

end Sidon
