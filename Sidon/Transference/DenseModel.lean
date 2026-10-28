module

public import Sidon.Transference.DenseGeometry

@[expose] public section

/-! # The colouring dense-model theorem -/

noncomputable section

open scoped Pointwise

namespace Sidon
namespace FourierSpace

variable {N r : ℕ}

@[simp] theorem tuplePairing_zero_right (φ : ColourTuple N r) : tuplePairing φ 0 = 0 := by
  unfold tuplePairing
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]

@[simp] theorem tuplePairing_smul_right (φ u : ColourTuple N r) (a : ℝ) :
    tuplePairing φ (a • u) = a * tuplePairing φ u := by
  unfold tuplePairing
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]

@[simp] theorem tuplePairing_smul_left (φ u : ColourTuple N r) (a : ℝ) :
    tuplePairing (a • φ) u = a * tuplePairing φ u := by
  unfold tuplePairing
  simp only [Pi.smul_apply, pairing_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]

@[simp] theorem tuplePairing_single (φ : ColourTuple N r) (i : Fin r) (w : FourierSpace N) :
    tuplePairing φ (Pi.single i w) = pairing (φ i) w := by
  unfold tuplePairing
  simp only [Pi.single_apply, apply_ite, map_zero]
  simp

theorem dualNorm_le_of_separator {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T)
    {φ : ColourTuple N r}
    (hsep : ∀ h : ColourTuple N r, ‖h‖ ≤ q → tuplePairing φ h < T) (i : Fin r) :
    dualNorm (φ i) ≤ T / q := by
  apply (pairing (φ i)).opNorm_le_of_unit_norm (div_nonneg hT hq.le)
  intro w hw
  have hball : ‖q • (Pi.single i w : ColourTuple N r)‖ ≤ q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, Pi.norm_single, hw, mul_one]
  have hp := hsep (q • (Pi.single i w : ColourTuple N r)) hball
  have hn := hsep ((-q) • (Pi.single i w : ColourTuple N r)) (by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hq, Pi.norm_single, hw, mul_one])
  simp only [tuplePairing_smul_right, tuplePairing_single] at hp hn
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hq).mpr
  rw [mul_comm, ← abs_of_pos hq, ← abs_mul]
  apply (abs_le).mpr
  constructor <;> nlinarith

theorem tuple_norm_error_le_of_scaled_decomposition {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {f g h : ColourTuple N r} (hg : g ∈ models N r)
    (hh : ‖h‖ ≤ ε * (N : ℝ) / 4)
    (heq : (1 + ε / 2)⁻¹ • f = g + h) : ‖f - g‖ ≤ ε * (N : ℝ) := by
  let a := 1 + ε / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have heq' : f - g = (a - 1) • g + a • h := by
    have heq' := congrArg (fun u : ColourTuple N r => a • u) heq
    have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    change a • (a⁻¹ • f) = a • (g + h) at heq'
    rw [smul_smul, haa, one_smul, smul_add] at heq'
    rw [heq']
    module
  rw [heq']
  calc
    _ ≤ ‖(a - 1) • g‖ + ‖a • h‖ := norm_add_le _ _
    _ = (ε / 2) * ‖g‖ + a * ‖h‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by dsimp [a]; linarith), abs_of_pos ha]
      dsimp [a]
      ring
    _ ≤ (ε / 2) * N + a * (ε * N / 4) :=
      add_le_add (mul_le_mul_of_nonneg_left (models_norm_le hg) (by positivity))
        (mul_le_mul_of_nonneg_left hh ha.le)
    _ ≤ ε * N := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hprod : ε * ε * (N : ℝ) ≤ ε * N := by
        simpa only [mul_assoc] using mul_le_of_le_one_left (mul_nonneg hε.le hN) hε₁
      dsimp [a]
      nlinarith

/-- A failed model supplies a normalized real separating tuple. -/
theorem exists_normalized_separator (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (f : ColourTuple N r)
    (hfail : ¬∃ g ∈ models N r, ∀ i, ‖f i - g i‖ ≤ ε * N) :
    ∃ φ : ColourTuple N r,
      tuplePairing φ f = (1 + ε / 2) * N ∧
      ∀ g ∈ models N r, ∀ h : ColourTuple N r, ‖h‖ ≤ ε * N / 4 →
        tuplePairing φ (g + h) < (N : ℝ) := by
  let a := 1 + ε / 2
  let q := ε * (N : ℝ) / 4
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha : 0 < a := by dsimp [a]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hv : a⁻¹ • f ∉ models N r + Metric.closedBall 0 q := by
    rintro ⟨g, hg, h, hh, heq⟩
    apply hfail
    refine ⟨g, hg, fun i => ?_⟩
    have he := tuple_norm_error_le_of_scaled_decomposition hε hε₁ hg
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hh) heq.symm
    exact (norm_le_pi_norm (f - g) i).trans he
  obtain ⟨ψ, hψ⟩ := separate_models_thickening (a⁻¹ • f) hv
  have hA : 0 < tuplePairing ψ (a⁻¹ • f) := by
    simpa only [zero_add, tuplePairing_zero_right] using
      hψ 0 zero_mem_models 0 (by simpa using hq.le)
  let A := tuplePairing ψ (a⁻¹ • f)
  have hAne : A ≠ 0 := ne_of_gt hA
  let φ := ((N : ℝ) / A) • ψ
  have hc : 0 < (N : ℝ) / A := div_pos hN' hA
  refine ⟨φ, ?_, fun g hg h hh => ?_⟩
  · dsimp only [φ]
    rw [tuplePairing_smul_left]
    have hrel : A = a⁻¹ * tuplePairing ψ f := tuplePairing_smul_right ψ f a⁻¹
    have hAf : tuplePairing ψ f = a * A := by rw [hrel]; field_simp
    rw [hAf]
    dsimp [a]
    field_simp [hAne]
  · have ht := mul_lt_mul_of_pos_left (hψ g hg h hh) hc
    rw [← tuplePairing_smul_left] at ht
    change tuplePairing φ (g + h) < (N : ℝ) / A * A at ht
    simpa only [div_mul_cancel₀ _ hAne] using ht

/-- The separator detects a positive discrepancy against its positive maximum. -/
theorem separator_max_discrepancy {ε : ℝ}
    (ν : FourierSpace N) (f φ : ColourTuple N r)
    (hf : ∀ i x, 0 ≤ f i x) (hνf : ∀ x, ∑ i : Fin r, f i x ≤ ν x)
    (hφf : tuplePairing φ f = (1 + ε / 2) * N)
    (hsep : ∀ g ∈ models N r, tuplePairing φ g < (N : ℝ)) :
    ε * N / 2 < pairing (fun x => positiveMax (fun i => φ i x)) (ν - 1) := by
  obtain ⟨g, hg, hmax⟩ := exists_models_pairing_positiveMax φ
  have hM : (∑ x : Fin N, positiveMax (fun i => φ i x)) < (N : ℝ) := by
    rw [← hmax]
    exact hsep g hg
  have hbound : tuplePairing φ f ≤ ∑ x : Fin N, ν x * positiveMax (fun i => φ i x) := by
    rw [tuplePairing_eq_sum]
    apply Finset.sum_le_sum
    intro x _
    calc
      _ ≤ ∑ i : Fin r, f i x * positiveMax (fun i => φ i x) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (le_positiveMax (fun i => φ i x) i) (hf i x)
      _ = (∑ i : Fin r, f i x) * positiveMax (fun i => φ i x) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hνf x) (positiveMax_nonneg _)
  have heq : pairing (fun x => positiveMax (fun i => φ i x)) (ν - 1) =
      (∑ x : Fin N, ν x * positiveMax (fun i => φ i x)) -
      ∑ x : Fin N, positiveMax (fun i => φ i x) := by
    change (∑ x : Fin N, (ν x - 1) * _) = _
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [heq, hφf] at *
  linarith


theorem pairing_approximation_error (ρ Q M : FourierSpace N) {τ : ℝ}
    (happrox : ∀ x, |Q x - M x| ≤ τ) :
    |pairing Q ρ - pairing M ρ| ≤ τ * ∑ x : Fin N, |ρ x| := by
  simp only [pairing_apply, ← Finset.sum_sub_distrib]
  calc
    _ = |∑ x : Fin N, ρ x * (Q x - M x)| := by congr 1; apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ x : Fin N, |ρ x * (Q x - M x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : Fin N, |ρ x| * τ := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (happrox x) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem sum_le_two_mul_of_norm_sub_one_le (ν : FourierSpace N)
    (hν : ‖ν - 1‖ ≤ (N : ℝ)) : ∑ x : Fin N, ν x ≤ 2 * (N : ℝ) := by
  let ν' : Fin N → ℝ := ν
  have h := abs_sum_le_norm (ν - 1)
  change |∑ x : Fin N, (ν' x - 1)| ≤ ‖ν - 1‖ at h
  rw [Finset.sum_sub_distrib] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have h' := (le_abs_self ((∑ x : Fin N, ν x) - N)).trans (h.trans hν)
  linarith

theorem sum_abs_sub_one_le_three_mul (ν : FourierSpace N) (hν : ∀ x, 0 ≤ ν x)
    (hmass : ∑ x : Fin N, ν x ≤ 2 * (N : ℝ)) :
    ∑ x : Fin N, |ν x - 1| ≤ 3 * (N : ℝ) := by
  let ν' : Fin N → ℝ := ν
  change (∑ x : Fin N, |ν' x - 1|) ≤ 3 * (N : ℝ)
  calc
    _ ≤ ∑ x : Fin N, (ν' x + 1) := by
      apply Finset.sum_le_sum
      intro x _
      exact (abs_sub (ν x) 1).trans (by rw [abs_of_nonneg (hν x), abs_one])
    _ = (∑ x : Fin N, ν' x) + N := by simp only [Finset.sum_add_distrib]; simp
    _ ≤ _ := by linarith

/-- Appendix C: one Fourier-uniform majorant admits simultaneous bounded colour models. -/
theorem colouring_dense_model (r : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N : ℕ), 0 < N → ∀ (ν : FourierSpace N)
      (f : ColourTuple N r), (∀ x, 0 ≤ ν x) → (∀ i x, 0 ≤ f i x) →
      (∀ x, ∑ i : Fin r, f i x ≤ ν x) → ‖ν - 1‖ ≤ η * N →
      ∃ g ∈ models N r, ∀ i, ‖f i - g i‖ ≤ ε * N := by
  let L := 4 / ε
  have hL : 1 ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ hε).mpr
    linarith
  obtain ⟨P, hP⟩ := exists_polynomial_positiveMax (ι := Fin r) L
    (by positivity : 0 < ε / 100)
  obtain ⟨B, hB, hBP⟩ := exists_dualNorm_aeval_bound P hL
  have hBpos : 0 < B := by linarith
  let η := min 1 (ε / (4 * B))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  refine ⟨η, hη, fun N hN ν f hν hf hνf herror => ?_⟩
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hη₁ : η ≤ 1 := min_le_left _ _
  have herrorN : ‖ν - 1‖ ≤ (N : ℝ) := herror.trans (by nlinarith)
  have hmass := sum_le_two_mul_of_norm_sub_one_le ν herrorN
  have habsmass := sum_abs_sub_one_le_three_mul ν hν hmass
  by_contra hfail
  obtain ⟨φ, hφf, hsep⟩ := exists_normalized_separator hN hε hε₁ f hfail
  have hdual (i : Fin r) : dualNorm (φ i) ≤ L := by
    have ht : dualNorm (φ i) ≤ (N : ℝ) / (ε * N / 4) := by
      apply dualNorm_le_of_separator (by positivity) hN'.le (fun h hh => ?_) i
      simpa only [zero_add] using hsep 0 zero_mem_models h hh
    convert ht using 1
    dsimp [L]
    field_simp
  let M : FourierSpace N := fun x => positiveMax (fun i => φ i x)
  have hgap : ε * N / 2 < pairing M (ν - 1) := by
    apply separator_max_discrepancy ν f φ hf hνf hφf
    intro g hg
    simpa only [add_zero] using hsep g hg 0 (by simpa using
      (show 0 ≤ ε * (N : ℝ) / 4 by positivity))
  let Q : FourierSpace N := MvPolynomial.aeval φ P
  have happrox (x : Fin N) : |Q x - M x| ≤ ε / 100 := by
    rw [show Q x = MvPolynomial.aeval (fun i => φ i x) P from aeval_apply φ P x]
    exact (hP (fun i => φ i x) (fun i =>
      (abs_apply_le_dualNorm (φ i) x).trans (hdual i))).le
  have herr := pairing_approximation_error (ν - 1) Q M happrox
  change |pairing Q (ν - 1) - pairing M (ν - 1)| ≤
    (ε / 100) * ∑ x : Fin N, |ν x - 1| at herr
  have herr' : |pairing Q (ν - 1) - pairing M (ν - 1)| ≤ (ε / 100) * (3 * N) :=
    herr.trans (mul_le_mul_of_nonneg_left habsmass (by positivity))
  have hgapQ : ε * N / 4 < pairing Q (ν - 1) := by
    have := neg_le_abs (pairing Q (ν - 1) - pairing M (ν - 1))
    nlinarith [mul_pos hε hN']
  have hboundQ : dualNorm Q ≤ B := hBP N φ hdual
  have hpair : pairing Q (ν - 1) ≤ ‖ν - 1‖ * B := by
    exact (le_abs_self _).trans ((abs_pairing_le (ν - 1) Q).trans
      (mul_le_mul_of_nonneg_left hboundQ (norm_nonneg _)))
  have hsmall : η * B ≤ ε / 4 := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (ε / (4 * B))) hBpos.le
    dsimp only [η]
    calc
      _ ≤ ε / (4 * B) * B := this
      _ = ε / 4 := by field_simp
  have hfinal : ‖ν - 1‖ * B ≤ ε * N / 4 := by
    calc
      _ ≤ (η * N) * B := mul_le_mul_of_nonneg_right herror hBpos.le
      _ = (η * B) * N := by ring
      _ ≤ (ε / 4) * N := mul_le_mul_of_nonneg_right hsmall hN'.le
      _ = _ := by ring
  linarith

end FourierSpace
end Sidon
