import Sidon.Transference.DenseModelInterval

/-! # Completing simultaneous models to a partition -/

noncomputable section

namespace Sidon

variable {N r : ℕ}

theorem weightedFourier_add (A : Finset ℤ) (f g : ℤ → ℝ) :
    weightedFourier A (fun n => f n + g n) = weightedFourier A f + weightedFourier A g := by
  ext α
  simp only [weightedFourier_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib,
    ContinuousMap.add_apply]

theorem weightedFourier_sub_function (A : Finset ℤ) (f g : ℤ → ℝ) :
    weightedFourier A (fun n => f n - g n) = weightedFourier A f - weightedFourier A g := by
  ext α
  simp only [weightedFourier_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ContinuousMap.sub_apply]

theorem norm_weightedFourier_le_sum_abs (A : Finset ℤ) (f : ℤ → ℝ) :
    ‖weightedFourier A f‖ ≤ ∑ n ∈ A, |f n| := by
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun n _ => abs_nonneg (f n)))).mpr
  exact norm_weightedFourier_apply_le A f

theorem abs_sum_le_norm_weightedFourier (A : Finset ℤ) (f : ℤ → ℝ) :
    |∑ n ∈ A, f n| ≤ ‖weightedFourier A f‖ := by
  have h := (weightedFourier A f).norm_coe_le_norm 0
  simp only [weightedFourier_apply, fourier_eval_zero, mul_one, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- A small total deficit can be added to one colour. -/
theorem complete_dense_model (hr : 0 < r) {ε : ℝ} (hε : 0 ≤ ε)
    (f g : Fin r → ℤ → ℝ)
    (hg0 : ∀ i n, 0 ≤ g i n) (hgSum : ∀ n, ∑ i : Fin r, g i n ≤ 1)
    (hgs : ∀ i n, n ∉ interval N → g i n = 0)
    (hfmass : (∑ n ∈ interval N, ∑ i : Fin r, f i n) = (N : ℝ))
    (hfg : ∀ i, ‖weightedFourier (interval N) (fun n => f i n - g i n)‖ ≤ ε * N) :
    ∃ h : Fin r → ℤ → ℝ,
      (∀ i n, 0 ≤ h i n) ∧ (∀ i n, h i n ≤ 1) ∧
      (∀ n ∈ interval N, ∑ i : Fin r, h i n = 1) ∧
      (∀ i n, n ∉ interval N → h i n = 0) ∧
      ∀ i, ‖weightedFourier (interval N) (fun n => f i n - h i n)‖ ≤
        ((r : ℝ) + 1) * ε * N := by
  let j : Fin r := ⟨0, hr⟩
  let D : ℤ → ℝ := fun n => if n ∈ interval N then 1 - ∑ i : Fin r, g i n else 0
  have hD0 (n : ℤ) : 0 ≤ D n := by
    dsimp [D]
    split_ifs
    · exact sub_nonneg.mpr (hgSum n)
    · rfl
  have hDsum : (∑ n ∈ interval N, D n) =
      ∑ i : Fin r, ∑ n ∈ interval N, (f i n - g i n) := by
    have hD : (∑ n ∈ interval N, D n) =
        (N : ℝ) - ∑ n ∈ interval N, ∑ i : Fin r, g i n := by
      calc
        _ = ∑ n ∈ interval N, (1 - ∑ i : Fin r, g i n) :=
          Finset.sum_congr rfl (fun n hn => if_pos hn)
        _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_one, card_interval]
    rw [hD, ← hfmass]
    rw [← Finset.sum_sub_distrib, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_sub_distrib]
  have hDmass : (∑ n ∈ interval N, D n) ≤ (r : ℝ) * ε * N := by
    rw [hDsum]
    calc
      _ ≤ ∑ _i : Fin r, ε * (N : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_abs_self _).trans ((abs_sum_le_norm_weightedFourier _ _).trans (hfg i))
      _ = _ := by simp; ring
  have hDnorm : ‖weightedFourier (interval N) D‖ ≤ (r : ℝ) * ε * N := by
    apply (norm_weightedFourier_le_sum_abs _ _).trans
    simpa only [abs_of_nonneg (hD0 _)] using hDmass
  let h : Fin r → ℤ → ℝ := fun i n => g i n + if i = j then D n else 0
  have hh0 (i : Fin r) (n : ℤ) : 0 ≤ h i n := by
    dsimp [h]
    split_ifs <;> linarith [hg0 i n, hD0 n]
  have hhSum (n : ℤ) : (∑ i : Fin r, h i n) ≤ 1 := by
    dsimp [h]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hn : n ∈ interval N
    · dsimp [D]
      rw [if_pos hn]
      linarith
    · have hgzero : (∑ i : Fin r, g i n) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact hgs i n hn
      rw [hgzero]
      dsimp [D]
      rw [if_neg hn]
      norm_num
  refine ⟨h, hh0, fun i n => ?_, fun n hn => ?_, fun i n hn => ?_, fun i => ?_⟩
  · exact (Finset.single_le_sum (fun k _ => hh0 k n) (Finset.mem_univ i)).trans (hhSum n)
  · dsimp [h]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp [D]
    rw [if_pos hn]
    ring
  · dsimp [h, D]
    rw [hgs i n hn, if_neg hn]
    split_ifs <;> simp only [add_zero]
  · by_cases hij : i = j
    · have heq : (fun n => f i n - h i n) = fun n => (f i n - g i n) - D n := by
        funext n
        dsimp [h]
        rw [if_pos hij]
        ring
      rw [heq, weightedFourier_sub_function]
      calc
        _ ≤ ‖weightedFourier (interval N) (fun n => f i n - g i n)‖ +
            ‖weightedFourier (interval N) D‖ := norm_sub_le _ _
        _ ≤ ε * N + (r : ℝ) * ε * N := add_le_add (hfg i) hDnorm
        _ = _ := by ring
    · have heq : (fun n => f i n - h i n) = fun n => f i n - g i n := by
        funext n
        dsimp [h]
        rw [if_neg hij, add_zero]
      rw [heq]
      apply (hfg i).trans
      have := mul_nonneg (Nat.cast_nonneg r) (mul_nonneg hε (Nat.cast_nonneg N))
      nlinarith

/-- The dense model may preserve a full partition of a normalized majorant. -/
theorem colouring_dense_partition_model_interval (r : ℕ) (hr : 0 < r) {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N : ℕ), 0 < N → ∀ (ν : ℤ → ℝ) (f : Fin r → ℤ → ℝ),
      (∀ n ∈ interval N, 0 ≤ ν n) → (∀ i, ∀ n ∈ interval N, 0 ≤ f i n) →
      (∀ n ∈ interval N, ∑ i : Fin r, f i n = ν n) →
      (∑ n ∈ interval N, ν n) = (N : ℝ) →
      ‖weightedFourier (interval N) (fun n => ν n - 1)‖ ≤ η * N →
      ∃ g : Fin r → ℤ → ℝ,
        (∀ i n, 0 ≤ g i n) ∧ (∀ i n, g i n ≤ 1) ∧
        (∀ n ∈ interval N, ∑ i : Fin r, g i n = 1) ∧
        (∀ i n, n ∉ interval N → g i n = 0) ∧
        ∀ i, ‖weightedFourier (interval N) (fun n => f i n - g i n)‖ ≤ ε * N := by
  let τ := ε / ((r : ℝ) + 1)
  have hr' : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hτ : 0 < τ := div_pos hε (by positivity)
  have hτ₁ : τ ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) + 1)).mpr
    linarith
  obtain ⟨η, hη, hmodel⟩ := colouring_dense_model_interval r hτ hτ₁
  refine ⟨η, hη, fun N hN ν f hν hf hνf hmass herror => ?_⟩
  obtain ⟨g, hg0, _, hgSum, hgs, hfg⟩ := hmodel N hN ν f hν hf
    (fun n hn => (hνf n hn).le) herror
  have hfmass : (∑ n ∈ interval N, ∑ i : Fin r, f i n) = (N : ℝ) := by
    rw [Finset.sum_congr rfl hνf, hmass]
  obtain ⟨h, hh0, hh1, hhSum, hhs, hfh⟩ := complete_dense_model hr hτ.le f g hg0 hgSum hgs hfmass hfg
  refine ⟨h, hh0, hh1, hhSum, hhs, fun i => ?_⟩
  convert hfh i using 1
  dsimp [τ]
  field_simp

end Sidon
