import Sidon.Transference.DensePartition
import Sidon.Transference.SidonMajorant
import Sidon.Transference.IndicatorCounts
import Sidon.Combinatorics.QuantitativeRado.Weighted

/-! # Partition regularity in Fourier-uniform Sidon sets -/

noncomputable section

namespace Sidon

/-- A normalized colour class, extended by zero outside the Sidon set. -/
def sidonColourWeight {r : ℕ} (N : ℕ) (S : Finset ℤ) (χ : ℤ → Fin r) (i : Fin r) (n : ℤ) : ℝ :=
  if χ n = i then sidonMajorant N S n else 0

theorem sidonColourWeight_nonneg {r : ℕ} (N : ℕ) (S : Finset ℤ) (χ : ℤ → Fin r)
    (i : Fin r) (n : ℤ) : 0 ≤ sidonColourWeight N S χ i n := by
  unfold sidonColourWeight
  split_ifs
  · exact sidonMajorant_nonneg _ _ _
  · rfl

theorem sidonColourWeight_le {r : ℕ} (N : ℕ) (S : Finset ℤ) (χ : ℤ → Fin r)
    (i : Fin r) (n : ℤ) : sidonColourWeight N S χ i n ≤ (N : ℝ) / S.card := by
  unfold sidonColourWeight
  split_ifs
  · exact sidonMajorant_le _ _ _
  · positivity

theorem sidonColourWeight_eq_zero {r : ℕ} (N : ℕ) {S : Finset ℤ} (χ : ℤ → Fin r)
    (i : Fin r) {n : ℤ} (hn : n ∉ S) : sidonColourWeight N S χ i n = 0 := by
  unfold sidonColourWeight
  rw [sidonMajorant_eq_zero N hn]
  split_ifs <;> rfl

theorem sum_sidonColourWeight {r : ℕ} (N : ℕ) (S : Finset ℤ) (χ : ℤ → Fin r) (n : ℤ) :
    (∑ i : Fin r, sidonColourWeight N S χ i n) = sidonMajorant N S n := by
  unfold sidonColourWeight
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem sidonColourWeight_scaled_indicator {r : ℕ} (N : ℕ) (S : Finset ℤ) (χ : ℤ → Fin r)
    (i : Fin r) (n : ℤ) : sidonColourWeight N S χ i n =
      ((N : ℝ) / S.card) * if n ∈ S.filter (fun n => χ n = i) then 1 else 0 := by
  by_cases hn : n ∈ S <;> by_cases hi : χ n = i <;>
    simp [sidonColourWeight, sidonMajorant, hn, hi]

theorem normalized_count_lower_bound {N s : ℕ} (hN : 0 < N) (hs : 1 ≤ s)
    {m κ C : ℝ} (hm : 0 < m)
    (hcount : κ * (N : ℝ) ^ (s - 1) ≤ ((N : ℝ) / m) ^ s * C) :
    κ * m ^ s / N ≤ C := by
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hscaled := mul_le_mul_of_nonneg_left hcount (pow_nonneg hm.le s)
  have heq : m ^ s * (((N : ℝ) / m) ^ s * C) = (N : ℝ) ^ s * C := by
    rw [div_pow]
    field_simp
  rw [heq] at hscaled
  have hpow : (N : ℝ) ^ s = (N : ℝ) ^ (s - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel hs]
  rw [hpow] at hscaled
  have hfinal : κ * m ^ s ≤ (N : ℝ) * C := by
    apply (mul_le_mul_iff_right₀ (pow_pos hN' (s - 1))).mp
    convert hscaled using 1 <;> ring
  exact (div_le_iff₀ hN').mpr (by simpa only [mul_comm] using hfinal)

/-- All transference parameters are chosen before the Sidon set and its colouring. -/
theorem sidon_partition_regularity_of_majorant_uniformity {s r : ℕ} (hs : 5 ≤ s) (hr : 0 < r)
    (c : Fin s → ℤ) (hc : ∀ i, c i ≠ 0) (I : Finset (Fin s))
    (hIne : I.Nonempty) (hI : ∑ i ∈ I, c i = 0) :
    ∃ N₀ : ℕ, ∃ η κ : ℝ, 0 < η ∧ 0 < κ ∧
      ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ S : Finset ℤ,
        IsSidonSet (S : Set ℤ) → S ⊆ interval N → Real.sqrt N / 100 ≤ S.card →
        ‖weightedFourier (interval N) (fun n => sidonMajorant N S n - 1)‖ ≤ η * N →
        ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
          κ * (S.card : ℝ) ^ s / N ≤
            (linearSolutions (S.filter (fun n => χ n = colour)) c).card := by
  classical
  obtain ⟨N₀, δ, hδ, hweighted⟩ :=
    QuantitativeRado.exists_many_weighted_linearSolutions (by omega) hr c hc I hIne hI
  have hs' : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  let ε := min 1 (δ / (80000 * (s : ℝ)))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hδ (by positivity))
  have hε₁ : ε ≤ 1 := min_le_left _ _
  obtain ⟨η, hη, hmodel⟩ := colouring_dense_partition_model_interval r hr hε hε₁
  refine ⟨N₀, η, δ / 2, hη, by positivity, fun N hNN hN S hS hSN hm hν χ => ?_⟩
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm' : (0 : ℝ) < S.card := (by positivity : 0 < Real.sqrt N / 100).trans_le hm
  have hmnat : 0 < S.card := by exact_mod_cast hm'
  let f : Fin r → ℤ → ℝ := sidonColourWeight N S χ
  obtain ⟨g, hg0, hg1, hgSum, _, hfg⟩ := hmodel N hN (sidonMajorant N S) f
    (fun n _ => sidonMajorant_nonneg N S n)
    (fun i n _ => sidonColourWeight_nonneg N S χ i n)
    (fun n _ => sum_sidonColourWeight N S χ n) (sum_sidonMajorant hmnat hSN) hν
  obtain ⟨j, hj⟩ := hweighted N hNN g (fun i n _ => hg0 i n) hgSum
  have htransfer := sidon_counting_transfer hN hs hS hSN hm c hc (f j) (g j)
    (sidonColourWeight_nonneg N S χ j) (sidonColourWeight_le N S χ j)
    (fun n _ hn => sidonColourWeight_eq_zero N χ j hn) (hg0 j) (hg1 j)
  have hεbound : 40000 * (s : ℝ) * ε ≤ δ / 2 := by
    have he := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (δ / (80000 * (s : ℝ))))
      (by positivity : 0 ≤ 40000 * (s : ℝ))
    change 40000 * (s : ℝ) * ε ≤ 40000 * (s : ℝ) * (δ / (80000 * (s : ℝ))) at he
    apply he.trans
    apply le_of_eq
    field_simp
    ring
  have herror : |weightedSolutionCount (interval N) c (fun _ => f j) -
      weightedSolutionCount (interval N) c (fun _ => g j)| ≤
      (δ / 2) * (N : ℝ) ^ (s - 1) := by
    apply htransfer.trans
    calc
      _ ≤ 40000 * (s : ℝ) * (N : ℝ) ^ (s - 2) * (ε * N) :=
        mul_le_mul_of_nonneg_left (hfg j) (by positivity)
      _ = (40000 * (s : ℝ) * ε) * (N : ℝ) ^ (s - 1) := by
        have hexp : s - 2 + 1 = s - 1 := by omega
        rw [← hexp, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hεbound (by positivity)
  have hcount : (δ / 2) * (N : ℝ) ^ (s - 1) ≤
      weightedSolutionCount (interval N) c (fun _ => f j) := by
    have hlow := (abs_le.mp herror).1
    linarith
  have heq : weightedSolutionCount (interval N) c (fun _ => f j) =
      ((N : ℝ) / S.card) ^ s *
        (linearSolutions (S.filter (fun n => χ n = j)) c).card := by
    change weightedSolutionCount (interval N) c (fun _ => sidonColourWeight N S χ j) = _
    have hf : sidonColourWeight N S χ j = fun n =>
        ((N : ℝ) / S.card) * if n ∈ S.filter (fun n => χ n = j) then 1 else 0 :=
      funext (sidonColourWeight_scaled_indicator N S χ j)
    rw [hf]
    simpa only [Fintype.card_fin] using weightedSolutionCount_scaled_indicator (interval N)
      (S.filter (fun n => χ n = j)) ((Finset.filter_subset _ _).trans hSN) c ((N : ℝ) / S.card)
  rw [heq] at hcount
  exact ⟨j, normalized_count_lower_bound hN (by omega) hm' hcount⟩


/-- Theorem 1.15 in relative-cardinality form. -/
theorem sidon_partition_regularity_relative {s r : ℕ} (hs : 5 ≤ s) (hr : 0 < r)
    (c : Fin s → ℤ) (hc : ∀ i, c i ≠ 0) (I : Finset (Fin s))
    (hIne : I.Nonempty) (hI : ∑ i ∈ I, c i = 0) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℤ,
        IsSidonSet (S : Set ℤ) → S ⊆ interval N → sidonDeviation N S ≤ γ →
        ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
          κ * (S.card : ℝ) ^ s / N ≤
            (linearSolutions (S.filter (fun n => χ n = colour)) c).card := by
  obtain ⟨M, η, κ, hη, hκ, hmain⟩ :=
    sidon_partition_regularity_of_majorant_uniformity hs hr c hc I hIne hI
  obtain ⟨L, hL, γ, hγ, hγhalf, hthreshold⟩ := exists_sidon_uniformity_threshold hη
  refine ⟨max M L, hL.trans (le_max_right _ _), γ, κ, hγ, hκ,
    fun N hN S hS hSN hdev χ => ?_⟩
  have hNL : L ≤ N := (le_max_right M L).trans hN
  have hNpos : 0 < N := by omega
  have hmhalf := sqrt_half_le_card_of_deviation_le_half hNpos S (hdev.trans hγhalf)
  have hmhundred : Real.sqrt N / 100 ≤ S.card := by
    linarith [Real.sqrt_nonneg (N : ℝ)]
  apply hmain N ((le_max_left M L).trans hN) hNpos S hS hSN hmhundred ?_ χ
  apply (sidonMajorant_fourier_uniformity hNpos hS hSN hmhalf).trans
  have ht := mul_le_mul_of_nonneg_left (hthreshold N hNL S hdev) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  convert ht using 1 <;> ring

/-- Theorem 1.15: every finite colouring of an extremal Sidon set has many solutions. -/
theorem sidon_partition_regularity {s r : ℕ} (hs : 5 ≤ s) (hr : 0 < r)
    (c : Fin s → ℤ) (hc : ∀ i, c i ≠ 0) (I : Finset (Fin s))
    (hIne : I.Nonempty) (hI : ∑ i ∈ I, c i = 0) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ γ κ : ℝ, 0 < γ ∧ 0 < κ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℤ,
        IsSidonSet (S : Set ℤ) → S ⊆ interval N →
        |(S.card : ℝ) - Real.sqrt N| ≤ γ * Real.sqrt N →
        ∀ χ : ℤ → Fin r, ∃ colour : Fin r,
          κ * (S.card : ℝ) ^ s / N ≤
            (linearSolutions (S.filter (fun n => χ n = colour)) c).card := by
  obtain ⟨N₀, hN₀, γ, κ, hγ, hκ, hmain⟩ :=
    sidon_partition_regularity_relative hs hr c hc I hIne hI
  refine ⟨N₀, hN₀, γ, κ, hγ, hκ, fun N hN S hS hSN hdev => ?_⟩
  apply hmain N hN S hS hSN
  have hNpos : 0 < N := by omega
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  unfold sidonDeviation
  have heq : (S.card : ℝ) / Real.sqrt N - 1 =
      ((S.card : ℝ) - Real.sqrt N) / Real.sqrt N := by field_simp
  rw [heq, abs_div, abs_of_pos hsqrt]
  exact (div_le_iff₀ hsqrt).mpr hdev

end Sidon
