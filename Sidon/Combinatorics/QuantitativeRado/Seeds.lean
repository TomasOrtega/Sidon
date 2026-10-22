import Sidon.Combinatorics.Deuber.Selection

/-! # Positive boxes of Deuber generators -/

noncomputable section

open scoped BigOperators Classical

namespace Sidon.QuantitativeRado

def seedValue (L R : ℕ) {M : ℕ} (j : Fin M) (u : Fin L) : ℤ :=
  (L : ℤ) * (R : ℤ) ^ j.val + u.val

theorem seedValue_injective (L R : ℕ) {M : ℕ} (j : Fin M) :
    Function.Injective (seedValue L R j) := by
  intro u v huv
  apply Fin.ext
  dsimp [seedValue] at huv
  exact_mod_cast (add_left_cancel huv : (u.val : ℤ) = v.val)

theorem weighted_geometric_sum_le (P R j : ℕ) (hR : 2 * P + 1 ≤ R) :
    (2 * P : ℤ) * (∑ i ∈ Finset.range j, (R : ℤ) ^ i) ≤ (R : ℤ) ^ j - 1 := by
  have hR' : (2 * P + 1 : ℤ) ≤ R := by exact_mod_cast hR
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have hp : 0 ≤ (R : ℤ) ^ j := by positivity
      nlinarith

theorem sum_prefix_pow {M : ℕ} (R : ℤ) (j : Fin M) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin M => i < j), R ^ i.val) =
      ∑ i ∈ Finset.range j.val, R ^ i := by
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i hi i' hi' h
    exact Fin.ext h
  · intro i hi
    have hij := Finset.mem_range.mp hi
    refine ⟨⟨i, hij.trans j.isLt⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  · intro i hi
    rfl

theorem seedValue_bounds {L R M : ℕ} (hR : 1 ≤ R)
    (j : Fin M) (u : Fin L) :
    (L : ℤ) * (R : ℤ) ^ j.val ≤ seedValue L R j u ∧
      seedValue L R j u ≤ 2 * (L : ℤ) * (R : ℤ) ^ j.val := by
  have hu : (0 : ℤ) ≤ u.val := by positivity
  have huL : (u.val : ℤ) ≤ L := by exact_mod_cast Nat.le_of_lt u.isLt
  have hpow : (1 : ℤ) ≤ (R : ℤ) ^ j.val := by
    apply one_le_pow₀
    exact_mod_cast hR
  dsimp [seedValue]
  constructor <;> nlinarith

theorem seedPattern_subset_interval {L R M P C N : ℕ}
    (hL : 0 < L) (hC : 0 < C) (hR : 2 * P + 1 ≤ R)
    (hN : (2 * C + 1) * L * R ^ M ≤ N) (u : Fin M → Fin L) :
    Deuber.pattern P (C : ℤ) (fun j => seedValue L R j (u j)) ⊆
      Set.Icc (1 : ℤ) (N : ℤ) := by
  have hRone : 1 ≤ R := by omega
  have hRone' : (1 : ℤ) ≤ R := by exact_mod_cast hRone
  have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
  have hC' : (1 : ℤ) ≤ C := by exact_mod_cast hC
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨a, rfl⟩ := hj
  let z := fun i : Fin M => seedValue L R i (u i)
  have htail : |∑ i ∈ Finset.univ.filter (fun i : Fin M => i < j),
      (a i : ℤ) * z i| ≤ (L : ℤ) * ((R : ℤ) ^ j.val - 1) := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => i < j), |(a i : ℤ) * z i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => i < j),
          (P : ℤ) * (2 * (L : ℤ) * (R : ℤ) ^ i.val) := by
        apply Finset.sum_le_sum
        intro i hi
        have ha : |(a i : ℤ)| ≤ P := abs_le.mpr (a i).property
        have hz := seedValue_bounds hRone i (u i)
        have hzpos : 0 ≤ z i := by dsimp [z]; linarith [pow_nonneg (by positivity : (0 : ℤ) ≤ R) i.val]
        rw [abs_mul, abs_of_nonneg hzpos]
        exact mul_le_mul ha hz.2 hzpos (by positivity)
      _ = (L : ℤ) * ((2 * P : ℤ) *
          ∑ i ∈ Finset.univ.filter (fun i : Fin M => i < j), (R : ℤ) ^ i.val) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (L : ℤ) * ((R : ℤ) ^ j.val - 1) := by
        rw [sum_prefix_pow]
        exact mul_le_mul_of_nonneg_left (weighted_geometric_sum_le P R j.val hR) (by positivity)
  have hzj := seedValue_bounds hRone j (u j)
  have hpow : (R : ℤ) ^ j.val ≤ (R : ℤ) ^ M :=
    pow_le_pow_right₀ hRone' (Nat.le_of_lt j.isLt)
  have hN' : (2 * (C : ℤ) + 1) * L * (R : ℤ) ^ M ≤ N := by
    exact_mod_cast hN
  have hpowpos : 0 ≤ (R : ℤ) ^ j.val := by positivity
  change (1 : ℤ) ≤ (C : ℤ) * z j + _ ∧ (C : ℤ) * z j + _ ≤ N
  have ht := abs_le.mp htail
  constructor
  · dsimp [z] at *
    nlinarith
  · have hproduct : (C : ℤ) * z j ≤ (C : ℤ) *
        (2 * (L : ℤ) * (R : ℤ) ^ j.val) :=
      mul_le_mul_of_nonneg_left hzj.2 (by positivity)
    have hscale : (2 * (C : ℤ) + 1) * L * (R : ℤ) ^ j.val ≤
        (2 * (C : ℤ) + 1) * L * (R : ℤ) ^ M :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    nlinarith

def seedVector (M L R : ℕ) (u : Fin M → Fin L) : Fin M → ℤ :=
  fun j => seedValue L R j (u j)

theorem seedVector_injective (M L R : ℕ) : Function.Injective (seedVector M L R) := by
  intro u v huv
  funext j
  exact seedValue_injective L R j (congrFun huv j)

def seedBox (M L R : ℕ) : Finset (Fin M → ℤ) :=
  Finset.univ.image (seedVector M L R)

theorem card_seedBox (M L R : ℕ) : (seedBox M L R).card = L ^ M := by
  rw [seedBox, Finset.card_image_of_injective _ (seedVector_injective M L R)]
  simp

theorem div_ge_half {N H : ℕ} (hH : 0 < H) (hN : 2 * H ≤ N) :
    (N : ℝ) / (2 * H) ≤ (N / H : ℕ) := by
  have hdiv : 1 ≤ N / H := (Nat.le_div_iff_mul_le hH).mpr (by omega)
  have hlt := Nat.lt_mul_div_succ N hH
  have hbound : N ≤ 2 * H * (N / H) := by nlinarith
  have hbound' : (N : ℝ) ≤ 2 * H * (N / H : ℕ) := by exact_mod_cast hbound
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * H)).mpr
  nlinarith

theorem exists_positive_seed_box (M P C : ℕ) (hC : 0 < C)
    (N : ℕ) (hN : 2 * ((2 * C + 1) * (4 * P + 2) ^ M) ≤ N) :
    ∃ L : ℕ, 0 < L ∧
      (N : ℝ) / (2 * ((2 * C + 1) * (4 * P + 2) ^ M)) ≤ L ∧
      ∀ u : Fin M → Fin L,
        Deuber.pattern P (C : ℤ) (seedVector M L (4 * P + 2) u) ⊆
          Set.Icc (1 : ℤ) (N : ℤ) := by
  let H := (2 * C + 1) * (4 * P + 2) ^ M
  have hH : 0 < H := by dsimp [H]; positivity
  let L := N / H
  have hL : 0 < L := by
    have h := (Nat.le_div_iff_mul_le hH).mpr (by dsimp [H] at *; omega : 1 * H ≤ N)
    exact h
  refine ⟨L, hL, ?_, ?_⟩
  · simpa only [H, L, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_one, Nat.cast_ofNat] using div_ge_half hH hN
  intro u
  apply seedPattern_subset_interval hL hC (by omega)
  have h := Nat.div_mul_le_self N H
  simpa only [L, H, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end Sidon.QuantitativeRado
