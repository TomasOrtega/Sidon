module

public import Sidon.Analysis.DiscreteFejer

@[expose] public section

/-! # The triangular closed form of the discrete Fejér kernel -/

namespace Sidon

theorem fejerWeight_natCast (H k : ℕ) :
    fejerWeight H (k : ℤ) = ((H - k : ℕ) : ℝ) * ((H : ℝ) ^ 2)⁻¹ := by
  classical
  rw [fejerWeight_apply]
  have hinner (u : ℕ) :
      (∑ v ∈ Finset.range H, if (v : ℤ) - u = k then ((H : ℝ) ^ 2)⁻¹ else 0) =
        if u + k < H then ((H : ℝ) ^ 2)⁻¹ else 0 := by
    have heq (v : ℕ) : ((v : ℤ) - u = k) ↔ v = u + k := by omega
    simp only [heq, Finset.sum_ite_eq', Finset.mem_range]
  simp_rw [hinner]
  have hfilter : (Finset.range H).filter (fun u => u + k < H) = Finset.range (H - k) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem fejerWeight_abs (H : ℕ) (h : ℤ) : fejerWeight H |h| = fejerWeight H h := by
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]
  · rw [abs_of_nonpos hh, fejerWeight_neg]

theorem fejerWeight_eq_nat_sub (H : ℕ) (h : ℤ) :
    fejerWeight H h = ((H - h.natAbs : ℕ) : ℝ) / (H : ℝ) ^ 2 := by
  rw [← fejerWeight_abs, ← Int.natCast_natAbs, fejerWeight_natCast, div_eq_mul_inv]

end Sidon
