import Sidon.Transference.DenseModel
import Sidon.Transference.RestrictionMoments

/-! # The dense model on integer intervals -/

noncomputable section

namespace Sidon

variable {N : ℕ}

theorem sum_interval_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M) :
    (∑ n ∈ interval N, F n) = ∑ i : Fin N, F ((i.val : ℤ) + 1) := by
  symm
  apply Finset.sum_bij (fun i _ => (i.val : ℤ) + 1)
  · intro i _
    exact mem_interval.mpr ⟨by omega, by have := i.isLt; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro n hn
    have hn' := mem_interval.mp hn
    let i : Fin N := ⟨(n - 1).toNat, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp [i]
    omega
  · intro i _
    rfl

namespace FourierSpace

def ofFunction (N : ℕ) (f : ℤ → ℝ) : FourierSpace N := fun i => f ((i.val : ℤ) + 1)

def zeroExtend (f : FourierSpace N) (n : ℤ) : ℝ :=
  if hn : n ∈ interval N then f ⟨(n - 1).toNat, by have := mem_interval.mp hn; omega⟩ else 0

theorem zeroExtend_eq_zero (f : FourierSpace N) {n : ℤ} (hn : n ∉ interval N) :
    zeroExtend f n = 0 := dif_neg hn

@[simp] theorem zeroExtend_apply (f : FourierSpace N) (i : Fin N) :
    zeroExtend f ((i.val : ℤ) + 1) = f i := by
  have hi : (i.val : ℤ) + 1 ∈ interval N :=
    mem_interval.mpr ⟨by omega, by have := i.isLt; omega⟩
  rw [zeroExtend, dif_pos hi]
  congr 1
  apply Fin.ext
  simp

@[simp] theorem ofFunction_zeroExtend (f : FourierSpace N) :
    ofFunction N (zeroExtend f) = f := by
  funext i
  exact zeroExtend_apply f i

theorem transform_ofFunction (N : ℕ) (f : ℤ → ℝ) :
    transform (ofFunction N f) = weightedFourier (interval N) f := by
  ext α
  rw [transform_apply, weightedFourier_apply, sum_interval_eq_sum_fin]
  rfl

theorem norm_ofFunction (N : ℕ) (f : ℤ → ℝ) :
    ‖ofFunction N f‖ = ‖weightedFourier (interval N) f‖ := by
  rw [norm_eq, transform_ofFunction]

theorem zeroExtend_nonneg {f : FourierSpace N} (hf : ∀ i, 0 ≤ f i) (n : ℤ) :
    0 ≤ zeroExtend f n := by
  unfold zeroExtend
  split_ifs
  · exact hf _
  · rfl

theorem zeroExtend_le_one {f : FourierSpace N} (hf : ∀ i, f i ≤ 1) (n : ℤ) :
    zeroExtend f n ≤ 1 := by
  unfold zeroExtend
  split_ifs
  · exact hf _
  · norm_num

theorem sum_zeroExtend_le_one {r : ℕ} {g : ColourTuple N r} (hg : g ∈ models N r) (n : ℤ) :
    (∑ i : Fin r, zeroExtend (g i) n) ≤ 1 := by
  by_cases hn : n ∈ interval N
  · simp only [zeroExtend, dif_pos hn]
    exact hg.2 _
  · simp only [zeroExtend_eq_zero _ hn, Finset.sum_const_zero]
    norm_num

end FourierSpace

/-- Simultaneous nonnegative bounded models, using the paper's integer Fourier convention. -/
theorem colouring_dense_model_interval (r : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N : ℕ), 0 < N → ∀ (ν : ℤ → ℝ) (f : Fin r → ℤ → ℝ),
      (∀ n ∈ interval N, 0 ≤ ν n) → (∀ i, ∀ n ∈ interval N, 0 ≤ f i n) →
      (∀ n ∈ interval N, ∑ i : Fin r, f i n ≤ ν n) →
      ‖weightedFourier (interval N) (fun n => ν n - 1)‖ ≤ η * N →
      ∃ g : Fin r → ℤ → ℝ,
        (∀ i n, 0 ≤ g i n) ∧ (∀ i n, g i n ≤ 1) ∧
        (∀ n, ∑ i : Fin r, g i n ≤ 1) ∧
        (∀ i n, n ∉ interval N → g i n = 0) ∧
        ∀ i, ‖weightedFourier (interval N) (fun n => f i n - g i n)‖ ≤ ε * N := by
  obtain ⟨η, hη, hmodel⟩ := FourierSpace.colouring_dense_model r hε hε₁
  refine ⟨η, hη, fun N hN ν f hν hf hνf herror => ?_⟩
  have hmem (i : Fin N) : (i.val : ℤ) + 1 ∈ interval N :=
    mem_interval.mpr ⟨by omega, by have := i.isLt; omega⟩
  have hnorm : ‖FourierSpace.ofFunction N ν - 1‖ ≤ η * N := by
    have heq : FourierSpace.ofFunction N ν - 1 =
        FourierSpace.ofFunction N (fun n => ν n - 1) := rfl
    rw [heq, FourierSpace.norm_ofFunction]
    exact herror
  obtain ⟨g, hg, hfg⟩ := hmodel N hN (FourierSpace.ofFunction N ν)
    (fun i => FourierSpace.ofFunction N (f i)) (fun x => hν _ (hmem x))
    (fun i x => hf i _ (hmem x)) (fun x => hνf _ (hmem x)) hnorm
  refine ⟨fun i => FourierSpace.zeroExtend (g i),
    fun i => FourierSpace.zeroExtend_nonneg (hg.1 i),
    fun i => FourierSpace.zeroExtend_le_one (fun x => FourierSpace.models_coordinate_le_one hg i x),
    FourierSpace.sum_zeroExtend_le_one hg,
    fun i n hn => FourierSpace.zeroExtend_eq_zero _ hn, fun i => ?_⟩
  rw [← FourierSpace.norm_ofFunction]
  have heq : FourierSpace.ofFunction N (fun n => f i n - FourierSpace.zeroExtend (g i) n) =
      FourierSpace.ofFunction N (f i) - g i := by
    funext x
    change f i ((x.val : ℤ) + 1) - FourierSpace.zeroExtend (g i) ((x.val : ℤ) + 1) =
      f i ((x.val : ℤ) + 1) - g i x
    rw [FourierSpace.zeroExtend_apply]
  rw [heq]
  exact hfg i

end Sidon
