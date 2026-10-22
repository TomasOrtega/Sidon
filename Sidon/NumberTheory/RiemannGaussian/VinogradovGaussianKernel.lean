/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Sidon.NumberTheory.RiemannGaussian.VinogradovShiftedMoment

namespace RiemannGaussian.VinogradovGaussianKernel
noncomputable section
open Filter Asymptotics
open scoped BigOperators ComplexConjugate

def weight (a : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * a * (n : ℝ) ^ 2)

def phase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n * x)

def kernel (a x : ℝ) : ℝ :=
  (1 / a ^ (1 / 2 : ℝ)) *
    ∑' m : ℤ, Real.exp (-Real.pi / a * ((m : ℝ) - x) ^ 2)

theorem summable_real_quadratic {A : ℝ} (hA : A < 0) (B C : ℝ) :
    Summable (fun n : ℤ => Real.exp (A * (n : ℝ) ^ 2 + B * n + C)) := by
  have h := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
    (a := (A : ℂ)) (by simpa using hA) (B : ℂ) (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (h.comp_tendsto Int.tendsto_coe_cofinite)
  have hm := hs.mul_right (Complex.exp C)
  apply Complex.summable_ofReal.mp
  apply hm.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [← Complex.exp_add, Complex.ofReal_exp]
  push_cast
  rfl

theorem summable_weight {a : ℝ} (ha : 0 < a) : Summable (weight a) := by
  change Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2))
  simpa only [zero_mul, add_zero] using
    summable_real_quadratic (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha) 0 0

theorem summable_kernel_translates {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable (fun m : ℤ => Real.exp (-Real.pi / a * ((m : ℝ) - x) ^ 2)) := by
  have h := summable_real_quadratic
    (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha)
    (2 * Real.pi / a * x) (-Real.pi / a * x ^ 2)
  convert h using 1
  ext m
  congr 1
  ring

theorem norm_phase (n : ℤ) (x : ℝ) : ‖phase n x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem phase_mul_conj (n : ℤ) (x y : ℝ) :
    phase n x * conj (phase n y) = phase n (x - y) := by
  simp only [phase, ← Complex.exp_conj, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_intCast]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem poisson {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∑' n : ℤ, (weight a n : ℂ) * phase n x) = (kernel a x : ℂ) := by
  have h := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) (Complex.I * x)
  have he (n : ℤ) : (weight a n : ℂ) * phase n x =
      Complex.exp (-Real.pi * (a : ℂ) * n ^ 2 +
        2 * Real.pi * (Complex.I * x) * n) := by
    rw [weight, phase, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [h]
  have hi : Complex.I * (Complex.I * (x : ℂ)) = -x := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  simp only [hi, ← sub_eq_add_neg]
  simp only [kernel, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow ha.le, Complex.ofReal_tsum, Complex.ofReal_exp,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]

theorem kernel_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < kernel a x := by
  have h := (summable_kernel_translates ha x).sum_le_tsum {0}
    (fun m _ => (Real.exp_pos _).le)
  simp only [Finset.sum_singleton] at h
  unfold kernel
  exact mul_pos (by positivity) ((Real.exp_pos _).trans_le h)

theorem kernel_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ kernel a x :=
  (kernel_pos ha x).le

theorem summable_lattice_product {k : ℕ} (f : Fin k → ℤ → ℂ)
    (hf : ∀ j, Summable (f j)) :
    Summable (fun n : Fin k → ℤ => ∏ j, f j (n j)) := by
  induction k with
  | zero => exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ k ih =>
    have ht := ih (fun j => f j.succ) (fun j => hf j.succ)
    have hp := summable_mul_of_summable_norm (hf 0).norm ht.norm
    have he := hp.comp_injective (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).symm.injective
    simpa only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Function.comp_def,
      Fin.prod_univ_succ, Fin.tail] using he

theorem tsum_lattice_product {k : ℕ} (f : Fin k → ℤ → ℂ)
    (hf : ∀ j, Summable (f j)) :
    (∑' n : Fin k → ℤ, ∏ j, f j (n j)) = ∏ j, ∑' n : ℤ, f j n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := summable_lattice_product (fun j => f j.succ) (fun j => hf j.succ)
    have he := (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).symm.tsum_eq
      (fun p : ℤ × (Fin k → ℤ) => f 0 p.1 * ∏ j, f j.succ (p.2 j))
    simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail] at he
    simp_rw [Fin.prod_univ_succ]
    rw [he, ← tsum_mul_tsum_of_summable_norm (hf 0).norm ht.norm,
      ih (fun j => f j.succ) (fun j => hf j.succ)]

def latticeWeight {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) : ℝ :=
  ∏ j, weight (a j) (n j)

def latticePhase {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) : ℂ :=
  ∏ j, phase (n j) (x j)

def latticeKernel {k : ℕ} (a x : Fin k → ℝ) : ℝ := ∏ j, kernel (a j) (x j)

theorem summable_latticeWeight {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    Summable (latticeWeight a) := by
  apply Complex.summable_ofReal.mp
  simpa only [latticeWeight, Complex.ofReal_prod] using
    summable_lattice_product (fun j n => (weight (a j) n : ℂ))
      (fun j => Complex.summable_ofReal.mpr (summable_weight (ha j)))

theorem norm_latticePhase {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) :
    ‖latticePhase n x‖ = 1 := by
  simp only [latticePhase, norm_prod, norm_phase, Finset.prod_const_one]

theorem latticePhase_mul_conj {k : ℕ} (n : Fin k → ℤ) (x y : Fin k → ℝ) :
    latticePhase n x * conj (latticePhase n y) = latticePhase n (x - y) := by
  simp only [latticePhase, map_prod, ← Finset.prod_mul_distrib,
    phase_mul_conj, Pi.sub_apply]

theorem lattice_poisson {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (x : Fin k → ℝ) :
    (∑' n : Fin k → ℤ, (latticeWeight a n : ℂ) * latticePhase n x) =
      (latticeKernel a x : ℂ) := by
  have hs (j : Fin k) : Summable (fun n : ℤ => (weight (a j) n : ℂ) * phase n (x j)) := by
    apply (summable_weight (ha j)).of_norm_bounded
    intro n
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      weight, abs_of_pos (Real.exp_pos _)]
  simp only [latticeWeight, latticePhase, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  rw [tsum_lattice_product _ hs]
  simp only [poisson, latticeKernel, Complex.ofReal_prod, ha]

theorem latticeWeight_nonneg {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) :
    0 ≤ latticeWeight a n :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

theorem summable_latticeFourier {k : ℕ} {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (x : Fin k → ℝ) :
    Summable (fun n : Fin k → ℤ => (latticeWeight a n : ℂ) * latticePhase n x) := by
  apply (summable_latticeWeight ha).of_norm_bounded
  intro n
  rw [norm_mul, norm_latticePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (latticeWeight_nonneg a n)]

theorem latticePhase_eq_mFourier {k : ℕ} (n : Fin k → ℤ) (x : Fin k → ℝ) :
    latticePhase n x = UnitAddTorus.mFourier n (fun j => (x j : UnitAddCircle)) := by
  simp only [latticePhase, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, Complex.ofReal_one, div_one, phase]

theorem summable_energy {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    Summable (fun n : Fin k → ℤ =>
      latticeWeight a n * ‖∑ b, w b * latticePhase n (x b)‖ ^ 2) := by
  have hb (n : Fin k → ℤ) : ‖∑ b, w b * latticePhase n (x b)‖ ≤ ∑ b, ‖w b‖ := by
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_mul, norm_latticePhase, mul_one]
  apply ((summable_latticeWeight ha).mul_right ((∑ b, ‖w b‖) ^ 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (latticeWeight_nonneg a n) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb n) 2)
    (latticeWeight_nonneg a n)

theorem energy_eq_gram {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    ((∑' n : Fin k → ℤ, latticeWeight a n *
        ‖∑ b, w b * latticePhase n (x b)‖ ^ 2 : ℝ) : ℂ) =
      ∑ b, ∑ c, (w b * conj (w c)) * (latticeKernel a (x b - x c) : ℂ) := by
  classical
  have hi (b c : ι) := (summable_latticeFourier ha (x b - x c)).mul_left
    (w b * conj (w c))
  have he (n : Fin k → ℤ) :
      ((latticeWeight a n * ‖∑ b, w b * latticePhase n (x b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ b, ∑ c, (w b * conj (w c)) *
          ((latticeWeight a n : ℂ) * latticePhase n (x b - x c)) := by
    rw [Complex.ofReal_mul, Complex.sq_norm, ← Complex.mul_conj]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
      ← latticePhase_mul_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [Complex.ofReal_tsum]
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b _ => summable_sum (fun c _ => hi b c))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c _ => hi b c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [tsum_mul_left, lattice_poisson ha]

def frequencyCost {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) : ℝ :=
  ∑ j, Real.pi * a j * (n j : ℝ) ^ 2

theorem latticeWeight_eq_exp {k : ℕ} (a : Fin k → ℝ) (n : Fin k → ℤ) :
    latticeWeight a n = Real.exp (-frequencyCost a n) := by
  simp only [latticeWeight, weight, frequencyCost, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finite_energy_le_gram {k : ℕ} {ι : Type*} [Fintype ι]
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (x : ι → Fin k → ℝ) (w : ι → ℂ)
    (C : Finset (Fin k → ℤ)) {Q : ℝ}
    (hQ : ∀ n ∈ C, frequencyCost a n ≤ Q) :
    (∑ n ∈ C, ‖∑ b, w b * latticePhase n (x b)‖ ^ 2) ≤
      Real.exp Q * (∑ b, ∑ c, (w b * conj (w c)) *
        (latticeKernel a (x b - x c) : ℂ)).re := by
  have hg := congrArg Complex.re (energy_eq_gram ha x w)
  rw [Complex.ofReal_re] at hg
  rw [← hg, ← tsum_mul_left]
  have hs := (summable_energy ha x w).mul_left (Real.exp Q)
  apply (Finset.sum_le_sum (fun n hn => ?_)).trans
    (hs.sum_le_tsum C (fun n _ => mul_nonneg (Real.exp_pos Q).le
      (mul_nonneg (latticeWeight_nonneg a n) (sq_nonneg _))))
  have h : 1 ≤ Real.exp Q * latticeWeight a n := by
    rw [latticeWeight_eq_exp, ← Real.exp_add, Real.one_le_exp_iff]
    linarith [hQ n hn]
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right h
    (sq_nonneg ‖∑ b, w b * latticePhase n (x b)‖)

def supportCost {k : ℕ} (a : Fin k → ℝ) (C : Finset (Fin k → ℤ)) : ℝ := by
  classical
  exact (insert 0 (C.image (frequencyCost a))).max' (by simp)

theorem frequencyCost_le_supportCost {k : ℕ} (a : Fin k → ℝ)
    (C : Finset (Fin k → ℤ)) {n : Fin k → ℤ} (hn : n ∈ C) :
    frequencyCost a n ≤ supportCost a C := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

theorem latticePhase_add {k : ℕ} (n : Fin k → ℤ) (x y : Fin k → ℝ) :
    latticePhase n (x + y) = latticePhase n x * latticePhase n y := by
  simp only [latticePhase, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add]
  ring

theorem product_latticePhase {k : ℕ} {ι : Type*} (S : Finset ι)
    (n : Fin k → ℤ) (x : ι → Fin k → ℝ) :
    (∏ b ∈ S, latticePhase n (x b)) = latticePhase n (∑ b ∈ S, x b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [latticePhase, phase]
  | @insert b S hb ih => simp [hb, ih, latticePhase_add]

theorem sample_power_expansion {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (n : Fin k → ℤ) (x : ι → Fin k → ℝ) (w : ι → ℂ) :
    (∑ b, w b * latticePhase n (x b)) ^ s =
      ∑ b : Fin s → ι, VinogradovShiftedMoment.tupleWeight s w b *
        latticePhase n (∑ j, x (b j)) := by
  classical
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, product_latticePhase]
  rfl

def momentGram {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a : Fin k → ℝ) (x : ι → Fin k → ℝ) (w : ι → ℂ) : ℂ :=
  ∑ b : Fin s → ι, ∑ c : Fin s → ι,
    (VinogradovShiftedMoment.tupleWeight s w b *
      conj (VinogradovShiftedMoment.tupleWeight s w c)) *
      (latticeKernel a ((∑ j, x (b j)) - ∑ j, x (c j)) : ℂ)

end
end RiemannGaussian.VinogradovGaussianKernel
