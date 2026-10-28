module

/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Sidon.NumberTheory.RiemannGaussian.VinogradovKorobovBilinearPhase

@[expose] public section

namespace RiemannGaussian.VinogradovKorobovBlock
noncomputable section
open scoped BigOperators
open RiemannGaussian.VinogradovKorobovBilinearPhase
def block (f : ℕ → ℂ) (L : ℕ) : ℂ := ∑ n ∈ Finset.range L, f n

def boundary (f : ℕ → ℂ) (L p : ℕ) : ℂ :=
  block f p - block (fun n => f (L + n)) p

theorem block_add (f : ℕ → ℂ) (L p : ℕ) :
    block f (L + p) = block f L + block (fun n => f (L + n)) p := by
  exact Finset.sum_range_add f L p

theorem block_shift (f : ℕ → ℂ) (L p : ℕ) :
    block f L = block (fun n => f (n + p)) L + boundary f L p := by
  have h : block f L + block (fun n => f (L + n)) p =
      block f p + block (fun n => f (n + p)) L := by
    rw [← block_add, Nat.add_comm L p, block_add]
    simp only [Nat.add_comm]
  unfold boundary
  linear_combination h

theorem weighted_shift_identity {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (w : ι → ℂ) (f : ℕ → ℂ) (L : ℕ) :
    (∑ i ∈ S, w i) * block f L =
      (∑ n ∈ Finset.range L, ∑ i ∈ S, w i * f (n + p i)) +
      ∑ i ∈ S, w i * boundary f L (p i) := by
  rw [Finset.sum_mul]
  calc
    _ = ∑ i ∈ S, (w i * block (fun n => f (n + p i)) L +
        w i * boundary f L (p i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, ← block_shift]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [block, Finset.mul_sum]
      exact Finset.sum_comm

theorem boundary_norm_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (L p : ℕ) :
    ‖boundary f L p‖ ≤ 2 * p := by
  have hb (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) : ‖block g p‖ ≤ p := by
    calc
      _ ≤ ∑ n ∈ Finset.range p, ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range p, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => hg n)
      _ = _ := by simp
  exact (norm_sub_le _ _).trans (by
    have h₁ := hb f hf
    have h₂ := hb (fun n => f (L + n)) (fun n => hf (L + n))
    linarith)

def dirichletTerm (t z : ℝ) (n : ℕ) : ℂ :=
  ((z + n : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))

def basePhase (t z : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log z : ℝ) : ℂ) * Complex.I)

theorem norm_basePhase (t z : ℝ) : ‖basePhase t z‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem dirichletTerm_eq {z : ℝ} (hz : 0 < z) (t : ℝ) (n : ℕ) :
    dirichletTerm t z n = basePhase t (z + n) := by
  have h := shifted_cpow_eq t (z := z + n) (a := 0) (b := 0) (by positivity)
    (by rfl) (by rfl)
  simpa [dirichletTerm, basePhase, logarithmicPhase] using h

theorem norm_dirichletTerm {z : ℝ} (hz : 0 < z) (t : ℝ) (n : ℕ) :
    ‖dirichletTerm t z n‖ = 1 := by
  rw [dirichletTerm_eq hz, norm_basePhase]

theorem dirichletTerm_shift {z : ℝ} (hz : 0 < z) (t : ℝ) (n a b : ℕ) :
    dirichletTerm t z (n + a * b) =
      basePhase t (z + n) * logarithmicPhase t (z + n) a b := by
  simpa only [dirichletTerm, basePhase, Nat.cast_add, Nat.cast_mul, add_assoc] using
    shifted_cpow_eq t (z := z + n) (a := a) (b := b) (by positivity)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end
end RiemannGaussian.VinogradovKorobovBlock
