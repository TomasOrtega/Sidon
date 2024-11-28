import Mathlib.Data.ZMod.Basic

open Set Cardinal

/-- A Sidon set is a set of elements in any additive commutative monoid
    where all pairwise sums are distinct. -/
def IsSidonSet {M : Type} [AddCommMonoid M] (s : Set M) : Prop :=
  ∀ a b c d, a ∈ s → b ∈ s → c ∈ s → d ∈ s →
  a + b = c + d → ({a, b} : Set M) = ({c, d} : Set M)

/-- The empty set is a Sidon set in any additive commutative monoid -/
theorem empty_is_sidon {M : Type} [AddCommMonoid M] :
  IsSidonSet (∅ : Set M) := by
  intros _ _ _ _ h
  exact fun _ _ _ _ => False.elim h

/-- Any singleton is a Sidon set in any additive commutative monoid -/
theorem singleton_is_sidon {M : Type} [AddCommMonoid M] (x : M) :
  IsSidonSet {x} := by
  intros _ _ _ _ ha hb hc hd _
  rw [ha, hb, hc, hd]

/-- A Sidon subset is a Sidon set -/
theorem sidon_subset_is_sidon {M : Type} [AddCommMonoid M] {s : Set M} (h : IsSidonSet s) : ∀ t : Set M, t ⊆ s → IsSidonSet t := by
intros t htins a b c d ha hb hc hd sum
exact h a b c d (htins ha) (htins hb) (htins hc) (htins hd) sum

/-- In a finite additive commutative group M, a Sidon set s with size #s satisfies #s * (#s - 1) ≤ #M.-/
theorem sidon_set_size_bound {M : Type} [AddCommGroup M] [Fintype M] {s : Finset M} (h : IsSidonSet s.toSet) : s.card * s.card - s.card ≤ toNat #M := by
  have : DecidableEq M := Classical.typeDecidableEq M
  let offDiag_s := Finset.offDiag s -- we use DecidableEq M here
  rw [<-Finset.offDiag_card s]
  let f_diffs := fun (t : offDiag_s) => t.val.1 - t.val.2
  have inj_diffs : Function.Injective f_diffs := by
    intros x y hxy
    obtain ⟨⟨a, b⟩ , hx⟩ := x
    obtain ⟨⟨c, d⟩ , hy⟩ := y
    rw [Finset.mem_offDiag] at hx hy
    obtain ⟨ains, bins, aneqb⟩ := hx
    obtain ⟨cins, dins, cneqd⟩ := hy
    rw [Subtype.mk.injEq]
    have sums : a + d = c + b := sub_eq_sub_iff_add_eq_add.mp hxy
    have hac : a = c := by
      have mem_a : a ∈ {a, d} := Set.mem_insert a {d}
      have hSidon := h a d c b ains dins cins bins sums
      rw [hSidon] at mem_a -- a ∈ {c, b}
      have : a = c ∨ a = b := mem_a
      have : a ≠ b := aneqb
      tauto
    rw [hac, add_right_inj] at sums
    exact Prod.ext hac sums.symm

  let ims := Finset.image f_diffs offDiag_s.attach

  calc
    s.offDiag.card = ims.card := by
      dsimp only [ims]
      rw [<-Finset.univ_eq_attach]
      rw [Finset.card_image_of_injective Finset.univ inj_diffs]
      rw [Finset.univ_eq_attach, Finset.card_attach]
    _ ≤ toNat #(M) := by
      dsimp only [ims]
      rw [<-Finset.univ_eq_attach, mk_fintype, toNat_natCast] -- we use Fintype M here
      exact Finset.card_le_univ _

/-- A Sidon set s in ℤ mod n (n not zero) with size |s| satisfies |s| * (|s| - 1) ≤ n -/
theorem sidon_set_size_bound_zmodn {n : ℕ} (n_ne_zero : NeZero n) (s : Finset (ZMod n)) (h : IsSidonSet s.toSet) : s.card * s.card - s.card ≤ n := calc
    s.card * s.card - s.card ≤ toNat #(ZMod n) := sidon_set_size_bound h
    _ = n := by rw [mk_fintype, ZMod.card, toNat_natCast] -- we use n_ne_zero here
