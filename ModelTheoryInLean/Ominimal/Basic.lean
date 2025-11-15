import Mathlib.ModelTheory.Order
import Aesop
import ModelTheoryInLean.Ominimal.Semialgebriac.Basic
import ModelTheoryInLean.Definability

namespace Ominimal

open FirstOrder FirstOrder.Language Semialgebraic Set

class OminimalStrucuture (L : Language) [L.IsOrdered]
  (M : Type*) [L.Structure M] [LinearOrder M] [M ⊨ L.dlo] : Prop where
  definable_is_semialgebraic : ∀ (s : Set M), UDefinable₁ L s → IsSemialgebraic s

variable {M : Type*} [TopologicalSpace M] [LinearOrder M] [OrderTopology M]

variable [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]

variable {L : Language} [L.IsOrdered] [L.Structure M] [L.OrderedStructure M]

omit [TopologicalSpace M] [OrderTopology M] [DenselyOrdered M]
[NoMinOrder M] [NoMaxOrder M] [Nonempty M] in
lemma open_intervals_univ_definable (I : Set M)
    (hI : ∃ (a b : M), a < b ∧ I = Ioo a b) : UDefinable₁ L I := by
  obtain ⟨a, b, hab, rfl⟩ := hI
  rw [UDefinable₁, Definable₁]
  rw [Set.definable_iff_exists_formula_sum]
  -- We construct the formula: a < x₀ ∧ x₀ < b
  -- where a and b are parameters (Sum.inl) and x₀ is a free variable (Sum.inr)
  let a' : ↑(univ : Set M) := ⟨a, trivial⟩
  let b' : ↑(univ : Set M) := ⟨b, trivial⟩
  -- For Formula (↑univ ⊕ Fin 1), we need terms of type L.Term ((↑univ ⊕ Fin 1) ⊕ Fin 0)
  let ta : L.Term ((↑(univ : Set M) ⊕ Fin 1) ⊕ Fin 0) :=
    Term.var (Sum.inl (Sum.inl (α := ↑(univ : Set M)) (β := Fin 1) a'))
  let tb : L.Term ((↑(univ : Set M) ⊕ Fin 1) ⊕ Fin 0) :=
    Term.var (Sum.inl (Sum.inl (α := ↑(univ : Set M)) (β := Fin 1) b'))
  let tx : L.Term ((↑(univ : Set M) ⊕ Fin 1) ⊕ Fin 0) :=
    Term.var (Sum.inl (Sum.inr (α := ↑(univ : Set M)) (β := Fin 1) (0 : Fin 1)))
  use ta.lt tx ⊓ tx.lt tb
  ext v
  simp only [Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_inf]
  constructor
  · intro h
    simp only [Ioo, Set.mem_setOf_eq] at h
    obtain ⟨h1, h2⟩ := h
    constructor
    · simp [Term.realize_lt, ta, tx]
      exact h1
    · simp [Term.realize_lt, tx, tb]
      exact h2
  · intro ⟨h1, h2⟩
    simp only [Ioo, Set.mem_setOf_eq]
    simp [Term.realize_lt, ta, tx, tb] at h1 h2
    exact ⟨h1, h2⟩

lemma cofinite_definable_subset_of_open_interval (I D : Set M)
  (hI : ∃ (a b : M), a < b∧ I = Ioo a b)
  (hD : UDefinable₁ L D) (hID : I ⊆ closure D)
  [OminimalStrucuture L M] : (I \ D).Finite := by
  rcases hI with ⟨a,b,hab,Iab⟩
  rw [←Set.not_infinite]
  by_contra inf
  simp [UDefinable₁, Definable₁] at hD
  suffices UDefinable₁ L (I \ D) by
    have hS : IsSemialgebraic (I \ D) :=
      OminimalStrucuture.definable_is_semialgebraic (I \ D) this
    rw [infinite_semialgebriac_set_iff_nonempty_interior (I \ D) hS] at inf
    obtain ⟨c, d, hcd, hIcd⟩ :=
      IsOpen.exists_Ioo_subset (isOpen_interior) inf
    have hIcd': Ioo c d ⊆ (closure D)ᶜ := by
      intro x hx
      refine mem_compl ?_
      intro hx'
      rw [mem_closure_iff] at hx'
      have Icd_inter_D : (Ioo c d ∩ D).Nonempty := hx' (Ioo c d) isOpen_Ioo hx
      have : (Ioo c d ∩ D) = ∅ := by
        rw [←disjoint_iff_inter_eq_empty, ← subset_compl_iff_disjoint_right]
        trans interior (I \ D)
        · exact hIcd
        trans (I \ D)
        · exact interior_subset
        exact diff_subset_compl I D
      rw [this] at Icd_inter_D
      exact not_nonempty_empty Icd_inter_D
    have : Ioo c d ⊆ closure D := by
      trans interior (I \ D)
      · exact hIcd
      trans I \ D
      · exact interior_subset
      trans I
      · exact diff_subset
      exact hID
    have hIcd'': Ioo c d ⊆ closure D ∩ (closure D)ᶜ := subset_inter this hIcd'
    have : closure D ∩ (closure D)ᶜ = ∅ := inter_compl_self (closure D)
    rw [this, subset_empty_iff] at hIcd''
    have : (Ioo c d).Nonempty := nonempty_Ioo.mpr hcd
    rw [hIcd''] at this
    exact not_nonempty_empty this
  have hI : UDefinable₁ L I := by
    apply open_intervals_univ_definable I
    use a,b
  rw [UDefinable₁] at *
  exact Set.Definable.sdiff hI hD

end Ominimal
