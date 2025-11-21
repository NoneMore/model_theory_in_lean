import Mathlib.ModelTheory.Order
import Aesop
import ModelTheoryInLean.Ominimal.Semialgebriac.Basic
import ModelTheoryInLean.Definability
import Mathlib.Data.Set.Function

namespace Ominimal

open FirstOrder FirstOrder.Language Semialgebraic Set Setoid

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
  (hI : ∃ (a b : M), a < b ∧ I = Ioo a b)
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

/--
A definable function with a finite range is constant on each component of a partition
induced by some finite set.
-/
lemma definable_fun_const_on_partition_of_finite_range [OminimalStrucuture L M]
    {f : M → M} (hf_def : UDefinableFun L (univ.restrict f))
    (hf_finite : (range f).Finite) :
    ∃ (F : Finset M), ∀ C ∈ finset_to_partition F, ∃ c, ∀ x ∈ C, f x = c := by
  classical
  -- For each s in the range of f, the fiber f⁻¹' {s} is a definable set.
  have h_fiber_def : ∀ s, UDefinable₁ L (f⁻¹' {s}) := by
    intro s
    have fiber_eq : f⁻¹' {s} = Subtype.val '' (univ.restrict f ⁻¹' {s}) := by { ext x; simp [restrict] }
    rw [fiber_eq]
    exact udefinable_fiber_of_UDefFun L hf_def s

  -- The set F is the union of the frontiers of all fibers.
  let F_set := ⋃ s ∈ range f, frontier (f⁻¹' {s})
  -- Since the range is finite and in an o-minimal structure, definable sets (the fibers)
  -- are semialgebraic with finite frontiers, F_set is finite.
  have hF_finite : F_set.Finite :=
    Finite.biUnion hf_finite fun s _ =>
      finite_frontier_of_semialgebriac_set (OminimalStrucuture.definable_is_semialgebraic _ (h_fiber_def s))
  let F := hF_finite.toFinset
  use F

  -- Now, we show f is constant on each cell C of the partition induced by F.
  intro C hC_part
  obtain ⟨x, hx_in_C⟩ := nonempty_of_mem_partition (finset_to_partition_is_partition F) hC_part
  let c := f x
  use c

  -- The fiber S is semialgebraic.
  let S := f⁻¹' {c}
  have hS_sa : IsSemialgebraic S := OminimalStrucuture.definable_is_semialgebraic _ (h_fiber_def c)

  -- A semialgebraic set respects the partition induced by its frontier.
  have h_respects_F : RespectsPartition S (finset_to_partition_is_partition F) := by
    refine respects_partition_of_subset ?_ (semialgebraic_respects_frontier_partition S hS_sa)
    -- Proof that frontier S ⊆ F.toSet
    intro a ha_in_frontier_S
    simp [S, c] at ha_in_frontier_S
    simp [F,F_set]
    use x

  -- For any cell C, either C ⊆ S or C is disjoint from S.
  rw [respects_partition_iff_respects_partition'] at h_respects_F
  specialize h_respects_F C hC_part

  -- Since x ∈ C and f(x) = c (so x ∈ S), C and S are not disjoint.
  have h_nondisjoint : (C ∩ S).Nonempty := ⟨x, hx_in_C, rfl⟩

  -- Thus, C must be a subset of S, which means for all y ∈ C, f(y) = c.
  rcases h_respects_F with h_subset | h_disjoint
  · intro y hy_in_C
    exact h_subset hy_in_C
  · exfalso
    exact h_nondisjoint.ne_empty (disjoint_iff_inter_eq_empty.mp h_disjoint)

end Ominimal
