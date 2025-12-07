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

omit [TopologicalSpace M] [OrderTopology M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M] in
lemma definable_lt :
    univ.Definable L {v : Fin 2 → M | v 0 < v 1} := by
  rw [Set.definable_iff_exists_formula_sum]
  -- We construct the formula x₀ < x₁
  let tx : L.Term (((↑univ : Set M) ⊕ Fin 2) ⊕ Fin 0) :=
    Term.var (Sum.inl (Sum.inr (0 : Fin 2)))
  let ty : L.Term (((↑univ : Set M) ⊕ Fin 2) ⊕ Fin 0) :=
    Term.var (Sum.inl (Sum.inr (1 : Fin 2)))
  use tx.lt ty
  ext v
  simp only [Set.mem_setOf_eq, Formula.Realize]
  -- We can now prove both directions with `simp`
  constructor <;> simp [tx,ty]

omit [TopologicalSpace M] [OrderTopology M] [DenselyOrdered M]
[NoMinOrder M] [NoMaxOrder M] [Nonempty M] in
lemma definable_lt_con (a : M) :
    univ.Definable L {v : Fin 1 → M | v 0 < a} := by
  let p : (Fin 2 → M) → Prop := fun v => v 0 < v 1 ∧ v 1 = a
  have S_def : univ.Definable L { v : Fin 2 → M | p v }:= by
    apply Definable.inter definable_lt
    apply Definable.preimage_comp ![1] (definable_con a)
  let S'_def := definable_exists S_def
  convert S'_def using 1
  aesop

omit [TopologicalSpace M] [OrderTopology M] [DenselyOrdered M]
[NoMinOrder M] [NoMaxOrder M] [Nonempty M] in
lemma definable_con_lt (a : M) :
    univ.Definable L {v : Fin 1 → M | a < v 0} := by
  let S := { v : Fin 2 → M | v 0 < v 1 ∧ v 0 = a }
  have S_def : univ.Definable L S:= by
    simp [S]
    apply Definable.inter definable_lt
    apply Definable.preimage_comp ![0] (definable_con a)
  have S'_def:= Definable.image_comp S_def ![1]
  suffices {v | a < v 0} = ((fun g ↦ g ∘ ![1]) '' S) from by rwa [this]
  ext v ; simp [S]
  constructor <;> intro h
  · use ![a, v 0] ; simp
    exact ⟨h,List.ofFn_inj.mp rfl⟩
  · aesop

omit [TopologicalSpace M] [OrderTopology M] [DenselyOrdered M]
[NoMinOrder M] [NoMaxOrder M] [Nonempty M] in
lemma open_intervals_univ_definable (I : Set M)
    (hI : ∃ (a b : M), a < b ∧ I = Ioo a b) : UDefinable₁ L I := by
  obtain ⟨a, b, _, rfl⟩ := hI
  rw [UDefinable₁, Definable₁]
  simp [Ioo]
  refine Definable.inter (definable_con_lt a) (definable_lt_con b)

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
    {S : Type*} [Finite S] {f : M → S} (hf_def : DefinableFunOfFiniteRange L f) :
    ∃ (F : Finset M), ∀ C ∈ finset_to_partition F, ∃ c, ∀ x ∈ C, f x = c := by
  classical
  -- The set F is the union of the frontiers of all fibers.
  let F_set := ⋃ (s : S), frontier (f⁻¹' {s})
  -- Since S is finite and in an o-minimal structure, definable sets (the fibers)
  -- are semialgebraic with finite frontiers, F_set is finite.
  have hF_finite : F_set.Finite := by
    apply Set.finite_iUnion
    intro s
    exact finite_frontier_of_semialgebriac_set (OminimalStrucuture.definable_is_semialgebraic _ (hf_def s))
  let F := hF_finite.toFinset
  use F

  -- Now, we show f is constant on each cell C of the partition induced by F.
  intro C hC_part
  obtain ⟨x, hx_in_C⟩ := nonempty_of_mem_partition (finset_to_partition_is_partition F) hC_part
  let c := f x
  use c

  -- The fiber S is semialgebraic.
  let S := f⁻¹' {c}
  have hS_sa : IsSemialgebraic S := OminimalStrucuture.definable_is_semialgebraic _ (hf_def c)

  -- A semialgebraic set respects the partition induced by its frontier.
  have h_respects_F : RespectsPartition S (finset_to_partition_is_partition F) := by
    refine respects_partition_of_subset ?_ (semialgebraic_respects_frontier_partition S hS_sa)
    -- Proof that frontier S ⊆ F.toSet
    intro a ha_in_frontier_S
    simp [S, c] at ha_in_frontier_S
    simp [F,F_set]
    use c

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

lemma definable_lt_of_fun {f : M → M} (f_def : UDefinableFun L (univ.restrict f)) :
    UDefinable₂ L { v | f v.1 < f v.2} := by
  simp [UDefinable₂, Definable₂]
  simp [UDefinableFun, UDefinable₂, Definable₂] at f_def
  have : univ.Definable L {v : Fin 4 → M | f (v 0) = v 2 ∧ f (v 1) = v 3 ∧ v 2 < v 3} := by
    apply Definable.inter
    · apply Definable.preimage_comp ![0,2] f_def
    apply Definable.inter
    · apply Definable.preimage_comp ![1,3] f_def
    apply Definable.preimage_comp ![2,3] definable_lt
  simpa [Fin.snoc] using definable_exists (definable_exists this)

end Ominimal
