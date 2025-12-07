import ModelTheoryInLean.Ominimal.Basic
import ModelTheoryInLean.Definability
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FinCases

namespace Ominimal

open FirstOrder FirstOrder.Language Semialgebraic Set Topology

variable {M : Type*} [TopologicalSpace M] [LinearOrder M] [OrderTopology M]

variable [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]

variable {L : Language} [L.IsOrdered] [L.Structure M] [L.OrderedStructure M]

variable [OminimalStrucuture L M]

section defs

variable (p : M → Prop) (a : M)

def eventuallyRight : Prop :=
  ∀ᶠ x in 𝓝[>] a, p x

def eventuallyLeft : Prop :=
  ∀ᶠ x in 𝓝[<] a, p x

def eventuallyRight' : Prop :=
  ∃ b, a < b ∧ ∀ c, a < c ∧ c < b → p c

def eventuallyLeft' : Prop :=
  ∃ b, b < a ∧ ∀ c, b < c ∧ c < a → p c

theorem eventuallyRight_iff_eventuallyRight' :
    eventuallyRight p a ↔ eventuallyRight' p a := by
  simp [eventuallyRight, eventuallyRight']
  constructor <;> intro h
  · simp [Filter.Eventually] at h
    obtain ⟨b,hb,hab⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
    use b, hb
    aesop
  · simp [Filter.Eventually]
    obtain ⟨b,hb,hab⟩ := h
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    use b, hb
    simpa [Ioo]

theorem eventuallyLeft_iff_eventuallyLeft' :
    eventuallyLeft p a ↔ eventuallyLeft' p a := by
  simp [eventuallyLeft, eventuallyLeft']
  constructor <;> intro h
  · simp [Filter.Eventually] at h
    obtain ⟨b,hb,hab⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp h
    use b, hb
    aesop
  · simp [Filter.Eventually]
    obtain ⟨b,hb,hab⟩ := h
    apply mem_nhdsLT_iff_exists_Ioo_subset.mpr
    use b, hb
    simpa [Ioo]

end defs

/-- The function `comparator(x)` that compares `f(x)` with `f(a)`. -/
noncomputable def comparator (f : M → M) (a : M) : M → Fin 3 :=
  fun x =>
    if f x < f a then
      0
    else if f x = f a then
      1
    else
      2

/--
Let `f : M → M` be a definable function, and let `a ∈ M` be a point.
The function `comparator(x)` that compares `f(x)` with `f(a)` has a finite range and is definable.
-/
lemma comparator_is_definable_of_finite_range {f : M → M} (hf_def : UDefinableFun L (univ.restrict f)) (a : M) :
    DefinableFunOfFiniteRange L (comparator f a) := by
  intro i
  simp [UDefinable₁, Definable₁]
  fin_cases i
  · have S_def : univ.Definable L {v : Fin 1 → M | f (v 0) < f a} := by
      have S₁_def : univ.Definable L {v : Fin 2 → M | f (v 0) < v 1} := by
        have S₁_def : univ.Definable L {v : Fin 3 → M | v 2 < v 1} := by
          apply Definable.preimage_comp ![2,1] definable_lt
        have S₂_def : univ.Definable L {v : Fin 3 → M | v 2 = f (v 0)} := by
          simp [UDefinableFun,UDefinable₂,Definable₂] at hf_def
          convert (Definable.preimage_comp (![0,2] : Fin 2 → Fin 3) hf_def) using 1
          ext v ; simp ; grind
        let S₃_def := Definable.inter S₁_def S₂_def
        simp [Set.inter_def] at S₃_def
        convert (definable_exists S₃_def) using 1
        simp [Fin.snoc]
      have S₂_def : univ.Definable L {v : Fin 2 → M | v 1 = f a} := by
        apply Definable.preimage_comp ![1] (definable_con (f a))
      let S_def := Definable.inter S₁_def S₂_def
      simp [Set.inter_def] at S_def
      let := definable_exists S_def
      convert this using 1
      simp [Fin.snoc]
    convert S_def using 1
    ext v
    simp [comparator] ; split_ifs with hf
    · grind
    grind
  · sorry
  · sorry

theorem UDefinable₁.eventually_right {p : M → Prop} (p_def : UDefinable₁ L {x | p x}) : UDefinable₁ L {(x : M) | eventuallyRight p x} := by
  let S : Set M := {x | ∃ y, x < y ∧ ¬ ∃ z, (x < z ∧ z < y) ∧ ¬ p z}
  suffices UDefinable₁ L S from by
    have : {x | eventuallyRight p x} = S := by
      simp [S, eventuallyRight_iff_eventuallyRight', eventuallyRight']
    rwa [this]
  simp [UDefinable₁, Definable₁, S]
  have S₁_def : univ.Definable L {v : Fin 3 → M | (v 0 < v 2 ∧ v 2 < v 1) ∧ ¬p (v 2)} := by
    apply Definable.inter
    · apply Definable.inter
      · apply Definable.preimage_comp ![0,2] definable_lt
      apply Definable.preimage_comp ![2,1] definable_lt
    apply Definable.compl
    apply Definable.preimage_comp ![2] p_def
  let S₂_def := definable_exists S₁_def
  let S_def := definable_exists (Definable.inter definable_lt (Definable.compl S₂_def))
  convert S_def using 1
  simp [Fin.snoc,Set.inter_def]
  rfl

theorem UDefinable₁.eventually_left {p : M → Prop} (p_def : UDefinable₁ L {x | p x}) : UDefinable₁ L {(x : M) | eventuallyLeft p x} := by
  let S : Set M := {x | ∃ y, y < x ∧ ¬ ∃ z, (y < z ∧ z < x) ∧ ¬ p z}
  suffices UDefinable₁ L S from by
    have : {x | eventuallyLeft p x} = S := by
      simp [S, eventuallyLeft_iff_eventuallyLeft', eventuallyLeft']
    rwa [this]
  simp [UDefinable₁, Definable₁, S]
  have S₁_def : univ.Definable L {v : Fin 3 → M | (v 1 < v 2 ∧ v 2 < v 0) ∧ ¬p (v 2)} := by
    apply Definable.inter
    · apply Definable.inter
      · apply Definable.preimage_comp ![1,2] definable_lt
      apply Definable.preimage_comp ![2,0] definable_lt
    apply Definable.compl
    apply Definable.preimage_comp ![2] p_def
  let S₂_def := definable_exists S₁_def
  let S_def := definable_exists (Definable.inter (Definable.preimage_comp ![1,0] definable_lt) (Definable.compl S₂_def))
  convert S_def using 1
  simp [Fin.snoc,Set.inter_def]
  rfl

/--
Let `f : M → S` be a definable function with `S` finite. For any `a ∈ M`, there is a `j ∈ S` such that `f` is eventually `j` to the right of `a`.
-/
theorem definable_fun_eventually_right {S : Type*} [Finite S] {f : M → S}
  (hf_def : DefinableFunOfFiniteRange L f) :
    ∀ a : M, ∃ j : S, eventuallyRight (fun x => f x = j) a := by
  intro a
  obtain ⟨F,hF⟩ := definable_fun_const_on_partition_of_finite_range hf_def
  by_cases haF : a ∈ F
  · let aR := { x ∈ F | a < x }
    have haRF: aR ⊆ F := Finset.filter_subset (fun x ↦ a < x) F
    by_cases haR : aR.Nonempty
    · let b := aR.min' haR
      have hbF : b ∈ F := by simp [b] ; exact haRF (Finset.min'_mem aR haR)
      specialize hF (Ioo a b) ?_
      · refine (mem_finset_to_partition_iff ⟨a,haF⟩).mpr ?_
        right ; right ; right
        use a, haF, b, hbF, (by simp [b,aR]), rfl
        simp [b,aR]
        grind
      obtain ⟨j,hj⟩ := hF
      use j
      rw [eventuallyRight_iff_eventuallyRight', eventuallyRight']
      use b, (by simp [b,aR]), hj
    specialize hF (Ioi a) ?_
    · refine (mem_finset_to_partition_iff ⟨a,haF⟩).mpr ?_
      left ; congr ; symm
      rw [Finset.max'_eq_iff F ⟨a,haF⟩ a]
      refine ⟨haF,by grind⟩
    obtain ⟨j,hj⟩ := hF
    use j
    rw [eventuallyRight_iff_eventuallyRight', eventuallyRight']
    obtain ⟨b, hb⟩ := exists_gt a
    use b, hb, (by grind)
  obtain ⟨C,⟨hC,haC⟩,_⟩ := (finset_to_partition_is_partition F).2 a
  specialize hF C hC
  obtain ⟨j,hj⟩ := hF
  use j
  rw [eventuallyRight_iff_eventuallyRight', eventuallyRight']
  by_cases hF : F.Nonempty
  · rcases (mem_finset_to_partition_iff hF).mp hC with hC | hC | hC | ⟨b,hb,c,hc,hbc,hCbc,hFbc⟩
    · obtain ⟨b, hb⟩ := exists_gt a
      use b, hb, (by grind)
    · grind
    · grind
    · grind
  simp [Finset.not_nonempty_iff_eq_empty.mp hF, finset_to_partition_empty] at hC
  obtain ⟨b, hb⟩ := exists_gt a
  use b, hb, (by grind)

/--
Let `f : M → S` be a definable function with `S` finite. For any `a ∈ M`, there is an `i ∈ S` such that `f` is eventually `i` to the left of `a`.
-/
theorem definable_fun_eventually_left {S : Type*} [Finite S] {f : M → S}
    (hf_def : DefinableFunOfFiniteRange L f) :
    ∀ a : M, ∃ i : S, eventuallyLeft (fun x => f x = i) a := by
  sorry

end Ominimal
