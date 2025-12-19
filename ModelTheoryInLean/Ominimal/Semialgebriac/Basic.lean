import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.SetNotation
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Closure
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith

open Set Setoid

namespace Set.Semialgebraic

variable {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

variable [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]

section

variable (S : Set α) (α)

inductive Component where
  | pt   (a : α)
  | oo   (a b : α) (hab : a ≤ b)
  | oi   (a : α)
  | io   (a : α)
  | univ

@[simp]
def Component.toSet : Component α → Set α
  | .pt a      => {a}
  | .oo a b _  => Ioo a b
  | .oi a      => Ioi a
  | .io a      => Iio a
  | .univ      => Set.univ

variable {α}

@[simp]
def IsComponent : Prop := ∃ c : Component α, S = c.toSet

@[simp]
def IsSemialgebraic : Prop :=
  ∃ F : Finset (Component α), S = ⋃ c ∈ F, (c.toSet)

omit [Nonempty α] in
/-- The frontier of a singleton set is the singleton itself. -/
lemma frontier_of_singleton (a : α) : frontier {a} = {a} := by
  nth_rewrite 1 [←Icc_self a]
  rw [frontier_Icc, pair_eq_singleton]
  exact le_refl _

omit [Nonempty α] in
/-- A component has a finite frontier. -/
theorem finite_frontier_of_isComponent {S : Set α} (h : IsComponent S) :
    (frontier S).Finite := by
  obtain ⟨c,rfl⟩ := h
  cases c with
  | pt a => simp [frontier_of_singleton]
  | oo a b hab =>
      by_cases h' : a = b
      · simp [h']
      · simp [frontier_Ioo (lt_of_le_of_ne hab h')]
  | oi a => simp
  | io a => simp
  | univ => simp

omit [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
[NoMinOrder α] [NoMaxOrder α] [Nonempty α] in
lemma frontier_subset_union (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  trans (frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t)
  · exact frontier_union_subset s t
  · exact union_subset_union inter_subset_left inter_subset_right

omit [Nonempty α] in
/-- A semialgebraic set has a finite frontier. -/
theorem finite_frontier_of_semialgebriac_set
    {S : Set α} (h : IsSemialgebraic S) :
    (frontier S).Finite := by
  classical
  obtain ⟨F,rfl⟩ := h
  refine Finset.induction_on F (by simp) ?_
  intro c F hc hF
  rw [Finset.set_biUnion_insert c F (Component.toSet α)]
  refine Finite.subset ?_ (frontier_subset_union _ _)
  refine Finite.union ?_ hF
  exact finite_frontier_of_isComponent (by exists c)

end

section parition

lemma card_filter_lt_orderEmbOfFin (F : Finset α) (k : Fin (F.card)) :
    (F.filter (· < F.orderEmbOfFin rfl k)).card = k.val := by
  conv =>
    enter [1, 1, 2]
    rw [← F.map_orderEmbOfFin_univ rfl]
  rw [Finset.filter_map, Finset.card_map]
  simp only [RelEmbedding.coe_toEmbedding, Function.comp_def, OrderEmbedding.lt_iff_lt]
  rw [← k.card_Iio]
  congr
  exact Finset.filter_gt_eq_Iio

variable (F : Finset α) (x : α)

def rank : ℕ :=
  2 * (F.filter (fun y => y < x)).card + (if x ∈ F then 1 else 0)

lemma rank_bound : rank F x < 2 * F.card + 1 := by
  simp only [rank]
  split_ifs with hx
  · refine Nat.add_lt_add_right ?_ 1
    have : {y ∈ F | y < x}.card < F.card := by
      refine Finset.card_lt_card ?_
      refine Finset.filter_ssubset.mpr ?_
      exists x, hx
      exact lt_irrefl x
    linarith
  · have : {y ∈ F | y < x}.card ≤ F.card := by
      exact Finset.card_filter_le F fun y ↦ y < x
    linarith

def rankFin : Fin (2 * F.card + 1) :=
  ⟨rank F x, rank_bound F x⟩

def partitionComponent (k : Fin (2 * F.card + 1)) : Set α :=
  { x | rankFin F x = k }

def partition_of_finset : Set (Set α) :=
  Set.range (partitionComponent F)

lemma partitionComponent_nonempty (k : Fin (2 * F.card + 1)) :
    (partitionComponent F k).Nonempty := by
  by_cases hF : F.Nonempty
  · rw [← Finset.card_pos] at hF
    have : NeZero F.card := NeZero.of_pos hF
    let f := F.orderEmbOfFin rfl
    by_cases hodd : k.val % 2 = 1
    · let n := k.val / 2
      have hn : n < F.card := by omega
      exists f ⟨n, hn⟩
      simp only [partitionComponent, rankFin, rank, mem_setOf_eq]
      split_ifs with hmem
      · congr 1
        suffices h : {y ∈ F | y < ↑(f ⟨n, hn⟩)}.card = n by
          rw [h] ; omega
        rw [card_filter_lt_orderEmbOfFin]
      · exfalso
        exact hmem (Finset.orderEmbOfFin_mem F rfl ⟨n, hn⟩)
    · let n := k.val / 2
      have heven : k.val = 2 * n := by omega
      by_cases hn : n = 0
      · obtain ⟨y,hy⟩ := exists_lt (f ⟨0,hF⟩)
        exists y
        simp only [partitionComponent, mem_setOf_eq]
        rw [show k = 0 by exact Fin.val_eq_zero_iff.mp (by omega)]
        simp only [rankFin, rank, Fin.mk_eq_zero, Nat.add_eq_zero_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_lt, false_or,
          ite_eq_right_iff, one_ne_zero, imp_false]
        constructor
        · intro x hx
          rw [←F.image_orderEmbOfFin_univ rfl, Finset.mem_image] at hx
          obtain ⟨l,hl,rfl⟩ := hx
          apply le_of_eq_or_lt
          right
          apply lt_of_lt_of_le hy
          simp [f]
        · contrapose! hy
          rw [←F.image_orderEmbOfFin_univ rfl, Finset.mem_image] at hy
          obtain ⟨l,hl,rfl⟩ := hy
          simp [f]
      · by_cases hn' : n < F.card
        · have lt : f ⟨n - 1, by omega⟩ < f ⟨n,hn'⟩ := by
            simp only [OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk, tsub_lt_self_iff, zero_lt_one,
              and_true]
            exact Nat.zero_lt_of_ne_zero hn
          obtain ⟨y,hy⟩ := exists_between lt
          use y
          simp only [partitionComponent, rankFin, mem_setOf_eq]
          ext
          simp only [rank]
          split_ifs with hy'
          · rw [heven]
            exfalso
            rw [←F.image_orderEmbOfFin_univ rfl, Finset.mem_image] at hy'
            obtain ⟨l,hl,rfl⟩ := hy'
            simp only [OrderEmbedding.lt_iff_lt, f] at hy
            have : l ≤ ⟨n - 1, by omega⟩ := Nat.le_sub_one_of_lt hy.2
            omega
          · suffices h : {y_1 ∈ F | y_1 < y}.card = n by
              omega
            rw [show n = (⟨n,hn'⟩ : Fin F.card).val by simp]
            rw [←card_filter_lt_orderEmbOfFin F ⟨n,hn'⟩]
            congr 1
            ext x
            simp only [Finset.mem_filter, and_congr_right_iff]
            intro hx
            constructor
            · intro hxy
              refine lt_trans hxy hy.2
            · intro hxF
              refine lt_of_le_of_lt ?_ hy.1
              rw [←F.image_orderEmbOfFin_univ rfl, Finset.mem_image] at hx
              obtain ⟨l,hl,rfl⟩ := hx
              simp only [OrderEmbedding.lt_iff_lt, OrderEmbedding.le_iff_le, f] at hxF ⊢
              exact Nat.le_sub_one_of_lt hxF
        · sorry
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    simp only [partitionComponent, Finset.card_empty, Nat.mul_zero, Nat.reduceAdd, rankFin, rank,
      Finset.filter_empty, mul_zero, Finset.notMem_empty, ↓reduceIte, add_zero, Fin.zero_eta,
      Fin.isValue]
    have ⟨a⟩ : Nonempty α := inferInstance
    exists a
    simp only [Fin.isValue, mem_setOf_eq]
    exact Eq.symm (Fin.fin_one_eq_zero k)

example : IsPartition (partition_of_finset F) := by
  refine PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ ?_ ?_
  · rw [pairwiseDisjoint_iff]
    rintro A ⟨k,rfl⟩ B ⟨l,rfl⟩ ⟨x,hx⟩
    simp [partitionComponent] at *
    grind
  · simp [partition_of_finset,partitionComponent]
  · sorry

end parition


end Semialgebraic
