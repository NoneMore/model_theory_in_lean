import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.SetNotation
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Closure
import Mathlib.Data.Setoid.Partition

open Set Setoid

namespace Semialgebraic

variable {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

variable [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]

variable (S : Set α)

/-- A component is a set that is either a singleton or an open interval (possibly unbound). -/
def IsComponent : Prop :=
  (∃ (a : α), S = {a}) ∨
  (∃ (a b : α), a ≤ b ∧ S = Ioo a b) ∨
  (∃ (a : α), S = Ioi a) ∨
  (∃ (a : α), S = Iio a) ∨
  S = univ

/-- A semialgebraic set is a finite union of components. -/
def IsSemialgebraic : Prop :=
  ∃ (F : Finset (Set α)), (∀ A ∈ F, IsComponent A) ∧ S = ⋃ i ∈ F, i

omit [Nonempty α] in
/-- The frontier of a singleton set is the singleton itself. -/
lemma frontier_of_singleton (a : α) : frontier {a} = {a} := by
  nth_rewrite 1 [←Icc_self a]
  rw [frontier_Icc, pair_eq_singleton]
  exact le_refl _

omit [Nonempty α] in
/-- A component has a finite frontier. -/
theorem finite_frontier_of_isComponent {S : Set α} (h : IsComponent S) : (frontier S).Finite := by
  unfold IsComponent at h
  rcases h with ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ | univ
  · rw [frontier_of_singleton]
    exact finite_singleton a
  · by_cases h' : a = b
    · simp [h']
    · rw [frontier_Ioo]
      · simp
      · exact lt_of_le_of_ne hab h'
  · rw [frontier_Ioi]
    exact finite_singleton a
  · rw [frontier_Iio]
    exact finite_singleton a
  · simp_all

omit [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
[NoMinOrder α] [NoMaxOrder α] [Nonempty α] in
lemma frontier_subset_union (s t : Set α) : frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  trans (frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t)
  · exact frontier_union_subset s t
  · exact union_subset_union inter_subset_left inter_subset_right

omit [Nonempty α] in
/-- A semialgebraic set has a finite frontier. -/
theorem finite_frointer_of_semialgebriac_set {S : Set α} (h : IsSemialgebraic S) :
  (frontier S).Finite := by
  classical
  obtain ⟨F, hF, hS⟩ := h
  subst hS
  induction F using Finset.induction with
  | empty => simp
  | @insert ha ih _ ih_ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    refine Finite.subset ?_ (frontier_subset_union ha (⋃ x ∈ ih, x))
    apply Finite.union
    · apply finite_frontier_of_isComponent
      apply hF
      exact Finset.mem_insert_self _ _
    · apply ih_ih
      intro A hA
      apply hF
      exact Finset.mem_insert_of_mem hA

lemma infinite_semialgebriac_set_iff_nonempty_interior (h : IsSemialgebraic S) :
  S.Infinite ↔ (interior S).Nonempty := by
  constructor <;> intro h'
  · rw [← self_diff_frontier]
    have : (S \ frontier S).Infinite :=
      Infinite.diff h' (finite_frointer_of_semialgebriac_set h)
    exact Set.Infinite.nonempty this
  · haveI : Nontrivial α := inferInstance
    obtain ⟨a,b,hab,Iab⟩ := IsOpen.exists_Ioo_subset (isOpen_interior) h'
    apply Infinite.mono (interior_subset)
    apply Infinite.mono Iab
    exact Ioo_infinite hab

noncomputable def frontier_of_semialgebriac_set_to_list
  (S : Set α) (hS : IsSemialgebraic S) :
  List α := by
    have : (frontier S).Finite := finite_frointer_of_semialgebriac_set hS
    let ffs : Finset α := Finite.toFinset this
    exact ffs.sort (· ≤ ·)

section partition

variable {n : ℕ} (f : Fin n → α) (hf : StrictMono f)
/--
Given `n` points `f 0, f 1, ..., f (n-1)`, this function generates a partition of `α`
into `2n + 1` sets. The points are assumed to be sorted.
The partition is `(-∞, f 0), {f 0}, (f 0, f 1), {f 1}, ..., {f (n-1)}, (f (n-1), ∞)`.
-/
noncomputable def points_to_partition :Set (Set α) :=
match n with
| 0 => {univ}
| n + 1 =>
  let singletons := ⋃ (i : Fin (n + 1)), {{f i}}
  let intervals_between := ⋃ (i : Fin n), {Ioo (f i.castSucc) (f (Fin.succ i))}
  let first_interval := {Iio (f 0)}
  let last_interval := {Ioi (f (Fin.last n))}
  singletons ∪ intervals_between ∪ first_interval ∪ last_interval

/--
Given a finite set of points `F`, this function induces a partition of `α` into
open intervals and singletons determined by the points in `F`.
-/
noncomputable def finset_to_partition (F : Finset α) : Set (Set α) :=
  let f := Finset.orderEmbOfFin F (rfl)
  points_to_partition f (OrderEmbedding.strictMono f)

lemma disjoint_of_ne {A B : Set α} (h_ne : A ≠ B)
  (hA : A ∈ points_to_partition f hf) (hB : B ∈ points_to_partition f hf) :
  Disjoint A B := by
  cases n with
  | zero =>
    simp [points_to_partition] at hA hB
    subst hA hB
    contradiction
  | succ n =>
    simp [points_to_partition] at hA hB
    have hf' : Monotone f := StrictMono.monotone hf
    rcases hA with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hB with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    all_goals try contradiction
    · refine Disjoint.symm (Iio_disjoint_Ioi_of_le ?_)
      apply hf' (Fin.zero_le _)
    · refine disjoint_singleton_right.mpr ?_
      simp ; exact hf' (Fin.le_last _)
    · refine disjoint_iff_forall_ne.mpr ?_
      intro a ha b hb
      apply ne_of_gt
      have : f j.succ ≤ f (Fin.last n) := hf' (Fin.le_last _)
      exact lt_trans (lt_of_lt_of_le hb.2 this) ha
    · refine Iio_disjoint_Ioi_of_le ?_
      exact hf' (Fin.zero_le _)
    · refine disjoint_singleton_right.mpr ?_
      simp ; exact hf' (Fin.zero_le _)
    · refine disjoint_iff_forall_ne.mpr ?_
      intro a ha b hb
      apply ne_of_lt
      have : f 0 ≤ f j.castSucc := hf' (Fin.zero_le _)
      exact lt_trans ha (lt_of_le_of_lt this hb.1)
    · refine disjoint_singleton_left.mpr ?_
      simp ; exact hf' (Fin.le_last _)
    · refine disjoint_singleton_left.mpr ?_
      simp ; exact hf' (Fin.zero_le _)
    · exact disjoint_singleton.mpr fun a ↦ h_ne (congrArg singleton a)
    · refine disjoint_singleton_left.mpr ?_
      simp ; intro h ; rw [hf.lt_iff_lt] at h
      exact hf' h
    · refine disjoint_iff_forall_ne.mpr ?_
      intro a ha b hb
      apply ne_of_lt
      have : a < f (Fin.last n) := lt_of_lt_of_le ha.2 (hf' (Fin.le_last _))
      exact lt_trans this hb
    · refine disjoint_iff_forall_ne.mpr ?_
      intro a ha b hb
      apply ne_of_gt
      have : f 0 < a := by
        apply lt_of_le_of_lt (hf' (Fin.zero_le _)) ha.1
      exact lt_trans hb this
    · refine disjoint_singleton_right.mpr ?_
      simp ; intro h ; rw [hf.lt_iff_lt] at h
      exact hf' h
    · refine Ioo_disjoint_Ioo.mpr ?_
      by_cases! hij : i = j
      · subst hij
        simp_all only [ne_eq, not_true_eq_false]
      rcases Ne.lt_or_gt hij with h₁ | h₂
      · simp ; right ; left
        exact hf' h₁
      · simp ; left ; right
        exact hf' h₂

lemma points_to_partition_pairwise_disjoint :
  (points_to_partition f hf).PairwiseDisjoint id := by
  rw [pairwiseDisjoint_iff]
  intro A hA B hB h_ne
  contrapose! h_ne
  simp
  apply disjoint_iff_inter_eq_empty.mp
  exact disjoint_of_ne f hf h_ne hA hB

lemma points_to_partition_sUnion_eq_univ :
  ⋃₀ (points_to_partition f hf) = univ := by
  refine sUnion_eq_univ_iff.mpr ?_
  intro a
  cases n with
  | zero =>
    apply Exists.intro
    · apply And.intro
      · rfl
      · simp_all only [mem_univ]
  | succ n =>
    by_cases ha₁ : ∃ i, f i = a
    · rcases ha₁ with ⟨i,hai⟩
      use {f i}
      exact ⟨by simp [points_to_partition], id (Eq.symm hai)⟩
    · by_cases ha₂ : a < f 0
      · use Iio (f 0)
        exact ⟨by simp [points_to_partition], ha₂⟩
      · by_cases ha₃ : f (Fin.last n) < a
        · use Ioi (f (Fin.last n))
          refine ⟨by simp [points_to_partition], ha₃⟩
        have : ∃ i, f i < a ∧ a < f (i+1) := by
          let S := { i : Fin (n + 1) | f i < a }
          have hS_nonempty : S.Nonempty := ⟨0, lt_of_le_of_ne (not_lt.mp ha₂) (fun h => ha₁ ⟨0, h⟩)⟩
          let m : Fin (n + 1) := S.toFinset.max' (toFinset_nonempty.mpr hS_nonempty)
          use m
          have hmS: m ∈ S := by
              rw [←mem_toFinset]
              exact Finset.max'_mem S.toFinset (toFinset_nonempty.mpr hS_nonempty)
          constructor
          · exact hmS
          · by_contra h
            have : f (m + 1) < a  := by
              apply lt_of_le_of_ne (not_lt.mp h)
              push_neg at ha₁
              exact ha₁ (m + 1)
            have : m + 1 ∈ S.toFinset := by
              rw [mem_toFinset]
              exact this
            have succ_of_m_le : m + 1 ≤ m := by
              exact Finset.le_max' S.toFinset (m + 1) this
            have val_of_succ_m : m.val + 1 = (m + 1).val := by
              refine Eq.symm (Fin.val_add_one_of_lt ?_)
              refine Fin.lt_last_iff_ne_last.mpr ?_
              by_contra h
              rw [h] at hmS ; simp [S] at hmS
              exact ha₃ hmS
            have : (m + 1).val ≤ m.val := succ_of_m_le
            rw [←val_of_succ_m] at this
            exact Nat.not_succ_le_self m.val this
        rcases this with ⟨i, hai₁, hai₂⟩
        use Ioo (f i) (f (i + 1))
        constructor
        · simp [points_to_partition]
          right ; right ; right
          have : i < Fin.last n := by
            rw [←hf.lt_iff_lt]
            exact lt_of_lt_of_le hai₁ (not_lt.mp ha₃)
          use Fin.castLT i this
          simp
          congr
          exact Fin.eq_of_val_eq (Eq.symm (Fin.val_add_one_of_lt this))
        · exact ⟨hai₁,hai₂⟩


lemma points_to_partition_is_partition :
  IsPartition (points_to_partition f hf) := by
  -- We proceed by cases on n.
  apply PairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · exact points_to_partition_pairwise_disjoint f hf
  · intro a
    refine mem_sUnion.mp ?_
    rw [points_to_partition_sUnion_eq_univ]
    trivial
  · cases n with
    | zero => simp [points_to_partition] ; exact empty_ne_univ
    | succ n =>
      simp [points_to_partition]
      refine ⟨nonempty_iff_empty_ne.mp nonempty_Ioi, nonempty_iff_empty_ne.mp nonempty_Iio, ?_⟩
      intro i
      refine nonempty_iff_ne_empty'.mp (nonempty_Ioo_subtype ?_)
      apply hf
      exact Fin.castSucc_lt_succ i

lemma finset_to_partition_is_partition (F : Finset α) :
  IsPartition (finset_to_partition F) := by
  unfold finset_to_partition
  exact points_to_partition_is_partition _ _

end partition
/--
A set `S` respects a partition `C` if `S` is the union of some of the sets in `C`.
-/
def RespectsPartition (S : Set α) {C : Set (Set α)} (_ : IsPartition C) : Prop :=
  ∃ F ⊆ C, S = ⋃₀ F

/--
A set `S` respects a partition `C` if for any set `X` in the partition, `X` is either a subset
of `S` or disjoint from `S`.
-/
def RespectsPartition' (S : Set α) {C : Set (Set α)} (_ : IsPartition C) : Prop :=
  ∀ X ∈ C, X ⊆ S ∨ Disjoint X S

lemma respects_partition_iff_respects_partition' (S : Set α) {C : Set (Set α)}
    (hC : IsPartition C) :
    RespectsPartition S hC ↔ RespectsPartition' S hC := by
  constructor <;> intro h
  · intro X hX
    obtain ⟨F,hF,hS⟩ := h
    by_cases hX' : X ⊆ S
    · left
      exact hX'
    · right
      rw [hS, disjoint_sUnion_right]
      intro Y hYF
      apply hC.pairwiseDisjoint hX (hF hYF)
      rintro rfl
      apply hX'
      rw [hS]
      exact subset_sUnion_of_mem hYF
  · use {X | X ∈ C ∧ X ⊆ S}
    constructor
    · rintro X ⟨hXC, _⟩; exact hXC
    · ext x
      constructor <;> intro hx
      · refine mem_sUnion.mpr ?_
        simp [RespectsPartition'] at h
        rw [IsPartition] at hC
        obtain ⟨t,ht,hxt⟩ := ExistsUnique.exists (hC.2 x)
        use t
        refine ⟨⟨ht,?_⟩,hxt⟩
        rcases h t ht with h₁ | h₂
        · exact h₁
        · exfalso
          apply disjoint_left.mp at h₂
          have : x ∉ S := h₂ hxt
          exact this hx
      · rw [mem_sUnion] at hx
        rcases hx with ⟨t,ht,hxt⟩
        simp at ht
        exact ht.2 hxt

/-- If a set `S` respects a partition `C`, it also respects any refinement `D` of `C`. -/
lemma respects_partition_of_refinement {S : Set α} {C D : Set (Set α)}
    (hC : IsPartition C) (hD : IsPartition D) (hCD : ∀ d ∈ D, ∃ c ∈ C, d ⊆ c)
    (hS : RespectsPartition S hC) :
    RespectsPartition S hD := by
  rw [respects_partition_iff_respects_partition'] at hS ⊢
  intro d hd
  rcases hCD d hd with ⟨c, hc, hdc⟩
  cases hS c hc with
  | inl hSc => left ; exact subset_trans hdc hSc
  | inr hSc =>
    right
    exact Disjoint.mono_left hdc hSc

/-- If a finite set `A` is a subset of `B`, then the partition induced by `B`
    is a refinement of the partition induced by `A`. -/
lemma finset_to_partition_is_refinement_of_subset (A B : Finset α) (hAB : A ⊆ B) :
    ∀ d ∈ finset_to_partition B, ∃ c ∈ finset_to_partition A, d ⊆ c := by
  intro d hd
  by_cases hA_empty : A = ∅
  · rw [hA_empty] ; simp [finset_to_partition, points_to_partition]
  simp only [finset_to_partition, points_to_partition] at hd
  split at hd
  · have hB_card_pos : B.card ≠ 0 := by
      refine Finset.card_ne_zero.mpr ?_
      have hA_ne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
      exact Finset.Nonempty.mono hAB hA_ne
    exfalso
    (expose_names; exact hB_card_pos heq)
  · rename_i n f hf heq heq₂ heq₃
    have : range f = B := by sorry
    sorry

/-- If a set `S` is a component, then it respects a partition induced by some finite set. -/
lemma respects_partition_of_is_component {S : Set α} (hS : IsComponent S) :
  ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A) := by
  sorry

/-- If two sets `S` and `T` each respect a partition induced by some finite set,
    then their union `S ∪ T` also respects a partition induced by some finite set. -/
lemma respects_partition_of_union {S T : Set α}
    (hS : ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A))
    (hT : ∃ (B : Finset α), RespectsPartition T (finset_to_partition_is_partition B)) :
    ∃ (C : Finset α), RespectsPartition (S ∪ T) (finset_to_partition_is_partition C) := by
  sorry

/-- For any semialgebraic set `S`, there exists some finite set `A`
    such that `S` respects the partition induced by `A`. -/
lemma exists_finset_respects_partition_of_semialgebriac (S : Set α) (hS : IsSemialgebraic S) :
  ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A) := by
  sorry

/-- For semialgebraic set `S`, there exists some finite set `A` of minimal size,
    such that `S` respects the partition induced by `A` -/
lemma min_card_finset_respects_partition_of_semialgebriac (S : Set α) (hS : IsSemialgebraic S) :
  ∃ (A : Finset α),
    RespectsPartition S (finset_to_partition_is_partition A) ∧
    ∀ (B : Finset α),
      RespectsPartition S (finset_to_partition_is_partition B) →
        A.card ≤ B.card := by
  sorry

/-- A semialgebraic set respects the partition induced by its finite frontier -/
lemma semialgebraic_respects_frontier_partition (S : Set α) (hS : IsSemialgebraic S) :
    RespectsPartition S (finset_to_partition_is_partition
      (finite_frointer_of_semialgebriac_set hS).toFinset) := by
  sorry

end Semialgebraic
