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
noncomputable def sequence_to_partition :Set (Set α) :=
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
  sequence_to_partition (Finset.orderEmbOfFin F (rfl)) (OrderEmbedding.strictMono (Finset.orderEmbOfFin F (rfl)))

lemma disjoint_of_ne {A B : Set α} (h_ne : A ≠ B)
  (hA : A ∈ sequence_to_partition f hf) (hB : B ∈ sequence_to_partition f hf) :
  Disjoint A B := by
  cases n with
  | zero =>
    simp [sequence_to_partition] at hA hB
    subst hA hB
    contradiction
  | succ n =>
    simp [sequence_to_partition] at hA hB
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

lemma sequence_to_partition_pairwise_disjoint :
  (sequence_to_partition f hf).PairwiseDisjoint id := by
  rw [pairwiseDisjoint_iff]
  intro A hA B hB h_ne
  contrapose! h_ne
  simp
  apply disjoint_iff_inter_eq_empty.mp
  exact disjoint_of_ne f hf h_ne hA hB

lemma sequence_to_partition_sUnion_eq_univ :
  ⋃₀ (sequence_to_partition f hf) = univ := by
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
      exact ⟨by simp [sequence_to_partition], id (Eq.symm hai)⟩
    · by_cases ha₂ : a < f 0
      · use Iio (f 0)
        exact ⟨by simp [sequence_to_partition], ha₂⟩
      · by_cases ha₃ : f (Fin.last n) < a
        · use Ioi (f (Fin.last n))
          refine ⟨by simp [sequence_to_partition], ha₃⟩
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
        · simp [sequence_to_partition]
          right ; right ; right
          have : i < Fin.last n := by
            rw [←hf.lt_iff_lt]
            exact lt_of_lt_of_le hai₁ (not_lt.mp ha₃)
          use Fin.castLT i this
          simp
          congr
          exact Fin.eq_of_val_eq (Eq.symm (Fin.val_add_one_of_lt this))
        · exact ⟨hai₁,hai₂⟩


lemma sequence_to_partition_is_partition :
  IsPartition (sequence_to_partition f hf) := by
  -- We proceed by cases on n.
  apply PairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · exact sequence_to_partition_pairwise_disjoint f hf
  · intro a
    refine mem_sUnion.mp ?_
    rw [sequence_to_partition_sUnion_eq_univ]
    trivial
  · cases n with
    | zero => simp [sequence_to_partition] ; exact empty_ne_univ
    | succ n =>
      simp [sequence_to_partition]
      refine ⟨nonempty_iff_empty_ne.mp nonempty_Ioi, nonempty_iff_empty_ne.mp nonempty_Iio, ?_⟩
      intro i
      refine nonempty_iff_ne_empty'.mp (nonempty_Ioo_subtype ?_)
      apply hf
      exact Fin.castSucc_lt_succ i

lemma finset_to_partition_is_partition (F : Finset α) :
  IsPartition (finset_to_partition F) := by
  exact sequence_to_partition_is_partition _ _

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
def RespectsPartition' (S : Set α) {C : Set (Set α)} (hC : IsPartition C) : Prop :=
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

/-- If the range of a strictly increasing sequence `f` is a subset of the range of `g`,
    then the partition induced by `g` is a refinement of the partition induced by `f`. -/
lemma partition_is_refinement_of_range_subset {n m : ℕ} {f : Fin n → α} {g : Fin m → α}
    (hf : StrictMono f) (hg : StrictMono g) (h_range : Set.range f ⊆ Set.range g) :
    ∀ d ∈ sequence_to_partition g hg, ∃ c ∈ sequence_to_partition f hf, d ⊆ c := by
  intro d hd
  have hnm : n ≤ m := by
    have card_f : Fintype.card (Set.range f) = n := by
      simp [card_range_of_injective hf.injective]
    have card_g : Fintype.card (Set.range g) = m := by
      simp [card_range_of_injective hg.injective]
    have : Fintype.card (Set.range f) ≤ Fintype.card (Set.range g) := by exact card_le_card h_range
    rwa [card_f, card_g] at this
  cases n with
  | zero =>
    simp [sequence_to_partition]
  | succ n =>
    cases m with
    | zero => exfalso ; exact Nat.not_succ_le_zero n hnm
    | succ m =>
      simp [sequence_to_partition] at *
      rcases hd with (h_Ioi | h_Iio | ⟨y, h_pt⟩ | ⟨y, h_Ioo⟩)
      · left
        simp [h_Ioi]
        obtain ⟨i, hi⟩ := h_range (mem_range_self (Fin.last n))
        rw [←hi]
        exact StrictMono.monotone hg (Fin.le_last i)
      · right ; left
        simp [h_Iio]
        obtain ⟨i, hi⟩ := h_range (mem_range_self 0)
        rw [←hi]
        exact StrictMono.monotone hg (Fin.zero_le i)
      · by_cases h : ∃ j, f j = g y
        · rcases h with ⟨j,hj⟩
          right ; right ;
          use {f j}
          constructor
          · left ; use j
          rw [←h_pt, hj]
        simp at h
        let gyL := { i | f i < g y}
        let gyR := { i | f i > g y}
        by_cases hL : gyL = ∅
        · right ; left
          simp [h_pt.symm]
          contrapose! hL
          use 0
          exact lt_of_le_of_ne hL (h 0)
        by_cases hR : gyR = ∅
        · left
          simp [h_pt.symm]
          contrapose! hR
          use Fin.last n
          refine lt_of_le_of_ne hR ?_
          exact fun a ↦ h (Fin.last n) (id (Eq.symm a))
        right ; right
        apply nonempty_iff_ne_empty.mpr at hL
        let x := gyL.toFinset.max' (toFinset_nonempty.mpr hL)
        have hx : x ∈ gyL := by
          rw [←mem_toFinset]
          exact Finset.max'_mem gyL.toFinset (toFinset_nonempty.mpr hL)
        have hx' : x < Fin.last n := by
          apply lt_of_le_of_ne (Fin.le_last x)
          intro hxeq
          obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.mpr hR
          have : f x < f j := lt_trans hx hj
          rw [hf.lt_iff_lt, hxeq] at this
          exact (lt_of_le_of_lt (Fin.le_last j) this).false
        use Ioo (f x) (f (x + 1))
        constructor
        · right
          let x' := Fin.castLT x hx'
          use x'
          congr
          refine Fin.eq_of_val_eq ?_
          exact Eq.symm (Fin.val_add_one_of_lt hx')
        subst h_pt ; simp
        refine ⟨hx,?_⟩
        apply lt_of_le_of_ne
        · by_contra h'
          have : x + 1 ∈ gyL := lt_of_not_ge h'
          have h_le : x + 1 ≤ x := Finset.le_max' (gyL.toFinset) (x+1) (Set.mem_toFinset.mpr this)
          contrapose! h_le
          exact Fin.lt_add_one_iff.mpr hx'
        exact fun a ↦ h (x + 1) (id (Eq.symm a))
      · subst h_Ioo
        obtain ⟨i,hi⟩ := mem_range.mp (h_range (mem_range_self 0))
        obtain ⟨j,hj⟩ := mem_range.mp (h_range (mem_range_self (Fin.last n)))
        rw [←hi, ←hj]
        by_cases hl : y.succ ≤ i
        · right ; left ; simp [Ioo,Iio] ; intro a ha ha'
          exact lt_of_lt_of_le ha' (hg.monotone hl)
        by_cases hr : j ≤ y.castSucc
        · left ; simp [Ioo,Ioi] ; intro a ha ha'
          refine lt_of_le_of_lt (hg.monotone hr) ha
        right ; right
        let yL := { i | f i ≤ g y.castSucc }
        let yR := { i | g y.succ ≤ f i }
        have hyL : yL.Nonempty := by
          have : 0 ∈ yL := by
            simp [yL] ; rw [←hi] ; apply hg.monotone
            exact Fin.not_lt.mp hl
          exact nonempty_of_mem this
        let x := yL.toFinset.max' (toFinset_nonempty.mpr hyL)
        have hx : x ∈ yL := by
          rw [←mem_toFinset]
          exact Finset.max'_mem yL.toFinset (toFinset_nonempty.mpr hyL)
        have hx' : x < Fin.last n := by
          rw [←hf.lt_iff_lt, ←hj]
          exact lt_of_le_of_lt hx (hg (Fin.not_le.mp hr))
        use Ioo (f x) (f (x + 1))
        constructor
        · right
          use Fin.castLT x hx'
          simp ; congr
          refine Fin.eq_of_val_eq ?_
          exact Eq.symm (Fin.val_add_one_of_lt hx')
        simp [Ioo] ; intro a ha ha'
        constructor
        · exact lt_of_le_of_lt hx ha
        · apply lt_of_lt_of_le ha'
          by_contra h
          apply lt_of_not_ge at h
          obtain ⟨k,hk⟩ := mem_range.mp (h_range (mem_range_self (x + 1)))
          rw [←hk] at h
          apply hg.lt_iff_lt.mp at h
          apply Fin.le_castSucc_iff.mpr at h
          apply hg.monotone at h
          rw [hk] at h
          change (x + 1) ∈ yL at h
          have : x + 1 ≤ x := Finset.le_max' (yL.toFinset) (x+1) (Set.mem_toFinset.mpr h)
          contrapose! this
          exact Fin.lt_add_one_iff.mpr hx'

/-- If a finset `A` is a subset of `B`, then the range of the induced strictly increasing
    sequence from `A` is a subset of the range of the induced sequence from `B`. -/
lemma range_orderEmbOfFin_subset_of_subset (A B : Finset α) (hAB : A ⊆ B) :
    Set.range (Finset.orderEmbOfFin A rfl) ⊆ Set.range (Finset.orderEmbOfFin B rfl) := by
  simp ; exact hAB

/-- If a finite set `A` is a subset of `B`, then the partition induced by `B`
    is a refinement of the partition induced by `A`. -/
lemma finset_to_partition_is_refinement_of_subset (A B : Finset α) (hAB : A ⊆ B) :
    ∀ d ∈ finset_to_partition B, ∃ c ∈ finset_to_partition A, d ⊆ c := by
  unfold finset_to_partition
  let fA := Finset.orderEmbOfFin A rfl
  let fB := Finset.orderEmbOfFin B rfl
  have hfA : StrictMono fA := OrderEmbedding.strictMono fA
  have hfB : StrictMono fB := OrderEmbedding.strictMono fB
  have h_range : Set.range fA ⊆ Set.range fB := by
    exact range_orderEmbOfFin_subset_of_subset A B hAB
  exact partition_is_refinement_of_range_subset hfA hfB h_range

/-- If a set `S` respects the partition induced by `A`, and `A ⊆ B`,
    then `S` also respects the partition induced by `B`. -/
lemma respects_partition_of_subset {S : Set α} {A B : Finset α} (hAB : A ⊆ B)
    (hS : RespectsPartition S (finset_to_partition_is_partition A)) :
    RespectsPartition S (finset_to_partition_is_partition B) := by
  exact respects_partition_of_refinement
    (finset_to_partition_is_partition A)
    (finset_to_partition_is_partition B)
    (finset_to_partition_is_refinement_of_subset A B hAB)
    hS

/-- If two sets `S` and `T` both respect a partition `C`,
    then their union `S ∪ T` also respects `C`. -/
lemma respects_partition_union {S T : Set α} {C : Set (Set α)} (hC : IsPartition C)
    (hS : RespectsPartition S hC) (hT : RespectsPartition T hC) :
    RespectsPartition (S ∪ T) hC := by
  rw [respects_partition_iff_respects_partition'] at *
  simp [RespectsPartition'] at *
  grind

/-- If two sets `S` and `T` each respect a partition induced by some finite set,
    then their union `S ∪ T` also respects a partition induced by some finite set. -/
lemma respects_partition_of_union {S T : Set α}
    (hS : ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A))
    (hT : ∃ (B : Finset α), RespectsPartition T (finset_to_partition_is_partition B)) :
    ∃ (C : Finset α), RespectsPartition (S ∪ T) (finset_to_partition_is_partition C) := by
  rcases hS with ⟨A, hA⟩
  rcases hT with ⟨B, hB⟩
  use A ∪ B
  have hA' : A ⊆ A ∪ B := Finset.subset_union_left
  have hB' : B ⊆ A ∪ B := Finset.subset_union_right
  apply respects_partition_union
  · exact respects_partition_of_subset hA' hA
  · exact respects_partition_of_subset hB' hB

/-- A singleton set respects the partition induced by itself. -/
lemma respects_partition_singleton (a : α) :
  RespectsPartition {a} (finset_to_partition_is_partition {a}) := by
  rw [respects_partition_iff_respects_partition', RespectsPartition']
  intro X hX
  rcases hX with ((h | h) | rfl) | rfl
  · simp at h ; subst h ; left ; simp
    exact Finset.orderEmbOfFin_singleton a 0
  · simp at h
  · right ; simp ; apply le_of_eq
    exact Finset.orderEmbOfFin_singleton a 0
  · right ; simp ; apply le_of_eq ; symm
    exact Finset.orderEmbOfFin_singleton a 0

/-- If a set `S` is a component, then it respects a partition induced by some finite set. -/
lemma respects_partition_of_is_component {S : Set α} (hS : IsComponent S) :
  ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A) := by
  rcases hS with ⟨a,rfl⟩ | ⟨a,b,hab,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ | rfl
  · use {a}
    exact respects_partition_singleton a
  · use {a,b}
    rw [respects_partition_iff_respects_partition', RespectsPartition']
    intro X hX
    by_cases hab' : a = b
    · simp [hab']
    apply hab.lt_of_ne at hab'
    rw [finset_to_partition, sequence_to_partition.eq_def] at hX
    split at hX
    · grind
    rename_i n f hf hn heq heq'
    have : n = 1 := by
      have : Finset.card {a,b} = 2 := by grind
      grind
    subst this
    have : range (Finset.orderEmbOfFin {a, b} rfl) = ({a,b} : Finset α) := Finset.range_orderEmbOfFin {a, b} rfl
    have f_range : range f = {a,b} := by grind
    have h_mono : f 0 < f 1 := hf (by grind)
    have h0_mem : f 0 ∈ ({a, b} : Set α) := by rw [← f_range]; exact mem_range_self 0
    have h1_mem : f 1 ∈ ({a, b} : Set α) := by rw [← f_range]; exact mem_range_self 1
    have f0 : f 0 = a := by grind
    have f1 : f 1 = b := by grind
    rcases hX with ((h | h) | rfl) | rfl
    · simp at h
      rcases h with h | h <;> right <;> simp [←h, ←f0, ←f1]
    · simp at h ; rcases h with h | h ; simp [←f0, ←f1]
    · right ; simp [←f0, ←f1]
      refine disjoint_left.mpr ?_
      intro x hx hx'
      grind
    · simp [←f0, ←f1] ; right
      refine disjoint_left.mpr ?_
      intro x hx hx'
      grind
  · use {a}
    rw [respects_partition_iff_respects_partition', RespectsPartition']
    intro X hX
    rcases hX with ((h | h) | rfl) | rfl
    · simp at h ; rw [←h] ; right ; simp ; apply le_of_eq
      exact Finset.orderEmbOfFin_singleton a 0
    · simp at h
    · simp ; right ; apply le_of_eq
      exact Finset.orderEmbOfFin_singleton a 0
    · simp ; left ; apply le_of_eq ; symm
      exact Finset.orderEmbOfFin_singleton a 0
  · use {a}
    rw [respects_partition_iff_respects_partition', RespectsPartition']
    intro X hX
    rcases hX with ((h | h) | rfl) | rfl
    · simp at h ; rw [←h] ; right ; simp ; apply le_of_eq ; symm
      exact Finset.orderEmbOfFin_singleton a 0
    · simp at h
    · simp ; left ; apply le_of_eq
      exact Finset.orderEmbOfFin_singleton a 0
    · simp ; right ; apply le_of_eq ; symm
      exact Finset.orderEmbOfFin_singleton a 0
  · use ∅
    simp [respects_partition_iff_respects_partition', RespectsPartition']

/-- For any semialgebraic set `S`, there exists some finite set `A`
    such that `S` respects the partition induced by `A`. -/
lemma exists_finset_respects_partition_of_semialgebriac (S : Set α) (hS : IsSemialgebraic S) :
  ∃ (A : Finset α), RespectsPartition S (finset_to_partition_is_partition A) := by
  classical
  obtain ⟨F, hF_comp, rfl⟩ := hS
  induction F using Finset.induction with
  | empty =>
    use ∅
    rw [respects_partition_iff_respects_partition']
    intro X hX
    have : X = univ := by
      simp [finset_to_partition, sequence_to_partition] at hX
      exact hX
    rw [this] ; right ; simp
  | @insert s G _ ih =>
    have hG: ∀ A ∈ G, IsComponent A := by grind
    have hs : IsComponent s := by grind
    simp
    exact respects_partition_of_union (respects_partition_of_is_component hs) (ih hG)

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
