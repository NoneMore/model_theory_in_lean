import Mathlib.ModelTheory.Definability

open Set

namespace FirstOrder.Language

open FirstOrder Language

variable {M : Type*} (L : Language) [L.Structure M]

def UDefinable₁ (s : Set M) : Prop :=
  univ.Definable₁ L s

def UDefinable₂ (s : Set (M × M)) : Prop :=
  (univ : Set M).Definable₂ L s

/-- A function `f : A → M` is U-definable if its graph is a U-definable set. -/
def UDefinableFun {A : Set M} (f : A → M) : Prop :=
  UDefinable₂ L ((fun (a : A) => (a.val, f a)) '' univ)

/-- A function `f : M → S` is definable if for every `s : S`, the preimage `f⁻¹' {s}` is a U-definable set. -/
def DefinableFunOfFiniteRange {S : Type*} (f : M → S) : Prop :=
  ∀ s : S, UDefinable₁ L (f⁻¹' {s})

lemma definable_con {L : Language} [L.Structure M] (a : M) :
    univ.Definable L {v : Fin 1 → M | v 0 = a} := by
  rw [Set.definable_iff_exists_formula_sum]
  let tx : L.Term ((↑univ : Set M) ⊕ Fin 1) :=
    Term.var (Sum.inr (0 : Fin 1))
  let ta : L.Term ((↑univ : Set M) ⊕ Fin 1) :=
    Term.var (Sum.inl ⟨a,trivial⟩)
  use Term.equal tx ta
  simp [Term.realize, tx, ta]

lemma definable_exists {L : Language} [L.Structure M] {n : ℕ} {p : (Fin (n + 1) → M) → Prop}
  {A : Set M} (p_def : A.Definable L {v | p v}) :
    A.Definable L { v : Fin n → M | ∃ x, p (Fin.snoc v x)} := by
  convert p_def.image_comp (Fin.castSucc)
  ext v
  simp only [mem_setOf_eq, mem_image]
  constructor
  · intro ⟨x, hx⟩
    refine ⟨_, hx, ?_⟩
    simp
  · rintro ⟨x, h, rfl⟩
    exists x (Fin.last n)
    convert h
    ext i
    cases i using Fin.lastCases with simp

lemma _root_.Set.Definable.specialize_last {L : Language} [L.Structure M]
    {A : Set M} {n : ℕ} {S : Set (Fin (n + 1) → M)}
    (hS : A.Definable L S) (a : A) :
    A.Definable L {v : Fin n → M | Fin.snoc v a ∈ S} := by
  obtain ⟨φ, hφ⟩ := hS
  let f : Fin (n + 1) → L[[↑A]].Term (Fin n) := Fin.lastCases (L.con a).term (Term.var)
  use (φ.subst f)
  ext v ; simp [hφ,Formula.Realize]
  apply iff_of_eq ; congr
  ext i
  induction i using Fin.lastCases <;> simp [f]

/-- The fiber of a definable (partial) function is definable. -/
lemma udefinable_fiber_of_UDefFun {A : Set M} {f : A → M} (f_def : L.UDefinableFun f) (b : M) :
    UDefinable₁ L (Subtype.val '' {x | f x = b}) := by
  simp [UDefinable₁,Definable₁]
  simp [UDefinableFun, UDefinable₂, Definable₂, Definable] at f_def
  choose φ hφ using f_def
  have : univ.Definable L {v : Fin 1 → M | ∃ y, φ.Realize (Fin.snoc v y) ∧ y = b} := by
    have : univ.Definable L {v : Fin 2 → M | φ.Realize v} := by
      simp [Definable] ; use φ
    let S_def := (Definable.inter this (Definable.preimage_comp ![1] (definable_con b)))
    simp [Set.inter_def] at S_def
    let S'_def := definable_exists S_def
    convert S'_def
  convert this using 1
  ext v ; simp
  change _ ↔ (Fin.snoc v b) ∈ setOf φ.Realize
  simp [←hφ,Fin.snoc]

end FirstOrder.Language
