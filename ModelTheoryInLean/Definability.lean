import Mathlib.ModelTheory.Definability

open Set
/-
TODO:
1.  Defining Formula
    -   `IsDefiningFormula {L : Language} (φ : L.Formula (Fin 2)) : Prop`
    -   A binary formula `φ(x, y)` is a defining formula iff for any `x, y₁, y₂`, `φ(x, y₁) ∧ φ(x, y₂)` implies `y₁ = y₂`.
    -   Implementation: `∀ (x y₁ y₂ : M), (Realize φ ![x, y₁]) ∧ (Realize φ ![x, y₂]) → y₁ = y₂`

2.  Domain and Range
    -   `domain {L : Language} (φ : L.Formula (Fin 2)) : Set M`
    -   `range {L : Language} (φ : L.Formula (Fin 2)) : Set M`
    -   Implementation:
        -   `domain φ := {x | ∃ y, Realize φ ![x, y]}`
        -   `range φ := {y | ∃ x, Realize φ ![x, y]}`

3.  Function from a Defining Formula
    -   `funOfDefiningFormula {L : Language} {φ : L.Formula (Fin 2)} (hφ : IsDefiningFormula φ) : (domain φ) → (range φ)`
    -   Implementation: Use `Classical.choose` on `∃ y, Realize φ ![x, y]`. Uniqueness is guaranteed by `IsDefiningFormula`.

4.  (Proposition) The constructed function is UDefinable_fun
    -   `funOfDefiningFormula_is_UDefinable : UDefinable_fun (funOfDefiningFormula hφ)`
    -   Implementation: Prove the graph of the function, `{ (x, y) | x ∈ domain φ ∧ y = (funOfDefiningFormula hφ) x }`, is a definable set. This set is equivalent to the set defined by `φ`.

5.  Generalization to n-ary functions
    -   `IsNaryDefiningFormula {L : Language} (n : ℕ) (φ : L.Formula (Fin (n + 1))) : Prop`
    -   `naryDomain {L : Language} {n : ℕ} (φ : L.Formula (Fin (n + 1))) : Set (Fin n → M)`
    -   `naryRange {L : Language} {n : ℕ} (φ : L.Formula (Fin (n + 1))) : Set M`
    -   `funOfNaryDefiningFormula`
    -   `funOfNaryDefiningFormula_is_UDefinable`
    -   Implementation: Replace `x` with a vector of type `Fin n → M`.

6.  Indicator Function
    -   `noncomputable indicator {M : Type*} (p : M → Prop) (a : M) : ℤ`
    -   Implementation: `if p a then 1 else 0`.

7.  Comparator Function
    -   `comparator {M : Type*} [LinearOrder M] (a b : M) : ℤ`
    -   Implementation: `match cmp a b with | Ordering.lt => -1 | Ordering.eq => 0 | Ordering.gt => 1`.
-/

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

/-- The fiber of a definable (partial) function is definable. -/
lemma udefinable_fiber_of_UDefFun {A : Set M} {f : A → M} (hf : L.UDefinableFun f) (y : M) :
  UDefinable₁ L (Subtype.val '' (f⁻¹' {y})) := by
    -- From `hf`, we get a formula `φ` that defines the graph of `f`.
    simp [UDefinableFun, UDefinable₂, Definable₂, Definable] at hf
    choose φ hφ using hf
    simp [UDefinable₁, Definable₁, Definable]

    let t_y : L[[↑(univ : Set M)]].Term (Fin 1) := Term.func (L.con ⟨y,Set.mem_univ y⟩) ![]
    let φ' : L[[↑univ]].Formula (Fin 1) := φ.subst ![Language.Term.var 0, t_y]

    use φ'
    ext v ; simp [φ', Formula.Realize]
    have : (fun a ↦ Term.realize v (![var 0, t_y] a)) = ![v 0,y] := List.ofFn_inj.mp rfl
    rw [this]
    constructor <;> intro h
    · suffices hφ' : Formula.Realize φ ![v 0, y] from by
        exact hφ'
      obtain ⟨hv,hfv⟩ := h
      change ![v 0, y] ∈ setOf φ.Realize
      rw [←hφ] ; simp ; use hv
    · change ![v 0, y] ∈ setOf φ.Realize at h
      rw [←hφ] at h
      simpa using h

end FirstOrder.Language
