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

def UDefinable_fun {A : Set M} {B : Set M} (f : A → B) : Prop :=
  (univ : Set M).Definable₂ L ((fun (a : A) => (a.val, (f a).val)) '' univ)

end FirstOrder.Language
