import Mathlib.ModelTheory.Definability

namespace FirstOrder.Language.Definable

open FirstOrder Language Set

variable {M : Type*} {L : Language} [L.Structure M] {α : Type*} {β : Type*}

def DefinableFun (L : Language) [L.Structure M] (A : Set M) (f : (α → M) → M) : Prop :=
  A.Definable L {v : ((α ⊕ Unit) → M)  | f (v ∘ Sum.inl) = v (Sum.inr ())}

theorem definable_fun_of_fun_symbol {n : ℕ} (f : L.Functions n) :
    DefinableFun L (∅ : Set M) (fun x : Fin n → M => Structure.funMap f x) := by
  refine empty_definable_iff.mpr ?_
  let t_out : L.Term (Fin n ⊕ Unit) := Term.var (Sum.inr ())
  let t_in  : Fin n → L.Term (Fin n ⊕ Unit) := fun i => Term.var (Sum.inl i)
  let φ := (Term.func f t_in).equal t_out
  use φ ; ext v ; simp [φ, t_in, t_out, Function.comp_def]

theorem definable_fun_of_term (t : L.Term α) :
    DefinableFun L (∅ : Set M) (fun v => t.realize v) := by
  refine empty_definable_iff.mpr ?_
  let t_lifted : L.Term (α ⊕ Unit) := t.relabel Sum.inl
  let t_out : L.Term (α ⊕ Unit) := Term.var (Sum.inr ())
  let φ := t_lifted.equal t_out
  use φ ; ext v ; simp [φ, t_lifted, t_out]

def DefinableMap (L : Language) [L.Structure M] (A : Set M) (F : (α → M) → (β → M)) : Prop :=
  ∀ i : β, DefinableFun L A (fun x => F x i)

lemma definable_exists_fintype [Finite β] {A : Set M} {S : Set ((α ⊕ β) → M)}
    (hS : A.Definable L S) :
    A.Definable L { v : α → M | ∃ u : β → M, Sum.elim v u ∈ S } := by
  obtain ⟨φ, hφ⟩ := hS
  use φ.iExs β
  ext v ; simp [hφ]

lemma definable_preimage_of_definableMap
    {α β : Type} [Finite β] {A : Set M}
    {F : (α → M) → (β → M)} (hF : DefinableMap L A F)
    {S : Set (β → M)} (hS : A.Definable L S) :
    A.Definable L { v : α → M | F v ∈ S } := by
  letI := Fintype.ofFinite β
  let graph := { w : α ⊕ β → M | ∀ i, (F (w ∘ Sum.inl)) i = w (Sum.inr i) }
  have h_graph : A.Definable L graph := by
    simp [graph]
    rw [setOf_forall fun i x ↦ F (x ∘ Sum.inl) i = x (Sum.inr i)]
    have : ∀ i, A.Definable L {x | F (x ∘ Sum.inl) i = x (Sum.inr i)} := by
      intro i
      specialize hF i
      simp [DefinableFun] at hF
      let f : α ⊕ Unit → α ⊕ β := Sum.map id (fun _ ↦ i)
      convert hF.preimage_comp f using 1
    convert definable_biInter_finset this (Finset.univ) using 1
    simp
  have h_cyl : A.Definable L { w : α ⊕ β → M | w ∘ Sum.inr ∈ S } :=
    hS.preimage_comp Sum.inr
  have hS' := definable_exists_fintype (Definable.inter h_graph h_cyl)
  simp [graph, inter_def] at hS'
  convert hS' using 1
  ext v ; simp
  constructor
  · intro h ; use (F v) ; grind
  · rintro ⟨u,hFv,hu⟩
    have : F v = u := by exact (eqOn_univ (F v) u).mp fun ⦃x⦄ a ↦ hFv x
    rwa [this]

-- def subst_map (Vars : β → Type*) (F : ∀ i, (Vars i → M) → M)
--     (w : α ⊕ (Σ i, Vars i) → M) : α ⊕ β → M :=
--   fun x => match x with
--   | Sum.inl a => w (Sum.inl a)
--   | Sum.inr b => F b (fun g => w (Sum.inr ⟨b, g⟩))

-- theorem definable_subst [Finite β] {S : Set (α ⊕ β → M)} {A :Set M} (hS : A.Definable L S)
--     (Vars : β → Type*) (F : ∀ i : β, (Vars i → M) → M) (hF : DefinableMap L A (subst_map Vars F)) :
--     A.Definable L { w : α ⊕ (Σ i, Vars i) → M | subst_map Vars F w ∈ S } := by
--   sorry

end FirstOrder.Language.Definable
