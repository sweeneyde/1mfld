import Mathlib

-- class TopologicalManifold (n : ℕ) (X : Type u) ... ?

class Topological1ManifoldWithBoundary (X : Type u) [TopologicalSpace X] [T2Space X] extends ChartedSpace NNReal X

-- The real line is a 1-manifold with (empty) boundary
instance : Topological1ManifoldWithBoundary ℝ where
  atlas := sorry
  chartAt _ := sorry
  mem_chart_source x := sorry
  chart_mem_atlas _ := sorry

section

/-
Following https://www.math.tecnico.ulisboa.pt/~ggranja/TD/08/classif1manifs.pdf

ϕ: U → R and ψ: V → R are charts of M
• U ∩ V ≠ ∅, U ⊄ V and V ⊄ U;
• I = ϕ(U) and J = ψ(V) are bounded intervals
    (possibly containing endpoints);
-/

variable
  {M : Type}
  [TopologicalSpace M] [T2Space M]
  [ht : Topological1ManifoldWithBoundary M]

structure NiceChart (φ : PartialHomeomorph M NNReal) where
  in_atlas : φ ∈ ht.atlas
  bounded : Bornology.IsBounded φ.target
  connected : ConnectedSpace φ.target

structure PairOfCharts (φ ψ : PartialHomeomorph M NNReal) where
  nice_φ : NiceChart φ
  nice_ψ : NiceChart ψ
  nonempty : Set.Nonempty (φ.source ∩ ψ.source)
  u_not_in_v : ¬ (φ.source ⊆ ψ.source)
  v_not_in_u : ¬ (ψ.source ⊆ φ.source)

def intersection
  {φ ψ : PartialHomeomorph M NNReal}
  (_ : PairOfCharts φ ψ) :=
  φ.restrOpen (ψ.source) (ψ.open_source)

lemma lemma01a
  (φ ψ : PartialHomeomorph M NNReal)
  (pair : PairOfCharts φ ψ)
  (x : (intersection pair).target)
  (ha : a ∈ (frontier (connectedComponent x : Set NNReal))) :
  (a ∉ (connectedComponent x : Set NNReal)) := by
  sorry

end section

class Topological1Manifold (X : Type u) [TopologicalSpace X] [T2Space X] : Prop where
  locally_euclidean : ∀ ⦃x : X⦄, ∃ (h : (PartialHomeomorph X ℝ)), x ∈ h.source

instance : Topological1Manifold ℝ := {
  locally_euclidean := by
    intro x
    have h' : Homeomorph ℝ ℝ := Homeomorph.refl ℝ
    use Homeomorph.toPartialHomeomorph h'
    simp only [Homeomorph.toPartialHomeomorph_source, Set.mem_univ]
}

instance : Topological1Manifold circle := {
  locally_euclidean := by
    sorry
}

def unit_interval := Set.Ioo (0 : ℝ) (1 : ℝ)

instance : Topological1Manifold unit_interval := {
  locally_euclidean := by
    intro x
    -- use Real.tanLocalHomeomorph
    sorry
}
