import Mathlib

-- class TopologicalManifold (n : ℕ) (X : Type u) ... ?

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
