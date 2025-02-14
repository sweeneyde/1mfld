import Mathlib

-- class TopologicalManifold (n : ℕ) (X : Type u) ... ?

-- TODO: include 2nd countable
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
  {a : NNReal}
  (ha : a ∈ (frontier (connectedComponentIn φ.target x))) :
  (a ∉ (connectedComponentIn φ.target x)) := by
  sorry

lemma lemma01b
  (φ ψ : PartialHomeomorph M NNReal)
  (pair : PairOfCharts φ ψ)
  (x : (intersection pair).target)
  {a : NNReal}
  (haK : a ∈ (frontier (connectedComponentIn φ.target x)))
  (haI : a ∈ φ.target) :
  (a ∉ (connectedComponentIn φ.target x)) := by
  sorry

section

variable
  (φ ψ : PartialHomeomorph M NNReal)
  (pair : PairOfCharts φ ψ)
  (x : (intersection pair).target)
  {a : NNReal}
  (haI : a ∈ φ.target)
  (haK : a ∈ (frontier (connectedComponent x : Set NNReal)))

def α := (intersection pair).symm.trans ψ

#check α

lemma lemma01b :
  (a ∉ (connectedComponent x : Set NNReal)) := by
  sorry

end section

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

instance : Topological1Manifold Circle := {
  locally_euclidean := by
    intro z
    sorry
}

noncomputable section

abbrev I := Set.Ioo (0 : ℝ) (1 : ℝ)

instance : Topological1Manifold I := {
  locally_euclidean := by
    let rev_embed_I : ℝ → I := by
      intro x
      by_cases xI : x ∈ I
      . use x
      . have h: ∃x, x ∈ I := by
          rw [← Set.Nonempty, Set.nonempty_Ioo]
          norm_num
        exact Classical.subtype_of_exists h

    let h' : PartialHomeomorph I ℝ := {
      toFun := (↑)
      invFun := rev_embed_I
      source := (Set.univ : Set I)
      target := (I : Set ℝ)
      map_source' := fun x _ => Subtype.coe_prop x
      map_target' := fun _ _ => by trivial
      left_inv' := by
        intro x _
        dsimp
        split
        . simp only [Subtype.coe_eta]
        . have : ↑x ∈ I := by exact Subtype.mem x
          contradiction
      right_inv' := by
        intro x xI
        dsimp
        split
        . dsimp
        . contradiction
      open_source := isOpen_univ
      open_target := isOpen_Ioo
      continuousOn_toFun := continuous_iff_continuousOn_univ.mp continuous_induced_dom
      continuousOn_invFun := by
        dsimp
        rw [continuousOn_iff_continuous_restrict]
        have eq : Set.restrict I rev_embed_I = id := by
          ext x
          rw [Set.restrict_apply, id_eq]
          dsimp
          split
          . trivial
          . have : ↑x ∈ I := by exact Subtype.mem x
            contradiction
        rw [eq]
        exact continuous_id
    }
    intro x
    use h'
    show x ∈ Set.univ
    trivial
}

-- TODO: the circle is a 1-manifold

-- TODO: smooth 1-manifolds are topological 1-manifolds

-- TODO: intervals are all homeomorphic

theorem intervals_are_homeo (a b c d : ℝ) : AffineHomeo (Set.Ioo a b) ≃ₜ (Set.Ioo c d) := by
  sorry
