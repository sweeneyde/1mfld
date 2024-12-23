import Mathlib
import one_mfld

-- The real line is a 1-manifold with (empty) boundary
instance : Topological1ManifoldWithBoundary ℝ where
  atlas := sorry
  chartAt _ := sorry
  mem_chart_source x := sorry
  chart_mem_atlas _ := sorry

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
    intro z
    sorry
}

noncomputable section

instance : Topological1Manifold (Set.Ioo (0 : ℝ) (1 : ℝ)) := {
  locally_euclidean := by
    let I := Set.Ioo (0 : ℝ) (1 : ℝ)
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
      map_source' := by
        intro x _
        apply Subtype.coe_prop
      map_target' := by
        intro x _
        trivial
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
      continuousOn_toFun := by
        refine continuous_iff_continuousOn_univ.mp ?_
        exact continuous_induced_dom
      continuousOn_invFun := by
        dsimp
        rw [continuousOn_iff_continuous_restrict]
        have eq : Set.restrict I rev_embed_I = id := by
          ext x
          rw [Set.restrict_apply, id_eq]
          dsimp
          split
          . dsimp
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
