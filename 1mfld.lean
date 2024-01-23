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
    intro z
    sorry
}

noncomputable section

def I := Set.Ioo (0 : ℝ) (1 : ℝ)
def embed_I : I → ℝ := (↑)
def Qhalf : ℚ := 1 / 2
def half : ℝ := Rat.cast Qhalf

lemma half_lt_one : half < (1 : ℝ) := by
  have h : (Qhalf < (1 : ℚ)) := by rw [Qhalf]; norm_num
  have h' : Rat.cast Qhalf < Rat.cast (1 : ℚ) := by rw [Real.ratCast_lt]; exact h
  calc
    half = Rat.cast Qhalf := rfl
    _ < Rat.cast (1 : ℚ) := h'
    _ = (1 : ℝ) := by rw [Rat.cast_one]

lemma zero_lt_half : (0 : ℝ) < half := by
  have h : ((0 : ℚ) < Qhalf) := by rw [Qhalf]; norm_num
  have h' : Rat.cast (0 : ℚ) < Rat.cast Qhalf := by rw [Real.ratCast_lt]; exact h
  calc
    (0 : ℝ) = Rat.cast (0 : ℚ) := by rw [Rat.cast_zero]
    _ < Rat.cast Qhalf := h'
    _ = half := by rfl

lemma half_in_I : half ∈ I := by
  rw [I, Set.Ioo]
  dsimp
  exact ⟨zero_lt_half, half_lt_one⟩

def rev_embed_I : ℝ → I := by
  intro x
  by_cases xgt1: 1 ≤ x
  . use half
    exact half_in_I
  . by_cases xlt0: x ≤ 0
    . use half
      exact half_in_I
    . use x
      rw [I, Set.Ioo]
      dsimp
      rw [not_le] at *
      exact ⟨xlt0, xgt1⟩


instance : Topological1Manifold I := {
  locally_euclidean := by
    let h' : PartialHomeomorph I ℝ := {
      toFun := embed_I
      invFun := rev_embed_I
      source := (Set.univ : Set I)
      target := (I : Set ℝ)
      map_source' := by
        intro x xI
        rw [embed_I]
        apply Subtype.coe_prop
      map_target' := by
        intro x xI
        trivial
      left_inv' := by
        intro x xI
        rw [rev_embed_I, embed_I]
        have zero_lt_x : (0 : ℝ) < x := by exact Set.Ioo.pos x
        have x_lt_one : x < (1 : ℝ) := by exact Set.Ioo.lt_one x
        rw [← not_le] at zero_lt_x
        rw [← not_le] at x_lt_one
        split
        . contradiction
        . simp only [Subtype.coe_eta]
      right_inv' := by
        intro x xI
        rw [rev_embed_I, embed_I]
        rw [I, Set.Ioo] at xI
        dsimp at xI
        split
        . linarith
        split
        . linarith
        . dsimp
      open_source := isOpen_univ
      open_target := isOpen_Ioo
      continuousOn_toFun := by
        refine continuous_iff_continuousOn_univ.mp ?_
        exact continuous_induced_dom
      continuousOn_invFun := by
        dsimp
        refine Metric.continuousOn_iff.mpr ?_
        intro b bI ε εpos
        let δ := min ε (min b (1 - b))
        have δleε : δ ≤ ε := min_le_left ε _
        rw [I, Set.Ioo] at bI
        dsimp at bI
        have δpos : (0:ℝ) < δ := by
          apply lt_min
          exact εpos
          apply lt_min
          linarith
          linarith
        use δ
        constructor
        . exact δpos
        intro a aI a_close_b
        rw [I, Set.Ioo] at aI
        dsimp at aI
        repeat
          rw [rev_embed_I]
          split
          . linarith
          split
          . linarith
        rw [Subtype.dist_eq]
        rw [Real.dist_eq] at *
        dsimp
        linarith
    }
    intro x
    use h'
    dsimp
    show x ∈ Set.univ
    trivial
}
