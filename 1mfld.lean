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

instance : LocallyConnectedSpace NNReal := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U xU
  rw [nhds_subtype {x : ℝ | 0 ≤ x} x] at xU
  simp only [Set.mem_setOf_eq, NNReal.val_eq_coe, Filter.mem_comap] at xU
  let ⟨t, x_t, t_U⟩ := xU
  rw [mem_nhds_iff_exists_Ioo_subset] at x_t
  let ⟨l, u, x_ul, ul_t⟩ := x_t
  rw [Set.Ioo] at x_ul
  dsimp at x_ul
  have l_lt_u : l < u := lt_trans x_ul.1 x_ul.2
  have upos : 0 < u := gt_of_gt_of_ge (x_ul.2) (zero_le x)

  let V := {y : NNReal | l < ↑y ∧ ↑y < u}
  use V
  constructor
  . rw [nhds_subtype {x : ℝ | 0 ≤ x} x]
    simp only [ge_iff_le, max_le_iff, NNReal.zero_le_coe, true_and, Set.mem_setOf_eq,
    NNReal.val_eq_coe, Filter.mem_comap]
    use Set.Ioo l u
    constructor
    . exact Ioo_mem_nhds x_ul.1 x_ul.2
    . intro a a_lu
      dsimp
      rw [Set.preimage, Set.Ioo] at a_lu
      dsimp at a_lu
      exact a_lu
  constructor
  -- . apply Convex.IsConnected
  . apply IsConnected.isPreconnected
    apply IsPathConnected.isConnected
    rw [IsPathConnected]
    let z := ((max 0 l) + u) / 2
    have znonneg : 0 ≤ z := by
      have nn₁ : 0 ≤ (max 0 l) := le_max_left 0 l
      have nn₂ : 0 ≤ u := LT.lt.le upos
      have : 0 ≤ (max 0 l) + u := add_nonneg nn₁ nn₂
      exact div_nonneg this zero_le_two
    let z' : NNReal := ⟨z, znonneg⟩
    have l_lt_z : l < z := by
      have : l ≤ max 0 l := le_max_right 0 l
      show l < (max 0 l + u) / 2
      linarith
    have z_lt_u : z < u := by
      have : max 0 l < u := max_lt_iff.mpr ⟨upos, l_lt_u⟩
      show (max 0 l + u) / 2 < u
      linarith
    have : z' ∈ V := ⟨l_lt_z, z_lt_u⟩
    use z'
    use this
    intro y yV
    dsimp at yV
    by_cases h : z' = y
    . exact Inseparable.joinedIn (congrArg nhds h) this yV
    rw [JoinedIn]
    let γ : Path z' y := {
      toFun := fun t ↦ ⟨(unitInterval.symm t)*z' + t*y,
        add_nonneg (mul_nonneg unitInterval.nonneg' znonneg) (mul_nonneg unitInterval.nonneg' (zero_le y))⟩
      continuous_toFun := by
        simp only [unitInterval.coe_symm_eq, NNReal.coe_mk]
        rw [Metric.continuous_iff]
        intro s ε εpos
        let δ := ε / dist y z'
        have dyz'pos : 0 < dist y z' := dist_pos.mpr (ne_comm.mpr h)
        have δpos : δ > 0 := div_pos εpos dyz'pos
        use δ
        constructor
        . exact δpos
        intro a a_s_near
        rw [dist, PseudoMetricSpace.toDist, instPseudoMetricSpaceNNReal, Subtype.pseudoMetricSpace]
        simp only [NNReal.val_eq_coe, NNReal.coe_mk]
        rw [dist, PseudoMetricSpace.toDist, Real.pseudoMetricSpace]
        simp only
        rw [sub_mul, sub_mul, one_mul]
        have : (max 0 l + u) / 2 - ↑a * ((max 0 l + u) / 2) + ↑a * ↑y - ((max 0 l + u) / 2 - ↑s * ((max 0 l + u) / 2) + ↑s * ↑y)
          = (↑a - ↑s) * (↑y - ((max 0 l + u) / 2)) := by ring
        rw [this, abs_mul]
        have : |(a:ℝ) - (s:ℝ)| < δ := by
          rw [← Real.dist_eq (a : ℝ) (s : ℝ)]
          exact a_s_near
        have : |↑y - (max 0 l + u) / 2| = dist y z' := rfl
        rw [this]
        calc
          |↑a - ↑s| * dist y z'
            < δ * dist y z' := mul_lt_mul_of_pos_right a_s_near dyz'pos
          _ = ε := div_mul_cancel ε (ne_of_gt dyz'pos)
      source' := by
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, NNReal.coe_mk, one_mul,
          Set.Icc.coe_zero, zero_mul, add_zero]
      target' := by
        simp only [unitInterval.symm_one, Set.Icc.coe_zero, NNReal.coe_mk, zero_mul,
          Set.Icc.coe_one, one_mul, zero_add]
        trivial
    }
    use γ
    intro t
    simp only [NNReal.coe_mk, Path.coe_mk_mk, gt_iff_lt, Set.mem_setOf_eq]
    constructor
    . show l < ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y
      by_cases tpos : t > 0
      . calc
          l = ↑(unitInterval.symm t) * l + t * l := by
            simp only [unitInterval.coe_symm_eq]
            ring
          _ < ↑(unitInterval.symm t) * l + t * y := by
            have : t * l < t * y := mul_lt_mul_of_pos_left yV.1 tpos
            linarith
          _ ≤ ↑(unitInterval.symm t) * z + t * y := by
            have : ↑(unitInterval.symm t) * l ≤ ↑(unitInterval.symm t) * z
              := mul_le_mul_of_nonneg_left (le_of_lt l_lt_z) unitInterval.nonneg'
            linarith
      . have : t = 0 := le_antisymm (not_lt.mp tpos) (unitInterval.nonneg')
        rw [this]
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, one_mul, Set.Icc.coe_zero, zero_mul,
          add_zero, gt_iff_lt]
        exact l_lt_z
    . show ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y < u
      by_cases tpos : t > 0
      . calc
          ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * ↑y
          < ↑(unitInterval.symm t) * ((max 0 l + u) / 2) + ↑t * u := by
            have : ↑t * ↑y < ↑t * u := mul_lt_mul_of_pos_left yV.2 tpos
            linarith
          _ ≤ ↑(unitInterval.symm t) * u + ↑t * u := by
            have : ↑(unitInterval.symm t) * ((max 0 l + u) / 2) ≤ ↑(unitInterval.symm t) * u
              := mul_le_mul_of_nonneg_left (le_of_lt z_lt_u) unitInterval.nonneg'
            linarith
          _ = u := by rw [unitInterval.coe_symm_eq]; ring
      . have : t = 0 := le_antisymm (not_lt.mp tpos) (unitInterval.nonneg')
        rw [this]
        simp only [unitInterval.symm_zero, Set.Icc.coe_one, one_mul, Set.Icc.coe_zero, zero_mul,
          add_zero, gt_iff_lt]
        exact z_lt_u
  . intro a aV
    dsimp at aV
    apply t_U
    rw [Set.preimage]
    dsimp
    apply ul_t
    rw [Set.Ioo]
    exact aV

lemma lemma01a
  (φ ψ : PartialHomeomorph M NNReal)
  (pair : PairOfCharts φ ψ)
  (x : (intersection pair).target)
  (ha : a ∈ (frontier (connectedComponentIn φ.target x))) :
  (a ∉ connectedComponentIn φ.target x) := by
    let I := φ.target
    let K := connectedComponentIn I x
    show a ∉ K
    have : IsOpen K := IsOpen.connectedComponentIn φ.open_target

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
