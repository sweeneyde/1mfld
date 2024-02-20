import Mathlib

instance : LocallyConnectedSpace Real := by infer_instance

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

lemma frontier_intersection_sub_union_frontiers
  {X : Type} [TopologicalSpace X] (A B : Set X)
  : frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  calc
    frontier (A ∩ B)
    ⊆ frontier A ∩ closure B ∪ closure A ∩ frontier B
      := frontier_inter_subset A B
    _ ⊆ frontier A ∪ frontier B
      := Set.union_subset_union
          (Set.inter_subset_left (frontier A) (closure B))
          (Set.inter_subset_right (closure A) (frontier B))

lemma boundary_of_rel_open_subset
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (rel_open : ∃ U : Set X, IsOpen U ∧ B = A ∩ U)
    : B ∩ frontier B ⊆ frontier A := by
  rcases rel_open with ⟨U, Uopen, B_AU⟩
  intro b ⟨bB, bfrontierB⟩
  have : frontier B ⊆ frontier A ∪ frontier U := by
    rw [B_AU]
    exact frontier_intersection_sub_union_frontiers A U
  have : b ∈ frontier A ∪ frontier U := this bfrontierB
  rcases this with bfrontierA | bfrontierU
  . exact bfrontierA
  exfalso
  rw [frontier, IsOpen.interior_eq Uopen] at bfrontierU
  have : b ∉ U := Set.not_mem_of_mem_diff bfrontierU
  have : b ∈ U := by
    rw [B_AU] at bB
    exact Set.mem_of_mem_inter_right bB
  contradiction


-- connected subsets of ℝ

lemma Real.exists_isGLB (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S) : ∃ x, IsGLB S x := by
  use sInf S
  rw [sInf_def, ← isLUB_neg, sSup_def, dif_pos]
  . apply Classical.choose_spec
  exact ⟨Set.nonempty_neg.mpr hne, BddBelow.neg hbdd⟩

lemma ordconn_of_connected {X : Set ℝ} (conn : IsConnected X)
  (a : ℝ) (aX : a ∈ X) (b : ℝ) (bX : b ∈ X) : Set.Icc a b ⊆ X := by
  have : Set.OrdConnected X :=
    IsPreconnected.ordConnected (IsConnected.isPreconnected conn)
  exact Set.Icc_subset X aX bX

lemma connected_bddAbove_subset_contains_Ioo {X : Set ℝ} {supX : ℝ} {x : ℝ}
    (conn : IsConnected X) (h_supX : IsLUB X supX) (xX : x ∈ X)
    : Set.Ioo x supX ⊆ X := by
  intro y ⟨x_lt_y, y_lt_supX⟩
  by_cases h: ∃ z ∈ X, y ≤ z
  . rcases h with ⟨z, zX, y_le_z⟩
    have : Set.Icc x z ⊆ X := ordconn_of_connected conn x xX z zX
    exact this ⟨LT.lt.le x_lt_y, y_le_z⟩
  . push_neg at h
    have : y ∈ upperBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : supX ≤ y := h_supX.2 this
    linarith

lemma connected_bddBelow_subset_contains_Ioo {X : Set ℝ} {infX : ℝ} {x : ℝ}
    (conn : IsConnected X) (h_infX : IsGLB X infX) (xX : x ∈ X)
    : Set.Ioo infX x ⊆ X := by
  intro y ⟨infX_lt_y, y_lt_x⟩
  by_cases h: ∃ z ∈ X, z ≤ y
  . rcases h with ⟨z, zX, z_le_y⟩
    have : Set.Icc z x ⊆ X := ordconn_of_connected conn z zX x xX
    exact this ⟨z_le_y, LT.lt.le y_lt_x⟩
  . push_neg at h
    have : y ∈ lowerBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : y ≤ infX := h_infX.2 this
    linarith

lemma connected_bdd_subset_contains_Ioo
    {X : Set ℝ} {infX supX : ℝ}
    (conn : IsConnected X) (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    : Set.Ioo infX supX ⊆ X := by
  let ⟨z, zX⟩ := IsConnected.nonempty conn
  have h₁ : Set.Ioo infX z ⊆ X := connected_bddBelow_subset_contains_Ioo conn h_infX zX
  have h₂ : Set.Ioo z supX ⊆ X := connected_bddAbove_subset_contains_Ioo conn h_supX zX
  have h₃ : Set.Ioo infX supX ⊆ Set.Ioo infX z ∪ {z} ∪ Set.Ioo z supX := by
    intro x ⟨infX_lt_x, x_lt_supX⟩
    rcases lt_trichotomy x z with (x_lt_z | x_eq_z | z_lt_z)
    . left; left
      exact ⟨infX_lt_x, x_lt_z⟩
    . left; right
      rw [Set.mem_singleton_iff, x_eq_z]
    . right
      exact ⟨z_lt_z, x_lt_supX⟩
  have h₄ : Set.Ioo infX z ∪ {z} ∪ Set.Ioo z supX ⊆ X := by
    rintro x ((_ | x_eq_z) | _)
    . apply h₁; assumption
    . rw [Set.mem_singleton_iff] at x_eq_z
      rw [x_eq_z]
      exact zX
    . apply h₂; assumption
  intro x x_Ioo
  exact h₄ (h₃ x_Ioo)

lemma Ico_Ioo_with_endpoint {a b : ℝ} (hab : a < b)
    : Set.Ico a b = (Set.Ioo a b) ∪ {a} := by
  apply Set.Subset.antisymm
  . intro x ⟨x_le_a, x_lt_b⟩
    by_cases xa : x = a
    . right; exact xa
    have : a < x := by exact Ne.lt_of_le' xa x_le_a
    left; exact ⟨this, x_lt_b⟩
  . rintro x (x_Ioo | x_a)
    . exact ⟨LT.lt.le x_Ioo.1, x_Ioo.2⟩
    . exact ⟨Eq.ge x_a, Eq.trans_lt x_a hab⟩

lemma Ioc_Ioo_with_endpoint {a b : ℝ} (hab : a < b)
    : Set.Ioc a b = (Set.Ioo a b) ∪ {b} := by
  apply Set.Subset.antisymm
  . intro x ⟨a_lt_x, x_le_b⟩
    by_cases xb : x = b
    . right; exact xb
    have : x < b := by exact Ne.lt_of_le xb x_le_b
    left; exact ⟨a_lt_x, this⟩
  . rintro x (x_Ioo | x_b)
    . exact ⟨x_Ioo.1, LT.lt.le x_Ioo.2⟩
    . exact ⟨(by rw [x_b]; exact hab), Eq.le x_b⟩

theorem classify_connected_reals
    {X : Set ℝ} (conn : IsConnected X)
    : (∃a:ℝ, ∃b:ℝ, a < b ∧ X = Set.Ioo a b) ∨
      (∃a:ℝ, ∃b:ℝ, a < b ∧ X = Set.Ioc a b) ∨
      (∃a:ℝ, ∃b:ℝ, a < b ∧ X = Set.Ico a b) ∨
      (∃a:ℝ, ∃b:ℝ, a < b ∧ X = Set.Icc a b) ∨
      (∃a:ℝ, X = Set.Iio a) ∨
      (∃a:ℝ, X = Set.Iic a) ∨
      (∃b:ℝ, X = Set.Ioi b) ∨
      (∃b:ℝ, X = Set.Ici b) ∨
      (∃a:ℝ, X = {a}) ∨
      (X = Set.univ)
    := by
  have ordconn := ordconn_of_connected conn
  let nonempty := IsConnected.nonempty conn

  have x_lt_excluded_supX {x supX : ℝ} (xX: x ∈ X)
    (h_supX: IsLUB X supX) (supX_X : supX ∉ X) : x < supX := by
    have : x ≠ supX := by
      intro x_eq_supX
      rw [← x_eq_supX] at supX_X
      contradiction
    exact Ne.lt_of_le this (h_supX.1 xX)

  have excluded_infX_lt_x {x infX : ℝ} (xX: x ∈ X)
    (h_infX: IsGLB X infX) (infX_X : infX ∉ X) : infX < x := by
    have : infX ≠ x := by
      intro x_eq_supX
      rw [x_eq_supX] at infX_X
      contradiction
    exact Ne.lt_of_le this (h_infX.1 xX)

  by_cases above : BddAbove X
  . let ⟨supX, h_supX⟩ := Real.exists_isLUB X nonempty above
    rw [IsLUB, IsLeast] at h_supX
    by_cases below : BddBelow X
    . let ⟨infX, h_infX⟩ := Real.exists_isGLB X nonempty below
      rw [IsGLB, IsGreatest] at h_infX
      have subset_Icc : X ⊆ Set.Icc infX supX := by
        intro x xX
        exact ⟨h_infX.1 xX, h_supX.1 xX⟩
      by_cases emptyX : X = ∅
      . have : X ≠ ∅ := by exact Set.Nonempty.ne_empty nonempty
        contradiction
      by_cases inf_eq_sup : infX = supX
      . right; right; right; right; right; right; right; right; left;
        use infX
        show X = {infX} -- {a}
        apply Set.Subset.antisymm
        . apply subset_trans subset_Icc
          exact Set.Icc_subset {infX} rfl (id inf_eq_sup.symm)
        . rw [Set.singleton_subset_iff]
          rcases nonempty with ⟨x, xX⟩
          have : x = supX := by
            apply LE.le.antisymm
            . exact h_supX.1 xX
            calc
              supX = infX := by rw [inf_eq_sup]
              _ ≤ x := h_infX.1 xX
          rw [inf_eq_sup, ← this]
          exact xX
      have : infX ≤ supX := isGLB_le_isLUB h_infX h_supX nonempty
      have inf_lt_sup : infX < supX := by exact Ne.lt_of_le inf_eq_sup this
      have contains_Ioo : Set.Ioo infX supX ⊆ X :=
        connected_bdd_subset_contains_Ioo conn h_infX h_supX
      by_cases supX_X : supX ∈ X
      . by_cases infX_X : infX ∈ X
        . right; right; right; left
          use infX, supX, inf_lt_sup
          show X = Set.Icc infX supX -- [a, b]
          apply Set.Subset.antisymm
          . exact subset_Icc
          . exact ordconn infX infX_X supX supX_X
        . right; left
          use infX, supX, inf_lt_sup
          show X = Set.Ioc infX supX -- (a, b]
          apply Set.Subset.antisymm
          . intro x xX
            constructor
            . exact excluded_infX_lt_x xX h_infX infX_X
            . exact h_supX.1 xX
          . rw [Ioc_Ioo_with_endpoint inf_lt_sup, Set.union_subset_iff]
            exact ⟨contains_Ioo, Set.singleton_subset_iff.mpr supX_X⟩
      . by_cases infX_X : infX ∈ X
        . right; right; left
          use infX, supX, inf_lt_sup
          show X = Set.Ico infX supX -- [a, b)
          apply Set.Subset.antisymm
          . intro x xX
            constructor
            . exact h_infX.1 xX
            . exact x_lt_excluded_supX xX h_supX supX_X
          . rw [Ico_Ioo_with_endpoint inf_lt_sup, Set.union_subset_iff]
            exact ⟨contains_Ioo, Set.singleton_subset_iff.mpr infX_X⟩
        . left
          use infX, supX, inf_lt_sup
          show X = Set.Ioo infX supX -- (a, b)
          apply Set.Subset.antisymm
          . intro x xX
            constructor
            . exact excluded_infX_lt_x xX h_infX infX_X
            . exact x_lt_excluded_supX xX h_supX supX_X
          . exact contains_Ioo
    . rw [bddBelow_def] at below
      push_neg at below
      by_cases supX_X : supX ∈ X
      . right; right; right; right; right; left
        use supX
        show X = Set.Iic supX -- (-∞, b]
        apply Set.Subset.antisymm
        . intro x xX
          exact h_supX.1 xX
        . intro x x_le_supX
          let ⟨A, AX, Asmall⟩ := below x
          have : Set.Icc A supX ⊆ X := ordconn A AX supX supX_X
          exact this ⟨LT.lt.le Asmall, x_le_supX⟩
      . right; right; right; right; left
        use supX
        show X = Set.Iio supX -- (-∞, b)
        apply Set.Subset.antisymm
        . intro x xX
          exact x_lt_excluded_supX xX h_supX supX_X
        . intro x x_lt_supX
          rw [Set.mem_Iio] at x_lt_supX
          let ⟨A, AX, Asmall⟩ := below x
          have : Set.Ioo A supX ⊆ X :=
            connected_bddAbove_subset_contains_Ioo conn h_supX AX
          exact this ⟨Asmall, x_lt_supX⟩
  . rw [bddAbove_def] at above
    push_neg at above
    by_cases below : BddBelow X
    . let ⟨infX, h_infX⟩ := Real.exists_isGLB X nonempty below
      by_cases infX_X : infX ∈ X
      . right; right; right; right; right; right; right; left
        use infX
        show X = Set.Ici infX -- [a, ∞)
        apply Set.Subset.antisymm
        . intro x xX
          exact h_infX.1 xX
        . intro x infX_le_x
          let ⟨B, BX, Bbig⟩ := above x
          have : Set.Icc infX B ⊆ X := ordconn infX infX_X B BX
          exact this ⟨infX_le_x, LT.lt.le Bbig⟩
      . right; right; right; right; right; right; left
        use infX
        show X = Set.Ioi infX -- (a, ∞)
        apply Set.Subset.antisymm
        . intro x xX
          exact excluded_infX_lt_x xX h_infX infX_X
        . intro x infX_lt_x
          rw [Set.mem_Ioi] at infX_lt_x
          let ⟨B, BX, Bbig⟩ := above x
          have : Set.Ioo infX B ⊆ X := by exact
            connected_bddBelow_subset_contains_Ioo conn h_infX BX
          exact this ⟨infX_lt_x, Bbig⟩
    . rw [bddBelow_def] at below
      push_neg at below
      right; right; right; right; right; right; right; right; right;
      show X = Set.univ -- (-∞, ∞)
      ext x
      simp only [Set.mem_univ, iff_true]
      let ⟨B, BX, Bbig⟩ := above x
      let ⟨A, AX, Asmall⟩ := below x
      have : Set.Icc A B ⊆ X := ordconn A AX B BX
      exact this ⟨LT.lt.le Asmall, LT.lt.le Bbig⟩
