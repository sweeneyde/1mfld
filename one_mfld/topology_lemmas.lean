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

def LocalCutPoint
  {X : Type} [TopologicalSpace X] (x : X) :=
  ∀V : Set X, IsOpen V → x ∈ V → ∃ U : Set X,
  U ⊆ V ∧ IsOpen U ∧ x ∈ U ∧ IsConnected U ∧ ¬(IsConnected (U \ {x}))

lemma localCutPoint_of_homeo
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) {x : X} (hx: LocalCutPoint x) : LocalCutPoint (f x) := by
  intro V' hV' fx_in_V'
  let V : Set X := f ⁻¹' V'
  have openV : IsOpen V := (Homeomorph.isOpen_preimage f).mpr hV'
  let ⟨U, U_subset_V, openU, x_in_U, connU, cutU⟩ := hx V openV fx_in_V'
  use f '' U
  constructor
  · exact Set.mapsTo'.mp U_subset_V
  constructor
  · exact (Homeomorph.isOpen_image f).mpr openU
  constructor
  · exact Set.mem_image_of_mem (⇑f) x_in_U
  constructor
  · exact (Homeomorph.isConnected_image f).mpr connU
  contrapose cutU; rw [not_not] at *
  have : ⇑f '' U \ {f x} = f '' (U \ {x}) := by
    ext z
    simp only [Set.mem_diff, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨w, ⟨hw₁, hw₂⟩⟩, z_ne_fx⟩
      use w
      constructor
      · constructor
        · exact hw₁
        · contrapose z_ne_fx
          rw [not_not] at *
          rw [← z_ne_fx, hw₂]
      · exact hw₂
    · rintro ⟨w, ⟨wU , w_ne_x⟩, fwz⟩
      constructor
      · use w
      · contrapose w_ne_x; rw [not_not] at *
        rw [w_ne_x] at fwz
        have : f.invFun (f w) = f.invFun (f x) := congrArg f.invFun fwz
        simp only [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, Homeomorph.symm_apply_apply] at this
        exact this
  rw [this] at cutU
  have : IsConnected (f.invFun '' (⇑f '' (U \ {x}))) := by
    simp only [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, Homeomorph.isConnected_image]
    exact (Homeomorph.isConnected_image f).mp cutU
  simp only [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, Homeomorph.isConnected_image] at this
  exact this

lemma localCutPoint_of_homeo_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) : LocalCutPoint x ↔ LocalCutPoint (f x) := by
  constructor
  · exact localCutPoint_of_homeo f
  · intro hfx
    have : _ := localCutPoint_of_homeo f.symm hfx
    rw [Homeomorph.symm_apply_apply] at this
    exact this

lemma localCutPoint_local
    {X : Type} [TopologicalSpace X] (x : X) (hx : LocalCutPoint x)
    (U : Set X) (hU: IsOpen U) (xU : x ∈ U) : LocalCutPoint (⟨x, xU⟩ : U) := by

  let i : { x // x ∈ U } → X := Subtype.val
  intro V hV xV
  have openV : IsOpen (↑V : Set X) := IsOpen.trans hV hU
  specialize hx (i '' V) openV (Set.mem_image_val_of_mem xU xV)
  have ⟨W, h₂, h₃, h₄, h₅, h₆⟩ := hx
  have : ∃W' : Set { x // x ∈ U }, W = i '' W' := by
    use i ⁻¹' W
    rw [Subtype.image_preimage_coe]
    refine (Set.inter_eq_self_of_subset_left ?h.a).symm
    exact subset_trans h₂ Set.image_val_subset
  have ⟨W', hW'⟩ := this
  have hW'' : W' = i ⁻¹' W := by
    rw [hW']
    have : Function.Injective i := Subtype.val_injective
    exact (Set.preimage_image_eq W' this).symm
  have openW' : IsOpen W' := by
    rw [hW'']
    exact isOpen_induced h₃
  rw [hW'] at h₂
  have openEmbedding_i : OpenEmbedding i := by
    apply openEmbedding_iff_continuous_injective_open.mpr
    exact ⟨continuous_subtype_val, Subtype.val_injective, IsOpen.isOpenMap_subtype_val hU⟩
  have connW' : IsConnected W' := by
    apply IsConnected.preimage_of_openMap
    rw [hW'']

    sorry
  have : W' ⊆ V := by
    intro w wW
    have : ↑w ∈ Subtype.val '' W' := Set.mem_image_of_mem Subtype.val wW
    have : ↑w ∈ Subtype.val '' V := h₂ this
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Subtype.coe_prop, exists_const] at this
    exact this
  use W'
  constructor
  · exact this
  constructor
  · exact openW'
  constructor
  · rw [hW'']
    simp only [Set.mem_preimage]
    exact h₄
  constructor
  ·
    sorry
  sorry

lemma connected_of_partialHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) (A : Set X) (h₁A : A ⊆ f.source)
    (h₂A : IsConnected A) : IsConnected (f '' A) := by
  let i := Set.inclusion h₁A
  have cont_i : Continuous i := continuous_inclusion h₁A
  let f' := f.toHomeomorphSourceTarget
  let j : f.source → X := (↑)
  let A' := i '' (Set.univ : Set A)
  let fA₀ := f' '' A'
  let fA₁ : Set Y := (↑) '' fA₀
  have : ConnectedSpace A := Subtype.connectedSpace h₂A
  have : f '' A = fA₁ := by
    dsimp
    ext y
    constructor
    · rintro ⟨a, aA, fa_eq_y⟩
      rw [← fa_eq_y]
      rw [← Set.image_comp, ← Set.image_comp]
      use ⟨a, aA⟩
      simp only [Set.mem_univ, Function.comp_apply, Set.inclusion_mk,
        PartialHomeomorph.toHomeomorphSourceTarget_apply_coe, and_self]
    · rintro ⟨y', ⟨a, ⟨a', _, h₃⟩, h₂⟩, h₁⟩
      use a
      constructor
      · rw [← h₃]
        simp only [Set.coe_inclusion, Subtype.coe_prop]
      rw [← h₃, ← h₁, ← h₂]
      simp only [Set.coe_inclusion, PartialHomeomorph.toHomeomorphSourceTarget_apply_coe]
      refine (PartialHomeomorph.eq_symm_apply f ?h.right.hx ?h.right.hy).mp ?h.right.a
      · have : ↑a' = j (i a') := rfl
        rw [this]
        exact Subtype.mem (i a')
      · simp only [Subtype.coe_prop, PartialHomeomorph.map_source]
      · simp only [Subtype.coe_prop, PartialHomeomorph.left_inv]
        rw [← h₃]
        simp only [Set.coe_inclusion]
  rw [this]
  refine IsConnected.image ?H Subtype.val ?hf
  · refine (Homeomorph.isConnected_image f').mpr ?H.a
    refine IsConnected.image ?H.a.H i ?H.a.hf
    refine isConnected_univ
    refine continuous_iff_continuousOn_univ.mp ?H.a.hf.a
    exact cont_i
  exact Continuous.continuousOn continuous_subtype_val

lemma connected_of_partialHomeomorph_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) (A : Set X) (hA : A ⊆ f.source)
    : IsConnected A ↔ IsConnected (f '' A) := by
  constructor
  · exact fun a => connected_of_partialHomeomorph f A hA a
  intro connfA
  have : f '' A ⊆ (PartialHomeomorph.symm f).source := by
    simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
      Set.image_subset_iff]
    have : f.source ⊆ f ⁻¹' f.target := PartialHomeomorph.source_preimage_target f
    exact Set.Subset.trans hA this
  have h : IsConnected (f.symm '' (f '' A)) :=
    connected_of_partialHomeomorph f.symm (f '' A) this connfA
  have : f.symm '' (f '' A) = A := by
    apply subset_antisymm
    · intro a ⟨fa, ⟨a', h₃a', h₂a'⟩, h₁a'⟩
      rw [← h₂a'] at h₁a'
      rw [PartialHomeomorph.left_inv f (hA h₃a')] at h₁a'
      rw [← h₁a']
      exact h₃a'
    · intro a ha
      rw [← Set.image_comp]
      use a
      constructor
      · exact ha
      simp only [Function.comp_apply]
      exact PartialHomeomorph.left_inv f (hA ha)
  rw [this] at h
  exact h

lemma preimage_of_partialHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) (B : Set Y) (hB : B ⊆ f.target)
    : f.symm '' B = f.source ∩ f ⁻¹' B := by
  exact PartialHomeomorph.symm_image_eq_source_inter_preimage f hB

lemma partialhomeomorph_image_of_symm_image
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) (B : Set Y) (hB : B ⊆ f.target)
    : f '' (f.symm '' B) = B := by
  rw [← Set.image_comp]
  apply subset_antisymm
  · rintro b ⟨b', h₁b', h₂b'⟩
    have : (↑f ∘ ↑(PartialHomeomorph.symm f)) b' = b' := f.right_inv' (hB h₁b')
    rw [this] at h₂b'
    rw [← h₂b']
    exact h₁b'
  · rintro b hb
    use b
    constructor
    · exact hb
    simp only [Function.comp_apply]
    exact f.right_inv (hB hb)

lemma partialhomeomorph_image_of_puncture
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) (U : Set X) (hU : U ⊆ f.source)
    {x : X} (hx : x ∈ U)
    : f '' U \ {f x} = f '' (U \ {x}) := by
  ext b;
  simp only [Set.mem_diff, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, a_in_Ux, fa_eq_b⟩, b_ne_fx⟩
    use a
    constructor
    · constructor
      · exact a_in_Ux
      · contrapose b_ne_fx; rw [not_not] at *
        rw [← b_ne_fx, fa_eq_b]
    · exact fa_eq_b
  · rintro ⟨a, ⟨a_in_Ux, a_ne_x⟩, fa_eq_b⟩
    constructor
    · use a
    · contrapose a_ne_x; rw [not_not] at *
      rw [a_ne_x] at fa_eq_b
      calc
        a = f.symm (f a) := (PartialHomeomorph.left_inv f (hU a_in_Ux)).symm
        _ = f.symm (f x) := by rw [fa_eq_b]
        _ = x := PartialHomeomorph.left_inv f (hU hx)

lemma localCutPoint_of_partialHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : PartialHomeomorph X Y) {x : X}
    (h₁x : x ∈ f.source) (h₂x: LocalCutPoint x) : LocalCutPoint (f x) := by

  rintro Vy openVy fxVy
  let Vx := f.symm '' (Vy ∩ f.target)
  have x_in_Vx : x ∈ Vx := by
    simp only [Set.mem_image, Set.mem_inter_iff]
    use f x
    exact ⟨⟨fxVy, PartialHomeomorph.map_source f h₁x⟩, PartialHomeomorph.left_inv f h₁x⟩
  have hVx : Vx = f.source ∩ ↑f ⁻¹' (Vy ∩ f.target) := PartialHomeomorph.symm_image_eq_source_inter_preimage f (Set.inter_subset_right Vy f.target)

  have openVx := PartialHomeomorph.isOpen_inter_preimage f (IsOpen.inter openVy f.open_target)
  rw [← hVx] at openVx

  have fVx : f '' Vx = Vy ∩ f.target := by
    apply partialhomeomorph_image_of_symm_image
    exact Set.inter_subset_right Vy f.target

  rcases h₂x Vx openVx x_in_Vx with ⟨Ux, Ux_sub_Vx, openUx, x_in_Ux, connUx, notConnUx_x⟩

  have Ux_source : Ux ⊆ f.source := by calc
    Ux ⊆ Vx := Ux_sub_Vx
    _ = f.source ∩ ↑f ⁻¹' (Vy ∩ f.target) := hVx
    _ ⊆ f.source := Set.inter_subset_left f.source (↑f ⁻¹' (Vy ∩ f.target))

  use f '' Ux
  constructor
  · calc
    f '' Ux ⊆ f '' Vx := Set.image_mono Ux_sub_Vx
    _ = Vy ∩ f.target := fVx
    _ ⊆ Vy := Set.inter_subset_left Vy f.target
  constructor
  · have := PartialHomeomorph.isOpen_image_source_inter f openUx
    rw [Set.inter_eq_right.mpr Ux_source] at this
    exact this
  constructor
  · exact Set.mem_image_of_mem f x_in_Ux
  constructor
  · exact (connected_of_partialHomeomorph_iff f Ux Ux_source).mp connUx
  · rw [partialhomeomorph_image_of_puncture f Ux Ux_source x_in_Ux]
    contrapose notConnUx_x; rw [not_not] at *
    have : Ux \ {x} ⊆ f.source := by calc
      Ux \ {x} ⊆ Ux := Set.diff_subset Ux {x}
      _ ⊆ f.source := Ux_source
    have := connected_of_partialHomeomorph_iff f (Ux \ {x}) this
    rw [this]
    exact notConnUx_x

lemma localCutPoint_of_nnreal_iff
    (x : NNReal) : (LocalCutPoint x) ↔ x > 0 := by
  constructor
  · sorry
  · sorry
