import Mathlib
import one_mfld.topology_lemmas

-- def two := 2
-- open 1mfld.topology_lemmas

-- class TopologicalManifold (n : ℕ) (X : Type u) ... ?

class Topological1ManifoldWithBoundary (X : Type u) [TopologicalSpace X] [T2Space X] extends ChartedSpace NNReal X

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
  bounded_above : BddAbove φ.target
  bounded_below : BddBelow φ.target
  connected : IsConnected φ.target

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

def endpoint
  (S : Set NNReal) (a : NNReal) :=
  (↑a : ℝ) ∈ frontier ((↑) '' S : Set ℝ)


section
variable
  (φ ψ : PartialHomeomorph M NNReal)
  (pair : PairOfCharts φ ψ)

def U : Set M := φ.source
def V : Set M := ψ.source
def I : Set NNReal := φ.target
def J : Set NNReal := ψ.target
def UV := U φ ∩ V ψ
def φ_UV := φ.restrOpen (V ψ) (ψ.open_source)
def ψ_UV := ψ.restrOpen (U φ) (φ.open_source)

lemma sourceφ_UV : (φ_UV φ ψ).source = (UV φ ψ) := rfl
lemma sourceψ_UV : (ψ_UV φ ψ).source = (UV φ ψ) := by
  have : (UV φ ψ) = (UV ψ φ) := by
    rw [UV, UV]
    exact Set.inter_comm φ.source ψ.source
  exact id this.symm

def α := PartialHomeomorph.trans (PartialHomeomorph.symm φ) ψ
lemma I_connected : IsConnected (I φ) := pair.nice_φ.connected
lemma J_connected : IsConnected (J ψ) := pair.nice_ψ.connected
lemma U_homeo_I : (U φ) ≃ₜ (I φ) := PartialHomeomorph.toHomeomorphSourceTarget φ
lemma V_homeo_J : (V ψ) ≃ₜ (J ψ) := U_homeo_I ψ

lemma U_connected : IsConnected (U φ) := by
  have conn : IsConnected (φ.invFun '' I φ) :=
    IsConnected.image (I_connected φ ψ pair) φ.invFun φ.continuousOn_invFun
  have : (φ.invFun '' I φ) = (U φ) := by
    rw [U, I]
    ext x
    constructor
    . intro x_invFun_target
      let ⟨y, yI, h⟩ := x_invFun_target
      rw [← h]
      exact φ.map_target' yI
    . intro xU
      use φ.toFun x
      constructor
      . exact PartialEquiv.map_source φ.toPartialEquiv xU
      . exact PartialEquiv.left_inv' φ.toPartialEquiv xU
  rw [← this]
  exact conn

lemma V_connected : IsConnected (V ψ) := by
  have conn : IsConnected (ψ.invFun '' J ψ) :=
    IsConnected.image (J_connected φ ψ pair) ψ.invFun ψ.continuousOn_invFun
  have : (ψ.invFun '' J ψ) = (V ψ) := by
    rw [V, J]
    ext x
    constructor
    . intro x_invFun_target
      let ⟨y, yJ, h⟩ := x_invFun_target
      rw [← h]
      exact ψ.map_target' yJ
    . intro xV
      use ψ.toFun x
      constructor
      . exact PartialEquiv.map_source ψ.toPartialEquiv xV
      . exact PartialEquiv.left_inv' ψ.toPartialEquiv xV
  rw [← this]
  exact conn

lemma U_open : IsOpen (U φ) := φ.open_source
lemma V_open : IsOpen (V ψ) := ψ.open_source
lemma UV_open : IsOpen (U φ ∩ V ψ) := IsOpen.inter (U_open φ) (V_open ψ)

lemma image_α : (α φ ψ).target = ψ '' (U φ ∩ V ψ) := by
  ext x
  rw [α]
  constructor
  . intro x_image_α
    simp only [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.symm_toPartialEquiv,
      PartialEquiv.trans_target, PartialHomeomorph.coe_coe_symm, PartialEquiv.symm_target,
      Set.mem_inter_iff, Set.mem_preimage] at x_image_α
    rcases x_image_α with ⟨x_J, ψinv_x_U⟩
    simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, Set.mem_inter_iff]
    use (PartialHomeomorph.symm ψ).toFun x
    simp only [PartialHomeomorph.symm_toPartialEquiv, PartialHomeomorph.coe_coe_symm]
    constructor
    . constructor
      . exact ψinv_x_U
      . rw [V]
        exact PartialHomeomorph.map_target ψ x_J
    . exact PartialHomeomorph.right_inv ψ x_J
  . intro x_ψUV
    simp only [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.symm_toPartialEquiv,
      PartialEquiv.trans_target, PartialHomeomorph.coe_coe_symm, PartialEquiv.symm_target,
      Set.mem_inter_iff, Set.mem_preimage]
    simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, Set.mem_inter_iff] at x_ψUV
    rcases x_ψUV with ⟨x', ⟨x'U, x'V⟩, ψx'x⟩
    rw [←ψx'x]
    constructor
    . exact PartialHomeomorph.map_source ψ x'V
    rw [PartialHomeomorph.left_inv ψ x'V, ← U]
    exact x'U

lemma source_α : (α φ ψ).source = φ '' (U φ ∩ V ψ) := by
  ext x
  rw [α]
  simp only [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.symm_toPartialEquiv,
    PartialEquiv.trans_source, PartialEquiv.symm_source, PartialHomeomorph.coe_coe_symm,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  . rintro ⟨xU, φinvx_V⟩
    use (PartialHomeomorph.symm φ) x
    constructor
    . constructor
      . rw [U]
        exact PartialHomeomorph.map_target φ xU
      . rw [V]
        exact φinvx_V
    . exact PartialHomeomorph.right_inv φ xU
  . rintro ⟨x', ⟨x'U, x'V⟩, φx'x⟩
    rw [←φx'x]
    constructor
    . exact PartialHomeomorph.map_source φ x'U
    . rw [PartialHomeomorph.left_inv φ x'U, ← V]
      exact x'V

lemma source_α' : (α φ ψ).source = (φ_UV φ ψ).target := by
  calc
    (α φ ψ).source = φ '' (U φ ∩ V ψ) := source_α φ ψ
    _ = (φ_UV φ ψ).target := by
      rw [φ_UV]
      simp only [PartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
        PartialHomeomorph.coe_coe_symm]
      ext x
      constructor
      . intro x_φUV
        rcases x_φUV with ⟨x', ⟨x'U, x'V⟩, φx'x⟩
        rw [← φx'x]
        constructor
        . exact PartialHomeomorph.map_source φ x'U
        . simp only [Set.mem_preimage]
          rw [PartialHomeomorph.left_inv φ x'U]
          exact x'V
      . rintro ⟨xI, φx_V⟩
        simp only [Set.mem_preimage] at φx_V
        simp only [Set.mem_image, Set.mem_inter_iff]
        use PartialHomeomorph.symm φ x
        constructor
        . constructor
          . exact PartialHomeomorph.map_target φ xI
          . exact φx_V
        . exact PartialHomeomorph.right_inv φ xI

lemma α_homeo : (α φ ψ).source ≃ₜ (α φ ψ).target := PartialHomeomorph.toHomeomorphSourceTarget (α φ ψ)


section

variable
  (x : (φ_UV φ ψ).target)

def K := connectedComponentIn (φ_UV φ ψ).target x

lemma K_subset_I : K φ ψ x ⊆ I φ := by calc
  (K φ ψ x) ⊆ (φ_UV φ ψ).target := by
    rw [K]
    exact connectedComponentIn_subset (φ_UV φ ψ).toPartialEquiv.target ↑x
  _ ⊆ I φ := by
    rw [φ_UV, I]
    simp only [PartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
      PartialHomeomorph.coe_coe_symm, Set.inter_subset_left]

lemma K_open : IsOpen (K φ ψ x : Set NNReal) :=
    IsOpen.connectedComponentIn (φ_UV φ ψ).open_target

lemma K_open_I : ∃ U : Set ℝ, IsOpen U ∧
    (↑) '' (K φ ψ x) = ((↑) '' (I φ)) ∩ U := by
  have Kopen := K_open φ ψ x
  rw [isOpen_induced_iff] at Kopen
  rcases Kopen with ⟨U, Uopen, preimage_U⟩
  use U
  constructor
  . exact Uopen
  ext y
  constructor
  . intro yK
    rcases yK with ⟨y', y'K, y'y⟩
    constructor
    . exact ⟨y', K_subset_I φ ψ x y'K, y'y⟩
    . rw [← preimage_U, Set.mem_preimage, NNReal.val_eq_coe, y'y] at y'K
      exact y'K
  . intro ⟨yI, yU⟩
    rw [← preimage_U]
    rcases yI with ⟨y', _, y'y⟩
    use y'
    constructor
    . rw [Set.mem_preimage, NNReal.val_eq_coe, y'y]
      exact yU
    . exact y'y

lemma image_α_open : IsOpen (α φ ψ).target := by
  rw [image_α]
  apply PartialHomeomorph.isOpen_image_of_subset_source
  exact UV_open φ ψ
  rw [V]
  exact Set.inter_subset_right (U φ) ψ.source

lemma αK_open : IsOpen ((α φ ψ) '' (K φ ψ x)) := by
  apply PartialHomeomorph.isOpen_image_of_subset_source
  exact (K_open φ ψ x)
  rw [source_α', K]
  exact connectedComponentIn_subset (φ_UV φ ψ).toPartialEquiv.target ↑x

lemma αK_connected : IsConnected ((α φ ψ) '' (K φ ψ x)) := by
  refine IsConnected.image ?H ↑(α φ ψ) ?hf
  rw [K, connectedComponentIn_eq_image]
  -- have : IsConnected (connectedComponent ↑x) := isConnected_connectedComponent
  apply IsConnected.image
  . exact isConnected_connectedComponent
  . exact Continuous.continuousOn continuous_subtype_val
  . exact Subtype.mem x
  . have t₁ : ContinuousOn (↑(α φ ψ)) (α φ ψ).source
      := PartialHomeomorph.continuousOn (α φ ψ)
    rw [source_α'] at t₁
    have t₂ : K φ ψ x ⊆ (φ_UV φ ψ).target := by
      rw [K]
      exact connectedComponentIn_subset (φ_UV φ ψ).toPartialEquiv.target ↑x
    exact ContinuousOn.mono t₁ t₂

lemma J_boundedAbove : BddAbove (J ψ) := pair.nice_ψ.bounded_above
lemma J_boundedBelow : BddBelow (J ψ) := pair.nice_ψ.bounded_below

lemma αK_J : ((α φ ψ) '' (K φ ψ x)) ⊆ J ψ := by
  rw [J, α]
  sorry





-- lemma αK_boundedAbove : BddAbove ((α φ ψ) '' (K φ ψ x)) := by
--   have : ((α φ ψ) '' (K φ ψ x)) ⊆ J ψ := by calc
--     ((α φ ψ) '' (K φ ψ x)) ⊆ ((α φ ψ) '' (φ_UV φ ψ).target) := by
--       exact?
--     _ ⊆ (α φ ψ).target := by sorry
--     _ ⊆ J ψ := sorry
--   -- apply BddAbove.mono
--   sorry


lemma lemma01a
  (ha : endpoint (K φ ψ x) a) :
  (a ∉ (K φ ψ x)) := by
    by_cases a_ep_I : endpoint (I φ) a
    . intro aK
      let αa := (α φ ψ).toFun a
      let αK := (α φ ψ) '' (K φ ψ x)
      have αa_ep_αK : endpoint αK αa := by

        sorry

      have : endpoint (Set.univ : Set NNReal) αa := by
        rw [endpoint] at *
        apply boundary_of_rel_open_subset (NNReal.toReal '' Set.univ) ((↑) '' αK)
        have : IsOpen αK := αK_open φ ψ x
        rw [isOpen_induced_iff] at this
        rcases this with ⟨U, openU, U_NNR_eq_αK⟩
        use U
        constructor
        . exact openU
        . rw [← U_NNR_eq_αK]
          ext y
          simp only [Set.mem_image, Set.mem_preimage, NNReal.val_eq_coe, Set.image_univ,
            Set.mem_inter_iff, Set.mem_range]
          constructor
          . intro ⟨y', y'U, y'y⟩
            rw [← y'y]
            exact ⟨(by use y'), y'U⟩
          . intro ⟨⟨y', y'y⟩, yU⟩
            use y'
            rw [y'y]
            exact ⟨yU, rfl⟩
        constructor
        . show ↑αa ∈ NNReal.toReal '' αK
          simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, NNReal.coe_eq, exists_eq_right]
          use a
        . show ↑αa ∈ frontier (NNReal.toReal '' αK)
          exact αa_ep_αK


      -- The two endpoints of K are a and b.
      let b : NNReal := sorry
      have hb : endpoint (K φ ψ x) b := sorry
      have b_ne_a : b ≠ a := sorry

      sorry

    . rw [endpoint] at *
      contrapose a_ep_I
      simp only [not_not] at *
      let ⟨U, openU, K_eq_IU⟩ := K_open_I φ ψ x
      rw [K_eq_IU] at ha
      have : ↑a ∈ frontier ((↑) '' I φ) ∪ frontier U := by
        apply frontier_intersection_sub_union_frontiers
        exact ha
      rcases this with _ | a_frontierU
      . assumption
      have aK : ↑a ∈ NNReal.toReal '' K φ ψ x
        := Set.mem_image_of_mem NNReal.toReal a_ep_I
      rw [K_eq_IU] at aK
      rw [← closure_diff_interior] at a_frontierU
      let ⟨_, not_aU⟩ := a_frontierU
      rw [IsOpen.interior_eq openU] at not_aU
      have aU : ↑a ∈ U := Set.mem_of_mem_inter_right aK
      contradiction

end section -- x
end section -- φ, ψ, pair
end section -- M, ht
