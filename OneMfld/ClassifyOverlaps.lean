import Mathlib
import OneMfld.UnitInterval
import OneMfld.FiniteIntervalCharts
import OneMfld.IntervalCharts
import OneMfld.NiceCharts

structure OChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  target_ioo : (∃ x y, (Set.Ioo x y = target))

structure HChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  target_iio : (∃ x, (Set.Iio x = target))

structure IChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  is_interval : (∃ x y, (Set.Ioo x y = target)) ∨ (∃ x, (Set.Iio x = target))

variable
  {M : Type*}
  [TopologicalSpace M]
  [ConnectedSpace M]
  [T2Space M]

def OChart.toIChart (a : OChart M) : IChart M :=
  { a with is_interval := Or.inl a.target_ioo }

def HChart.toIChart (a : HChart M) : IChart M :=
  { a with is_interval := Or.inr a.target_iio }

def Overlap (U : Set α) (V : Set α) : Prop :=
  (U ∩ V).Nonempty ∧ (U \ V).Nonempty ∧ (V \ U).Nonempty

def does_overlap' (U : Set α) (V : Set α) (hu : ¬ U ⊆ V)
  : (U \ V).Nonempty := Set.diff_nonempty.mpr hu

def does_overlap (U : Set α) (V : Set α) (h : (U ∩ V).Nonempty) (hu : ¬ U ⊆ V) (hv : ¬ V ⊆ U)
  : Overlap U V := by
    apply And.intro
    · exact h
    · apply And.intro
      · exact does_overlap' U V hu
      · exact does_overlap' V U hv

def overlap_symm {U : Set α} {V : Set α} (h : Overlap U V) : Overlap V U := by
  dsimp [Overlap] at h
  apply And.intro
  · exact Set.inter_nonempty_iff_exists_right.mpr h.1
  · apply And.intro
    · exact h.2.2
    · exact h.2.1

lemma Overlap.nonempty {U : Set α} {V : Set α} (h : Overlap U V) : (Nonempty U) ∧ (Nonempty V) := by
  have nonempty : (U ∩ V).Nonempty := h.1
  apply And.intro
  · exact Set.Nonempty.to_subtype (Set.Nonempty.left nonempty)
  · exact Set.Nonempty.to_subtype (Set.Nonempty.right nonempty)

/-- Turn a homeomorphism of open subtypes `A ≃ₜ B` into a partial homeomorphism `X ⇀ Y`. -/
noncomputable def Homeomorph.toPartialHomeomorphOnOpens {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y} (h : A ≃ₜ B) (hA : IsOpen A) (hB : IsOpen B) :
    PartialHomeomorph X Y :=
{ h.toEquiv.toPartialEquiv with
  open_source := hA,
  open_target := hB,
  continuousOn_toFun := by
    sorry
  continuousOn_invFun := by
    sorry
}

def Interval3 := (Set.Icc (0 : Real) (3 : Real))

def handle_h_h''' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 2)
  (hb_target : b.target = Set.Iio 2)
  (ha : a.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2)
  (hb : b.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2) :
  { φ : PartialHomeomorph Interval3 M | φ.target = a.source ∪ b.source ∧ φ.source = Set.univ } := by

  let s := Interval3
  let t := Set.Ico (0 : Real) (2 : Real)
  let tc := Set.Icc (2 : Real) (3 : Real)

  let φfun : Interval3 → M := by
    rintro ⟨ x, hx ⟩
    dsimp [Interval3] at hx
    simp only [Set.mem_Icc] at hx
    exact if x < 2 then (a.symm.toFun ⟨ x, hx.1 ⟩) else (b.symm.toFun ⟨ 3 - x, by linarith ⟩ )

  have inj_on : Set.InjOn φfun (Set.univ) := by sorry

  have surj_on : Set.SurjOn φfun (Set.univ) (a.source ∪ b.source) := by
    intro x hx
    simp only [Set.image_univ, Set.mem_range, Subtype.exists]
    by_cases ha : x ∈ a.source
    · use (a.toFun x)
      have : a.toFun x ∈ a.target := by exact PartialEquiv.map_source a.toFun ha
      rw [ha_target] at this
      simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_Iio] at this
      have h0 : a.toFun x ≥ 0 := by exact zero_le (a.toFun x)
      have hi : ↑(a.toFun x) ∈ Interval3 := by
        dsimp [Interval3]
        simp only [Set.mem_Icc, NNReal.zero_le_coe, true_and]
        refine (Real.le_toNNReal_iff_coe_le ?_).mp ?_
        exact zero_le_three
        simp only [Real.toNNReal_ofNat]
        have : ↑(a.toFun x) ≤ 2 := by exact le_of_lt this
        have h23 : (2 : Real) ≤ (3 : Real) := by linarith
        exact Preorder.le_trans (a.toFun x) 2 3 this h23
      use hi
      simp only [PartialHomeomorph.toFun_eq_coe]
      dsimp [φfun]
      split_ifs with h2
      refine (PartialHomeomorph.eq_symm_apply a.symm ?_ ha).mp rfl
      simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source]
      rw [ha_target]
      simp only [Set.mem_Iio]
      exact this
      exfalso
      apply h2
      exact this
    · have xb : x ∈ b.source := by
        simp only [Set.mem_union] at hx
        tauto
      use (3 : Real) - (b.toFun x)
      have : (3 : Real) - ↑(b.toFun x) ∈ Interval3 := by
        dsimp [Interval3]
        simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right,
          NNReal.zero_le_coe, and_true]
        have : b.toFun x ∈ b.target := by exact PartialEquiv.map_source b.toPartialEquiv xb
        rw [hb_target] at this
        simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_Iio] at this
        have h23 : (2 : NNReal) ≤ 3 := by
          refine NNReal.coe_le_coe.mp ?_
          simp only [NNReal.coe_ofNat]
          linarith
        have this' : (b.toPartialHomeomorph x) ≤ 2 := by exact le_of_lt this
        have hf : (b.toPartialHomeomorph x) ≤ 3 := by
          apply Preorder.le_trans (b.toPartialHomeomorph x) (2 : NNReal) (3 : NNReal) this' h23
        exact hf
      use this
      simp only [PartialHomeomorph.toFun_eq_coe]
      dsimp [φfun]
      simp only [sub_sub_cancel]
      split_ifs with h2
      · have h1 : (b.toFun x).toReal > 1 := by
          have : 3 - (b.toFun x).toReal < 2 := by exact h2
          linarith
        have h2' : (b.toFun x).toReal < 2 := by
          have : b.toFun x ∈ b.target := by exact PartialEquiv.map_source b.toPartialEquiv xb
          rw [hb_target] at this
          simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_Iio] at this
          exact this
        have hbi : (b.toFun x) ∈ Set.Ioo 1 2 := by
          simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_Ioo]
          apply And.intro
          · exact h1
          · exact h2'
        rw [←hb] at hbi
        simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, Set.mem_inter_iff] at hbi
        rcases hbi with ⟨ x1, ⟨ hx1, hxi ⟩  ⟩
        exfalso
        apply ha
        have hxi' : b.toFun x1 = b.toFun x := by exact hxi
        have hbb : b.symm (b.toFun x1) = b.symm (b.toFun x) := by
          rw [hxi']
        simp only [PartialHomeomorph.toFun_eq_coe] at hbb
        have cx1 : b.symm (b.toPartialHomeomorph x1) = x1 := by
          refine (PartialHomeomorph.eq_symm_apply b.symm ?_ ?_).mp rfl
          simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
            PartialHomeomorph.toFun_eq_coe]
          refine PartialHomeomorph.map_source b.toPartialHomeomorph ?_
          exact Set.mem_of_mem_inter_right hx1
          simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_target]
          exact Set.mem_of_mem_inter_right hx1
        have cx : b.symm (b.toPartialHomeomorph x) = x := by
          exact PartialHomeomorph.left_inv b.toPartialHomeomorph xb
        rw [cx1] at hbb
        rw [cx] at hbb
        rw [←hbb]
        exact hx1.1
      · refine (PartialHomeomorph.eq_symm_apply b.symm ?_ xb).mp rfl
        simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source]
        rw [hb_target]
        simp only [Set.mem_Iio]
        have : ↑(b.toPartialHomeomorph x) < 2 := by
          simp only [PartialHomeomorph.toFun_eq_coe] at this
          dsimp [Interval3] at this
          simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right,
            NNReal.zero_le_coe, and_true] at this
          simp only [not_lt] at h2
          ring_nf at h2
          have h3 : ↑(b.toFun x) ≤ 3 := by exact this
          have h2' : 2 ≤ 3 - ↑(b.toFun x) := by
            sorry
          have : 2 - 3 ≤ 3 - ↑(b.toFun x) - 3 := by
            apply tsub_le_tsub
            exact h2'
            simp only [le_refl]
        exact this

  have bij_on : Set.BijOn φfun (Set.univ) (a.source ∪ b.source) := by
    have : Set.BijOn φfun (Set.univ) (φfun '' Set.univ) := by exact Set.InjOn.bijOn_image inj_on
    have image : φfun '' Set.univ = (a.source ∪ b.source) := by
      apply Set.SurjOn.image_eq_of_mapsTo surj_on
      apply Set.mapsTo_univ_iff.mpr
      intro ⟨ x, hx ⟩
      simp only [Set.mem_union]
      dsimp [φfun]
      split_ifs with h2
      left

      refine PartialHomeomorph.map_target a.toPartialHomeomorph ?_
      rw [ha_target]
      simp only [Set.mem_Iio]
      exact h2

      right
      refine PartialHomeomorph.map_target b.toPartialHomeomorph ?_
      rw [hb_target]
      simp only [Set.mem_Iio]
      dsimp [Interval3] at hx
      simp only [Set.mem_Icc] at hx
      have : 3 - x < 2 := by linarith
      exact this

    rw [image] at this
    assumption

  have nonempty : Nonempty Interval3 := by sorry

  let ψfun := Function.invFunOn φfun (Set.univ)

  have hinv : Set.InvOn ψfun φfun (Set.univ) (a.source ∪ b.source) := by sorry

  have equiv : Equiv (Set.univ : Set Interval3) (a.source ∪ b.source : Set M) := by
    exact Set.BijOn.equiv φfun bij_on

  have homeo : Homeomorph (Set.univ : Set Interval3) (a.source ∪ b.source : Set M) := by
    have : CompactSpace (Set.univ : Set Interval3) := by sorry
    have cts : Continuous equiv := by sorry
    apply Continuous.homeoOfEquivCompactToT2 cts

  have homeo' : Homeomorph (Interval3) (a.source ∪ b.source : Set M) := by sorry

  use { toFun := fun x => homeo'.toFun x
      , invFun := fun x => by
          by_cases h : x ∈ a.source ∪ b.source
          · exact homeo'.symm.toFun ⟨ x, h ⟩
          · exact ⟨ (0 : Real), by dsimp [Interval3] ; simp only [Set.mem_Icc, le_refl, Nat.ofNat_nonneg,
            and_self] ⟩
      , source := Set.univ
      , target := a.source ∪ b.source
      , map_source' := by
          intro x
          intro hx
          simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, Subtype.coe_prop]
      , map_target' := by
          intro x hx
          exact trivial
      , left_inv' := by
          intro x
          intro hx
          simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, Subtype.coe_prop, ↓reduceDIte,
            Subtype.coe_eta, Homeomorph.symm_apply_apply]
      , right_inv'  := by
          intro x
          intro hx
          simp only [Set.mem_union, Equiv.toFun_as_coe, Homeomorph.coe_toEquiv]
          split_ifs
          simp only [Homeomorph.apply_symm_apply]
      , open_source := isOpen_univ
      , open_target := IsOpen.union a.open_source b.open_source
      , continuousOn_toFun := by
          apply continuous_iff_continuousOn_univ.mp
          simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv]
          apply Continuous.comp' continuous_subtype_val
          exact Homeomorph.continuous homeo'
      , continuousOn_invFun := by
          refine ContinuousOn.union_continuousAt ?_ ?_ ?_
          exact a.open_source

      }

def handle_h_h''' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 2)
  (hb_target : b.target = Set.Iio 2)
  (ha : a.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2)
  (hb : b.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2) :
  { φ : PartialHomeomorph M Interval3 | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by

  let s := a.source ∪ b.source
  let t := a.source
  let tc := b.source \ a.source

  let target := (Set.Iic (3 : NNReal))

  let split := b.symm 1

  have closure_t : s ∩ (closure t) = a.source ∪ {split} := by
    sorry

  have source_frontier : s ∩ (frontier t) = {split} := by
    sorry

  let d (j : M) : Decidable (j ∈ t) := Classical.propDecidable (j ∈ t)

  let a' : M → Interval3 := by
    intro x
    let y : Real := a.toFun x
    have hy0 : y ≥ 0 := by sorry
    have hy3 : y < 2 := by sorry
    use y
    dsimp [Interval3]
    simp only [Set.mem_Icc]
    apply And.intro
    · linarith
    · linarith

  let f : M → Interval3
    := a.source.piecewise (a') (fun _ => ⟨ 1, by dsimp [Interval3] ; simp only [Set.mem_Icc,
      zero_le_one, Nat.one_le_ofNat, and_self] ⟩ )

  let g (x : M) : Interval3 := by
    let y : Real := b.toFun x
    have hy0 : y ≥ 0 := by sorry
    have hy3 : y < 2 := by sorry
    use 3 - y
    dsimp [Interval3]
    simp only [Set.mem_Icc, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right]
    apply And.intro
    · linarith
    · linarith

  let φfun := t.piecewise f g

  have f_split : f split = (1 : Real) := by sorry
  have g_split : g split = (1 : Real) := by sorry

  have φ_cts : ContinuousOn φfun s := by sorry

  let ψfun : Interval3 → M := by
    rintro ⟨ x, hx ⟩
    dsimp [Interval3] at hx
    simp only [Set.mem_Icc] at hx
    let x' : NNReal := ⟨ x, by linarith ⟩
    let y' : NNReal := ⟨ 3 - x, by linarith ⟩
    exact if x < 2 then (a.symm x') else (b.symm y')

  use { toFun := φfun
      , invFun := ψfun
      , source := s
      , target := Set.univ
      , map_source' := by
          intro x
          intro hx
          exact trivial
      , map_target' := by
          rintro ⟨ x, hx ⟩
          intro _
          dsimp [ψfun]
          split_ifs with h2
          · have : a.symm ⟨ x, by sorry ⟩ ∈ a.source := by sorry
            exact Set.mem_union_left b.source this
          · have : b.symm ⟨ 3 - x, by sorry ⟩ ∈ b.source := by sorry
            exact Set.mem_union_right a.source this
      , left_inv' := by
          intro x
          intro hx
          dsimp [φfun, ψfun]
          split_ifs with h2
          sorry
      , right_inv'  := by
          intro x
          intro _
          dsimp [φfun]
          by_cases hxt : ψfun x ∈ t
          · dsimp [t.piecewise]
            have : t.piecewise f g (ψfun x) = f (ψfun x) := Set.piecewise_eq_of_mem t f g hxt
            rw [this]
            dsimp [f, ψfun]



      , open_source := IsOpen.union a.open_source b.open_source
      , open_target  := isOpen_univ
      , continuousOn_toFun := φ_cts
      , continuousOn_invFun := by sorry
      }

def handle_h_h'' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 1)
  (hb_target : b.target = Set.Iio 1)
  (ha : ∃ (x : NNReal), a.toFun '' (a.source ∩ b.source) = Set.Ioo x 1)
  (hb : ∃ (y : NNReal), b.toFun '' (a.source ∩ b.source) = Set.Ioo y 1) :
  { φ : PartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by

  let s := a.source ∪ b.source
  let t := a.source
  let tc := b.source \ a.source

  let bsplit := hb.choose
  let hbsplit := hb.choose_spec

  have b_src_minus_src : b.toFun '' (b.source \ a.source) = Set.Iic bsplit := by
     sorry

  have bsplit_target : bsplit ∈ b.target := by
    dsimp [bsplit]
    have : PartialHomeomorph.IsImage b.symm b.target b.source :=
      PartialHomeomorph.isImage_source_target b.symm

  let split := b.symm.toFun bsplit
  have split_target : split ∈ b.source := by
    have : PartialHomeomorph.IsImage b.symm b.target b.source :=
      PartialHomeomorph.isImage_source_target b.symm
    dsimp [split]
    exact PartialHomeomorph.map_target b.toPartialHomeomorph bsplit_target

  have split_bsplit : b.toFun split = bsplit :=
    (PartialEquiv.eq_symm_apply b.toPartialEquiv split_target bsplit_target).mp rfl

  have b_end := b.target_iio.choose
  have hb_end := b.target_iio.choose_spec

  -- tc maps via b to Set.Iic y
  have b_inter : PartialHomeomorph.IsImage b.toPartialHomeomorph (a.source ∩ b.source) (Set.Ioo bsplit 1) := by
    have : b.toFun '' (a.source ∩ b.source) = Set.Ioo bsplit 1 := by
      dsimp [bsplit]
      exact hbsplit
    dsimp [PartialHomeomorph.IsImage]
    intro x hx
    apply Iff.intro
    · intro hx'
      rw [←this] at hx'
      simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, Set.mem_inter_iff] at hx'
      rcases hx' with ⟨ x', ⟨ ⟨ hxa, hxb ⟩, hxc  ⟩  ⟩
      have : Set.InjOn b.toFun b.source := by exact PartialEquiv.injOn b.toPartialEquiv
      specialize this hxb hx hxc
      rw [←this]
      exact Set.mem_inter hxa hxb
    · intro hx'
      rw [←this]
      simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_image, Set.mem_inter_iff]
      use x
      simp only [and_true]
      exact hx'

  have b_tc : PartialHomeomorph.IsImage b.toPartialHomeomorph tc (Set.Iic bsplit) := by
    have : PartialHomeomorph.IsImage b.toPartialHomeomorph b.source b.target :=
      PartialHomeomorph.isImage_source_target b.toPartialHomeomorph
    dsimp [tc]
    have : PartialHomeomorph.IsImage b.toPartialHomeomorph (b.source \ a.source) (b.target \ Set.Iic bsplit) :=
      by refine PartialHomeomorph.IsImage.of_image_eq
         apply?
    apply?
    apply?
    sorry
  --  have b_image : PartialHomeomorph.IsImage b.toPartialHomeomorph b.source b.target := by
  --    exact PartialHomeomorph.isImage_source_target b.toPartialHomeomorph
  --  rw [←hb_end] at b_image
  --  dsimp [tc]
  --  sorry

  have b_tc_symm : PartialHomeomorph.IsImage b.symm (Set.Iic bsplit) tc := by
    sorry
  --  have b_image : PartialHomeomorph.IsImage b.toPartialHomeomorph b.source b.target := by
  --    exact PartialHomeomorph.isImage_source_target b.toPartialHomeomorph
  --  rw [←hb_end] at b_image
  --  dsimp [tc]
  --  sorry

  have frontier_tc : PartialHomeomorph.IsImage b.toPartialHomeomorph (frontier tc) ({bsplit}) := by
    have : frontier (Set.Iic bsplit) = { bsplit } := by exact frontier_Iic
    rw [←this]
    exact PartialHomeomorph.IsImage.frontier b_tc

  have frontier_tc_symm : PartialHomeomorph.IsImage b.symm {bsplit} (frontier tc) := by
    have : frontier (Set.Iic bsplit) = { bsplit } := by exact frontier_Iic
    rw [←this]
    exact PartialHomeomorph.IsImage.frontier b_tc_symm

  have frontier_split : {split} = b.source ∩ (frontier tc) := by
    have : b.symm bsplit ∈ frontier tc := by
      dsimp [PartialHomeomorph.IsImage] at frontier_tc_symm
      specialize frontier_tc_symm bsplit_target
      simp only [Set.mem_singleton_iff, iff_true] at frontier_tc_symm
      assumption

    have lhs : { split } ⊆ b.source ∩ (frontier tc) := by
      simp only [Set.subset_inter_iff, Set.singleton_subset_iff]
      apply And.intro
      · exact split_target
      · exact this

    have rhs : b.source ∩ frontier tc ⊆ { split } := by
      intro x ⟨ hx1, hx2 ⟩
      dsimp [PartialHomeomorph.IsImage] at frontier_tc
      specialize frontier_tc hx1
      simp only [Set.mem_singleton_iff] at this
      simp only [Set.mem_singleton_iff] at frontier_tc
      rw [←split_bsplit] at frontier_tc
      have := frontier_tc.mpr hx2
      simp only [Set.mem_singleton_iff]
      have inj : Set.InjOn b.toFun b.source := by exact PartialEquiv.injOn b.toPartialEquiv
      dsimp [Set.InjOn] at this
      specialize inj hx1 split_target
      apply inj
      assumption

    exact Set.Subset.antisymm lhs rhs

  -- --------------------------------

  have closure_t : s ∩ (closure t) = a.source ∪ {split} := by
    sorry

  have source_frontier : s ∩ (frontier t) = {split} := by
    sorry

  let d (j : M) : Decidable (j ∈ t) := Classical.propDecidable (j ∈ t)

  let f : M → Real
    := a.source.piecewise (fun x => ((a.toFun x) : Real)) (fun _ => 1)

  let g (x : M) : Real := by
    let y : Real := b.toFun x
    exact (bsplit - y) + 1

  let φfun := t.piecewise f g

  have f_split : f split = 1 := by sorry
  have g_split : g split = 1 := by sorry

  have φ_cts : ContinuousOn φfun s := by
    apply ContinuousOn.piecewise
    rw [source_frontier]
    simp only [Set.mem_singleton_iff, forall_eq]
    · rw [f_split, g_split]
    · rw [closure_t]
      apply ContinuousOn.union_continuousAt a.open_source
      · dsimp [f]
        apply ContinuousOn.piecewise ?_ ?_ ?_
        simp only [NNReal.coe_eq_one, and_imp]
        · intro x
          intro hx
          have : a.source ∩ frontier a.source = ∅ := by sorry
          rw [this] at hx
          simp only [Set.mem_empty_iff_false] at hx
        · have : a.source ∩ closure a.source = a.source := by sorry
          rw [this]
          refine Continuous.comp_continuousOn' ?_ ?_
          exact NNReal.continuous_coe
          exact PartialHomeomorph.continuousOn a.toPartialHomeomorph
        · exact continuousOn_const
      · simp only [Set.mem_singleton_iff, forall_eq]

    ·

  --


  have frontier_tc : b.toFun '' (frontier tc) = { bsplit } := by
    have : frontier (Set.Iic bsplit) = { bsplit } := by exact frontier_Iic
    rw [←this]


  have b_tc : b.toFun '' tc = Set.Iic bsplit := by sorry

  have homeo_tc : Homeomorph tc (Set.Iic bsplit) := by
    apply?

  have frontier_tc : b.toFun '' (frontier tc) = { bsplit } := by
    have : frontier (Set.Iic bsplit) = { bsplit } := by exact frontier_Iic
    rw [←this]
    rw [←b_tc]
    apply Homeomorph.image_frontier b


  -- want split to be the point in b.source which is in the frontier of a.source



  let split : M := by sorry
  let hsplit : split ∈ a.source ∩ b.source := by sorry

def handle_h_h' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 1)
  (ha : ∃ (x : NNReal), a.toFun '' (a.source ∩ b.source) = Set.Ioo x 1)
  (hb : ∃ (y : NNReal), b.toFun '' (a.source ∩ b.source) = Set.Ioo y 1) :
  { φ : PartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by

  let split : M := by sorry
  let hsplit : split ∈ a.source ∩ b.source := by sorry

  let a_split : Real := a.toFun split
  let b_split : Real := b.toFun split

  let interval := Set.Icc 0 (a_split + b_split)

  let f (x : M) := ((a.toFun x) : Real)

  have f_cts : ContinuousOn f a.source := by
    dsimp [f]
    refine Continuous.comp_continuousOn' ?_ ?_
    · exact NNReal.continuous_coe
    · exact PartialHomeomorph.continuousOn a.toPartialHomeomorph

  let g (x : M) : Real := by
    let y  : Real := b.toFun x
    exact (b_split - y) + a_split

  let a_side := a.source ∩ (a.toFun ⁻¹' Set.Iic (a.toFun split))
  let b_side := b.source ∩ (b.toFun ⁻¹' Set.Iic (b.toFun split))

  -- a_side ∩ b_side = { split }

  let s := a.source ∪ b.source
  let t := a_side

  have stt : s ∩ t = t := by
    dsimp [s]
    simp only [Set.inter_eq_right]
    dsimp [t]
    dsimp [a_side]
    apply Set.subset_union_compl_iff_inter_subset.mp
    refine
      Set.subset_union_of_subset_left ?_
        (↑a.toPartialHomeomorph ⁻¹' Set.Iic (a.toPartialHomeomorph split))ᶜ
    exact Set.subset_union_left

  let d (j : M) : Decidable (j ∈ t) := Classical.propDecidable (j ∈ t)

  have ha : a.toFun split = a_split := rfl

  have ga : g split = a_split := by
    dsimp [g]
    dsimp [b_split]
    ring

  have fa : f split = a_split := by
    dsimp [f]
    dsimp [a_split]

  let φfun := t.piecewise f g

  have image : PartialHomeomorph.IsImage a.toPartialHomeomorph a_side (Set.Iic (a.toFun split)) := by
    simp only [PartialHomeomorph.toFun_eq_coe]
    dsimp [a_side]
    refine PartialHomeomorph.IsImage.of_preimage_eq ?_
    simp only [Set.right_eq_inter, Set.inter_subset_left]

  have image' : PartialHomeomorph.IsImage a.toPartialHomeomorph.symm (Set.Iic (a.toFun split)) a_side := by
    exact PartialHomeomorph.IsImage.symm image

  have image_frontier' : PartialHomeomorph.IsImage a.toPartialHomeomorph (frontier t) ({a.toFun split} : Set NNReal) := by
    dsimp [t]
    have image_f : PartialHomeomorph.IsImage a.toPartialHomeomorph (frontier t) (frontier (Set.Iic (a.toFun split))) := by
      exact PartialHomeomorph.IsImage.frontier image
    have : frontier (Set.Iic (a.toFun split)) =  ({a.toFun split} : Set NNReal) := frontier_Iic
    rw [this] at image_f
    exact image_f

  have image_frontier : PartialHomeomorph.IsImage a.toPartialHomeomorph.symm ({a.toFun split} : Set NNReal) (frontier t) := by
    dsimp [t]
    have image_f : PartialHomeomorph.IsImage a.toPartialHomeomorph.symm (frontier (Set.Iic (a.toFun split))) (frontier t) := by
      exact PartialHomeomorph.IsImage.frontier image'
    have : frontier (Set.Iic (a.toFun split)) =  ({a.toFun split} : Set NNReal) := frontier_Iic
    rw [this] at image_f
    exact image_f

  have closure_image : PartialHomeomorph.IsImage a.toPartialHomeomorph (closure t) (Set.Iic (a.toFun split)) := by
    have image : PartialHomeomorph.IsImage a.toPartialHomeomorph (closure t) (closure (Set.Iic (a.toFun split))) := by
      exact PartialHomeomorph.IsImage.closure image
    have : closure (Set.Iic (a.toFun split)) = (Set.Iic (a.toFun split)) := closure_Iic (a.toPartialEquiv split)
    rw [this] at image
    exact image

  have compact_t : IsCompact t := by
    have : IsCompact (Set.Icc 0 (a.toFun split)) := by exact isCompact_Icc
    have e : (Set.Icc 0 (a.toFun split)) = (Set.Iic (a.toFun split)) := by
      ext x
      simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_Icc, zero_le, true_and, Set.mem_Iic]
    rw [e] at this
    have i : PartialHomeomorph.IsImage a.toPartialHomeomorph.symm (Set.Iic (a.toFun split)) t := by exact
      image'
    have homeo : Homeomorph t (Set.Iic (a.toFun split)) := sorry
    apply (Homeomorph.isCompact_image homeo).mp
    sorry

  have closed_t : IsClosed t := IsCompact.isClosed compact_t
  have closure_t : closure t = t := by exact closure_eq_iff_isClosed.mpr closed_t

  have frontier_t' : a.source ∩ frontier t = { split } := by
    ext x
    apply Iff.intro
    · intro hx
      dsimp [PartialHomeomorph.IsImage] at image_frontier'
      simp only [Set.mem_inter_iff] at hx
      specialize image_frontier' hx.1
      have := image_frontier'.mpr hx.2
      simp only [Set.mem_singleton_iff] at this
      have inj : Set.InjOn a.toFun a.source := by exact PartialEquiv.injOn a.toPartialEquiv
      dsimp [Set.InjOn] at inj
      specialize inj hx.1 (Set.mem_of_mem_inter_left hsplit)
      apply inj
      assumption
    · intro hx
      have : (a.toFun split) ∈ a.target := by exact PartialEquiv.map_source a.toPartialEquiv (Set.mem_of_mem_inter_left hsplit)
      have : (a.toFun split) ∈ a.symm.source := this
      specialize image_frontier this
      have : x = split := hx
      rw [this]
      simp only [PartialHomeomorph.toFun_eq_coe, Set.mem_singleton_iff, iff_true] at image_frontier
      have : a.symm (a.toPartialHomeomorph split) = split := PartialHomeomorph.left_inv a.toPartialHomeomorph this
      rw [this] at image_frontier

      simp only [Set.mem_inter_iff]
      apply And.intro
      · exact Set.mem_of_mem_inter_left hsplit
      · exact image_frontier

  have frontier_t : frontier t = { split } := by
    have ts : t ⊆ a.source := by exact Set.inter_subset_left
    have fc : frontier t ⊆ closure t := by exact frontier_subset_closure
    have : closure t = t := by exact closure_eq_iff_isClosed.mpr closed_t
    rw [this] at fc
    have fs : frontier t ⊆ a.source := by exact fun ⦃a⦄ a_1 => ts (fc a_1)
    have : frontier t = a.source ∩ frontier t := by exact Set.right_eq_inter.mpr fs
    rw [this]
    exact frontier_t'

  -- (s ∩ closure tᶜ)
  have : s ∩ closure (tᶜ) ⊆ closure (s ∩ tᶜ) := by
    have open_s : IsOpen s := by
      dsimp [s]
      refine IsOpen.union (by exact a.open_source) (by exact b.open_source)
    exact IsOpen.inter_closure open_s


  have split_in_a : split ∈ a.source := Set.mem_of_mem_inter_left hsplit

  have φ_cts : ContinuousOn φfun s := by
    apply ContinuousOn.piecewise
    · rw [frontier_t]
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_imp]
      intro x hxs hx
      rw [hx, fa, ga]
    · rw [closure_t]
      rw [stt]
      have : t ⊆ a.source := by exact Set.inter_subset_left
      exact ContinuousOn.mono f_cts this
    ·

  let φ : PartialHomeomorph M Real :=
  { toFun := φfun
  , invFun := by sorry
  , source : Set M := a.source ∪ b.source
  , target := Set.Icc (0 : Real) (1 : Real)
  , map_source' := by
      intro x
      intro hx
      simp only [Set.mem_Icc]
      dsimp [φfun]
      by_cases xt : x ∈ t
      · have : t.piecewise f g x = f x := Set.piecewise_eq_of_mem t f g xt
        rw [this]
        have : a.toFun x ∈ a.target := by
          dsimp [f]
          apply PartialHomeomorph.map_source a.toPartialHomeomorph
          exact Set.mem_of_mem_inter_left xt
        rcases a.target_iio with ⟨ z, hz ⟩
        rw [ha_target] at this
        simp only [Set.mem_Iio] at this
        apply And.intro
        · exact NNReal.zero_le_coe
        · exact le_of_lt this
      · have : t.piecewise f g x = g x := Set.piecewise_eq_of_not_mem t f g xt
        rw [this]

        have bx_min' : (b.toPartialHomeomorph x : Real) / (b_split : Real) ≥ 0 := by sorry
        have bx_max' : (b.toPartialHomeomorph x : Real) / (b_split : Real) ≤ 1 := by sorry
        have a_min'' : (1 : Real) - (a_split : Real) ≤ 1 := by sorry
        have a_min''' : (1 : Real) - (a_split : Real) ≥ 0 := by sorry

        apply And.intro
        · dsimp [g]
          have : (b.toPartialHomeomorph x : Real) / (b_split : Real) * (1 - (a_split : Real)) ≤ 1 := by
            exact mul_le_one₀ bx_max' a_min''' a_min''
          linarith
        · dsimp [g]
          have : (b.toPartialHomeomorph x : Real) / (b_split : Real) * ((a_split : Real) - 1) ≤ 1 * ((a_split : Real) - 1) := by
            apply mul_le_mul_of_nonneg
            linarith
            linarith
            linarith
            ring_nf at a_min'''
            ring_nf

            exact a_min'''
            exact a_min'''
          linarith


  , map_target'  := by
      intro x
      intro hx
      sorry
  , left_inv' := by sorry
  , right_inv'  := by sorry
  , open_source := IsOpen.union (a.open_source) (b.open_source)
  , open_target := by sorry
  , continuousOn_toFun := φ_cts
  , continuousOn_invFun := by sorry
  }
  use φ
  simp only [Set.mem_setOf_eq]


  sorry

def handle_h_h' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { φ : PartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by
  sorry

def handle_h_h (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  Homeomorph M UnitInterval := by
  let ⟨ φ, ⟨ hφ, hs ⟩ ⟩ := handle_h_h' a b h
  have ho : IsOpen φ.source := by exact φ.open_source
  have hc : IsClosed φ.source := by
    have cpct : IsCompact φ.source := by
      have cpct' : CompactSpace φ.target := by
        rw [hs]
        apply isCompact_iff_compactSpace.mp ?_
        exact isCompact_iff_isCompact_univ.mp isCompact_Icc
      have h : Homeomorph φ.target φ.source := φ.toHomeomorphSourceTarget.symm
      apply isCompact_iff_isCompact_univ.mpr
      have : CompactSpace φ.source := by exact Homeomorph.compactSpace h
      exact CompactSpace.isCompact_univ
    exact IsCompact.isClosed cpct
  have : φ.source = Set.univ := by
    have hco : IsClopen φ.source := ⟨hc, ho⟩
    have he : IsPreconnected (Set.univ : Set M) := isPreconnected_univ
    have ha : Nonempty a.source := (Overlap.nonempty h).1
    have hφn : Nonempty φ.source := by
      rw [hφ]
      refine Set.Nonempty.to_subtype ?_
      refine Set.Nonempty.inl ?_
      exact Set.Nonempty.of_subtype
    have he' := he.subset_isClopen hco
    have nonempty : a.source.Nonempty := Set.Nonempty.of_subtype
    simp only [Set.univ_inter, Set.univ_subset_iff] at he'
    apply he'
    exact Set.Nonempty.of_subtype
  have hh : Homeomorph φ.source φ.target := by exact φ.toHomeomorphSourceTarget
  rw [this] at hh
  rw [hs] at hh
  exact φ.toHomeomorphOfSourceEqUnivTargetEqUniv this hs


def handle_o_o (a : OChart M) (b : OChart M) (h : Overlap a.source b.source) :
  (Homeomorph M Circle) ⊕ { f : OChart M | f.source = a.source ∪ b.source } := by
  sorry

def handle_o_h (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { f : HChart M | f.source = a.source ∪ b.source } := by
  sorry

def handle_o_h' (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) (hc : IsConnected (a.source ∩ b.source):
  { f : HChart M | f.source = a.source ∪ b.source } := by

  sorry
