import Mathlib

import OneMfld.ClosureOverlap
import OneMfld.PartialHomeomorphHelpers

lemma continuity {α : Type u} {β : Type u} [TopologicalSpace α] [TopologicalSpace β]
  (f : α → β) (U : Set α) (V : Set α) (h : V ⊆ U) (hc : ContinuousOn f U) :
  (ContinuousOn f V) := by
    exact ContinuousOn.mono hc h

lemma map_source_image {α : Type u} {β : Type u} [TopologicalSpace α] [TopologicalSpace β]
  (U : PartialHomeomorph α β) (V : Set α) (hV : V ⊆ U.source)
  : (U.toFun' '' V ⊆ U.target) := by
  rintro x hx
  simp at hx
  rcases hx with ⟨y , hyv, huy ⟩
  rw [← huy]
  exact PartialHomeomorph.map_source U (hV hyv)

structure OChart (X : Type*) [TopologicalSpace X]
  extends PartialHomeomorph X NNReal where
  target_ioo : target = Set.Ioo 0 1

structure HChart (X : Type*) [TopologicalSpace X]
  extends PartialHomeomorph X NNReal where
  target_ioo : target = Set.Ico 0 1

#check PartialHomeomorph

universe u
variable {α : Type u}
variable [TopologicalSpace α]

-- TODO: prove this
variable [LocallyConnectedSpace α]

def Overlap (U : Set α) (V : Set α) : Prop :=
  (U ∩ V).Nonempty ∧ (U \ V).Nonempty ∧ (V \ U).Nonempty

def IsUpper (S : Set NNReal) : Prop := ∃ x, S = Set.Ioo x 1
def IsLower (S : Set NNReal) : Prop := ∃ x, S = Set.Ioo 0 x
def IsOuter (S : Set NNReal) : Prop := (IsUpper S) ∨ (IsLower S)


lemma overlap_oo_is_outer {U : OChart α} {V : OChart α} (h : Overlap U.source V.source)
  (x : α) (hx : x ∈ U.source ∩ V.source) :
  IsOuter ((U.toFun') '' (connectedComponentIn (U.source ∩ V.source) x)) := by
      let phi := U.toFun'
      let W := connectedComponentIn (U.source ∩ V.source) x
      let phiW := phi '' W

      have hu : IsOpen U.source := U.open_source
      have hv : IsOpen V.source := V.open_source
      have huv := IsOpen.inter hu hv

      have ho : IsOpen phiW := by
        apply PartialHomeomorph.isOpen_image_of_subset_source
        exact IsOpen.connectedComponentIn huv
        have hwuv : W ⊆ U.source ∩ V.source := connectedComponentIn_subset (U.source ∩ V.source) x
        have huvu : (U.source ∩ V.source) ⊆ U.source := Set.inter_subset_left
        exact fun ⦃a⦄ a_1 => huvu (hwuv a_1)

      have huc : IsConnected U.source := by
        apply (partial_homeo_source_connected_iff_target_connected U.toPartialHomeomorph).mpr
        rw [U.target_ioo]
        refine isConnected_Ioo ?_
        exact zero_lt_one' NNReal

      have hm : W ⊆ U.source := by
        dsimp [W]
        have : connectedComponentIn (U.source ∩ V.source) x ⊆ (U.source ∩ V.source) :=
          connectedComponentIn_subset (U.source ∩ V.source) x
        rintro y hy
        exact Set.mem_of_mem_inter_left (this hy)

      have hw : IsConnected W
      exact isConnected_connectedComponentIn_iff.mpr hx
      have hw' : IsConnected phiW
      apply IsConnected.image hw ↑U.toPartialHomeomorph
      have hco : ContinuousOn (↑U.toPartialHomeomorph) U.source
      exact PartialHomeomorph.continuousOn U.toPartialHomeomorph
      exact ContinuousOn.mono hco hm

      have hpt : phiW ⊆ Set.Ioo 0 1
      have hpt' : phiW ⊆ U.target := by
        rintro x hx
        rcases hx with ⟨y , hyv, huy ⟩
        rw [←huy]
        exact PartialHomeomorph.map_source U.toPartialHomeomorph (hm hyv)

      have hwv : ((closure W) ∩ (V.source \ W)).Nonempty := by
        have hVconn : IsConnected V.source := by
          apply (partial_homeo_source_connected_iff_target_connected V.toPartialHomeomorph).mpr
          rw [V.target_ioo]
          exact isConnected_Ioo (zero_lt_one' NNReal)
        have hUopen : IsOpen W := by exact IsOpen.connectedComponentIn huv
        have hUV : (W ∩ V.source).Nonempty := by
          apply Set.inter_nonempty.mpr
          use x
          constructor
          · exact mem_connectedComponentIn hx
          · exact Set.mem_of_mem_inter_right hx
        have hVU : (V.source \ W).Nonempty := by
          rcases h.2.2 with ⟨y,hy⟩
          use y
          simp only [Set.mem_diff]
          constructor
          · exact Set.mem_of_mem_diff hy
          · by_contra hw
            have : y ∈ U.source := hm hw
            simp only [Set.mem_diff] at hy
            exact hy.2 this
        apply nonempty_closure_inter_diff hVconn hUopen hv hUV hVU





--

lemma overlap_ho_is_outer {U : OChart α} {V : HChart α} (h : Overlap U.source V.source)
                          (x : α) (hx : x ∈ U.source ∩ V.source) :
                          IsOuter ((U.toFun) '' (connectedComponent x)) := sorry

lemma overlap_hh_is_outer {U : HChart α} {V : HChart α} (h : Overlap U.source V.source)
                          (x : α) (hx : x ∈ U.source ∩ V.source) :
                          IsOuter ((U.toFun) '' (connectedComponent x)) := sorry

--lemma at_most_two_components {U : HChart α} {V : HChart α} :
--                             (ConnectedComponents (U.source ∩ V.source)).encard ≤ 2 := sorry
