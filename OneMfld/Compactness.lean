import Mathlib
import OneMfld.FiniteIntervalCharts

variable
  {M : Type*}
  [TopologicalSpace M]

lemma noncompact_ioo (x y : NNReal) (hxy : x < y) : ¬ CompactSpace (Set.Ioo x y) := by sorry

lemma noncompact_iio (x : NNReal) (hx : 0 < x) : ¬ CompactSpace (Set.Iio x) := by sorry

lemma noncompact_target (ht : FinitelyIntervalChartedSpace M) (z : M) (a : PartialHomeomorph M NNReal) (ha : a ∈ ht.atlas) (hz : z ∈ a.source) : ¬ CompactSpace (a.target) := by
    have := ht.is_interval a ha
    rcases this with (h|h)
    · rcases h with ⟨ x, y, h ⟩
      rw [←h]
      have hz' : a.toFun z ∈ a.target := by exact PartialEquiv.map_source a.toPartialEquiv hz
      rw [←h] at hz'
      simp only [Set.mem_Ioo] at hz'
      rcases hz' with ⟨ hxz, hzy ⟩
      have hxy : x < y := gt_trans hzy hxz
      apply noncompact_ioo x y hxy
    · rcases h with ⟨ x, h ⟩
      rw [←h]
      have hz' : a.toFun z ∈ a.target := by exact PartialEquiv.map_source a.toPartialEquiv hz
      rw [←h] at hz'
      simp only [Set.mem_Iio] at hz'
      have hx : 0 < x := by exact pos_of_gt hz'
      apply noncompact_iio x hx
