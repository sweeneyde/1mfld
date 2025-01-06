import Mathlib
import OneMfld.ClassifyInterval
import OneMfld.NiceCharts

class IntervalChartedSpace (M : Type*) [TopologicalSpace M] extends ChartedSpace NNReal M where
  is_interval (φ : PartialHomeomorph M NNReal) (h : φ ∈ atlas) : (∃ x y, (Set.Ioo x y = φ.target)) ∨ (∃ x, (Set.Iio x = φ.target))

variable
  {M : Type*}
  [TopologicalSpace M]

def ioi_unbounded (x : NNReal) : ¬ Bornology.IsBounded (Set.Ioi x) := by sorry
def univ_unbounded : ¬ Bornology.IsBounded (Set.univ : Set NNReal) := by sorry

noncomputable instance interval_charted (ht : NicelyChartedSpace NNReal M) : IntervalChartedSpace M where
  chartAt := ht.chartAt
  atlas := ht.atlas
  mem_chart_source := ht.mem_chart_source
  chart_mem_atlas := ht.chart_mem_atlas
  is_interval (φ : PartialHomeomorph M NNReal) := by
    intro h
    have bounded := ht.is_bounded φ h
    have connected := ht.is_connected φ h

    have c := classify_connected_nnreal_interval (φ.target) (φ.open_target) (isConnected_iff_connectedSpace.mpr connected)
    rcases c with (h|h|h|h)
    · left ; assumption
    · right ; assumption
    · exfalso
      rcases h with ⟨x,h⟩
      apply ioi_unbounded x
      rw [h]
      exact bounded
    · exfalso
      apply univ_unbounded
      rw [←h]
      exact bounded
