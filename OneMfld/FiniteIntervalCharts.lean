import Mathlib
import OneMfld.IntervalCharts
import OneMfld.FinitelyCharted

class FinitelyIntervalChartedSpace (M : Type*) [TopologicalSpace M] extends IntervalChartedSpace M where
  is_finite : Set.Finite atlas

variable
  {M : Type*}
  [TopologicalSpace M]
  [CompactSpace M]

noncomputable def finitely_interval_charted (ht : IntervalChartedSpace M) : FinitelyIntervalChartedSpace M := by
  have c : { ht' : ChartedSpace NNReal M | Set.Finite ht'.atlas ∧ ht'.atlas ⊆ ht.atlas } := choose_charts
  rcases c with ⟨ ht', c1, c2 ⟩

  exact { ht' with
          is_finite := c1
        , is_interval := by
            intro x hx
            apply ht.is_interval
            apply c2
            exact hx
         }
