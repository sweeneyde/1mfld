


class Topological1ManifoldWithBoundary (X : Type u) [TopologicalSpace X] [T2Space X] extends ChartedSpace NNReal X

class ChartedSpaceWithConnectedCharts (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] extends ChartedSpace H M where
  source_connected : ∀ x, IsConnected (chartAt x).source

def connected_chart {M : Type*} [TopologicalSpace M]  [LocallyConnectedSpace M] (x : M) (f : PartialHomeomorph M NNReal) : PartialHomeomorph M NNReal :=
  let src := f.source
  f.restrOpen (connectedComponentIn src x) (IsOpen.connectedComponentIn f.open_source)



def is_finite_open_interval (U : Set Real) := ∃ (x : Real), ∃ (y : Real), (Set.Ioo x y = U)
def is_left_open_interval (U : Set Real) := ∃ (x : Real), (Set.Iio x = U)


theorem setOf_isPreconnected_eq_of_ordered :
    { s : Set α | IsPreconnected s } =
      -- bounded intervals
      range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      -- unbounded intervals and `univ`
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by

-- def classify_intervals (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :

--instance {M : Type*} [TopologicalSpace M] [X : ChartedSpace NNReal M] : ChartedSpaceWithConnectedCharts NNReal M where
--  atlas : Set (PartialHomeomorph M NNReal) := X.atlas
--  chartAt : M → PartialHomeomorph M NNReal := X.chartAt
--  mem_chart_source : ∀ x, x ∈ (X.chartAt x).source := X.mem_chart_source
--  chart_mem_atlas : ∀ x, X.chartAt x ∈ X.atlas := sorry
--  source_connected : ∀ x, IsConnected (X.chartAt x).source := sorry

def restrict_charts (M : Type*) [TopologicalSpace M] [LocallyConnectedSpace M] (X : ChartedSpace NNReal M) : ChartedSpaceWithConnectedCharts NNReal M where
  chartAt (x : M) : PartialHomeomorph M NNReal :=
    let src := (X.chartAt x).source
    (X.chartAt x).restrOpen
      (connectedComponentIn src x)
      (IsOpen.connectedComponentIn (X.chartAt x).open_source)
  source_connected (x : M) : IsConnected (ChartedSpaceWithConnectedCharts.chartAt x).source :=
    by


--  mem_chart_source (x : M) : x ∈ (X.chartAt x).source := ChartedSpace.mem_chart_source x
--  atlas : Set (PartialHomeomorph M NNReal) := X.atlas
--  chart_mem_atlas : ∀ x, X.chartAt x ∈ X.atlas := sorry
