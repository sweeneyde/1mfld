


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


lemma relu_ioo {U : Set NNReal} (h : ∃ x y, Ioo x y = Ioi 0 ∩ NNReal.toReal '' U) :
  (∃ x y, Ioo x y = U) ∨ (∃ y, Iio y = U) ∨ ({0} = U) ∨ (∅ = U):= by
  rcases h with ⟨a,b,h⟩
  by_cases hab : a < b
  · have ha : a ≥ 0 := by
      have : sInf (Set.Ioo a b) = a := csInf_Ioo hab
      rw [h] at this
      rw [←this]
      simp only [ge_iff_le]
      apply Real.sInf_nonneg
      intro x hx
      have hx' : x ∈ Set.Ioi 0 := mem_of_mem_inter_left hx
      exact le_of_lt hx'
    have hb : b ≥ 0 := by linarith
    by_cases h0 : 0 ∈ U
    · right ; left
      use ⟨ b, hb ⟩
      ext x
      simp only [mem_Iio]
      constructor
      · intro hx
        by_cases hx0 : x > 0
        · have hi : NNReal.toReal x ∈ Set.Ioi 0 := by exact hx0
          have h : NNReal.toReal x ∈ Set.Ioo a b := by
            simp only [mem_Ioo]
            constructor

        · sorry
      · intro hx
        sorry
    · left
      use ⟨ a, ha ⟩
      use ⟨ b, hb ⟩
      ext x
      simp only [mem_Ioo]
      constructor
      · intro ⟨ha', hb'⟩
        have hx' : NNReal.toReal x ∈ Set.Ioo a b := by
          apply mem_Ioo.mpr
          exact ⟨ha', hb'⟩
        rw [h] at hx'
        have hx'' : NNReal.toReal x ∈ NNReal.toReal '' U := mem_of_mem_inter_right hx'
        simp only [mem_image, NNReal.coe_inj, exists_eq_right] at hx''
        assumption
      · intro hu
        have hx1 : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hu
        have hx2 : NNReal.toReal x ∈ Set.Ioi 0 := by
          apply mem_Ioi.mpr
          apply NNReal.coe_pos.mpr
          have : x ≠ 0 := ne_of_mem_of_not_mem hu h0
          exact pos_iff_ne_zero.mpr this
        have : NNReal.toReal x ∈ Set.Ioo a b := by
          rw [h]
          exact mem_inter hx2 hx1
        exact this
  · have : Ioo a b = ∅ := Ioo_eq_empty hab
    rw [this] at h
    by_cases h0 : 0 ∈ U
    · right ; right ; left
      ext x
      constructor
      · exact fun a => mem_of_eq_of_mem a h0
      · intro hx
        simp only [mem_singleton_iff]
        by_cases hx0 : x > 0
        · have : NNReal.toReal x ∈ Set.Ioi 0 := hx0
          have this' : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hx
          have this'' : NNReal.toReal x ∈ (∅ : Set Real) := by
            rw [h]
            exact mem_inter hx0 this'
          exact False.elim this''
        · have : x ≥ 0 := by exact zero_le x
          have this' : x ≤ 0 := by exact le_of_not_lt hx0
          exact nonpos_iff_eq_zero.mp this'
    · right ; right ; right
      ext x
      simp only [mem_empty_iff_false, false_iff]
      by_cases hx0 : x > 0
      · by_contra hu
        have : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hu
        have this' : NNReal.toReal x ∈ Set.Ioi 0 := hx0
        have this'' : NNReal.toReal x ∈ Set.Ioi 0 ∩ NNReal.toReal '' U  := mem_inter hx0 this
        rw [←h] at this''
        exact this''
      · have : x ≥ 0 := by exact zero_le x
        have this' : x ≤ 0 := by exact le_of_not_lt hx0
        have this'' : x = 0 := by exact nonpos_iff_eq_zero.mp this'
        exact Eq.mpr_not (congrArg (Membership.mem U) this'') h0
  exact { toFun := φ.toFun,
          invFun := φ.invFun,
          source := φ ⁻¹' t,
          target := t,
          map_source' := by
            intro z hz
            dsimp [t]
            dsimp [t] at hz
            simp only [Set.mem_inter_iff, Set.mem_preimage] at hz
            simp only [Set.mem_inter_iff]
            assumption
          map_target' := by
            intro z hz
            dsimp [t]
            dsimp [t] at hz
            simp only [Set.mem_inter_iff, Set.mem_preimage]
            4
          left_inv' := sorry,
          right_inv' := sorry,
          open_target := IsOpen.inter φ.open_target isOpen_Ioo,
          open_source := by
            apply ContinuousOn.isOpen_preimage
            · exact φ.continuousOn_toFun
            · exact φ.open_source
            · intro x hx

              dsimp [t] at hx
              simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
              have := φ.map_target' hx.1
              have this' := φ.right_inv'

              simp only [PartialEquiv.invFun_as_coe] at this


              sorry
            · exact IsOpen.inter φ.open_target isOpen_Ioo
          continuousOn_invFun := sorry,
          continuousOn_toFun := sorry
          }



--atlas : Set (PartialHomeomorph M H)
--The atlas of charts in the ChartedSpace.

--chartAt : M → PartialHomeomorph M H
--The preferred chart at each point in the charted space.

--mem_chart_source (x : M) : x ∈ (ChartedSpace.chartAt x).source
--chart_mem_atlas (x : M) : ChartedSpace.chartAt x ∈ ChartedSpace.atlas

structure NiceChart (φ : PartialHomeomorph M NNReal) where
  in_atlas : φ ∈ ht.atlas
  bounded : Bornology.IsBounded φ.target
  connected : ConnectedSpace φ.target

theorem not_bounded_univ : ¬ Bornology.IsBounded (Set.univ : Set NNReal) := by
  apply Metric.ediam_eq_top_iff_unbounded.mp
  dsimp [EMetric.diam]
  simp only [Set.mem_univ, iSup_pos]
  dsimp [iSup]
  have f : ∀ (x : NNReal), sSup (Set.range fun (y : NNReal) => edist x y) = ⊤ := by
    intro x
    apply sSup_eq_top.mpr
    simp only [Set.mem_range, exists_exists_eq_and]
    intro b hb
    use b.toNNReal + 1 + x
    dsimp [edist]
    dsimp [PseudoMetricSpace.edist]
    push_cast
    ring_nf
    refine ENNReal.lt_iff_exists_coe.mpr ?_
    simp only [ENNReal.coe_lt_coe]
    use b.toNNReal
    apply And.intro
    · refine Eq.symm (ENNReal.coe_toNNReal ?_)
      exact LT.lt.ne_top hb
    · have : abs (-1 - b.toReal) = 1 + b.toReal := by
        have bpos' : b.toReal ≥ 0 := by exact ENNReal.toReal_nonneg
        have bpos : 1 + b.toReal ≥ 0 := by linarith
        apply (abs_eq bpos).mpr
        right
        ring
      simp only [gt_iff_lt]
      push_cast
      refine NNReal.coe_lt_coe.mp ?_
      push_cast
      refine (ENNReal.lt_ofReal_iff_toReal_lt ?_).mp ?_
      exact LT.lt.ne_top hb
      rw [this]
      refine (ENNReal.lt_ofReal_iff_toReal_lt ?_).mpr ?_
      exact LT.lt.ne_top hb
      exact lt_one_add b.toReal
  have : ⊤ ∈ Set.range fun (x : NNReal) => sSup (Set.range fun (y : NNReal) => edist x y) := by
    simp only [Set.mem_range]
    use 0
    exact f 0
  exact csSup_eq_top_of_top_mem this

theorem not_bounded_Ioi {x : NNReal} : ¬ Bornology.IsBounded (Set.Ioi x) := by
  apply Metric.ediam_eq_top_iff_unbounded.mp
  dsimp [EMetric.diam]
  simp only [Set.mem_Ioi]
  dsimp [iSup]
  have f : ∀ (x_1 : NNReal), sSup (Set.range fun (x_2 : x < x_1) => sSup (Set.range fun y => sSup (Set.range fun (_ : x < y) => edist x_1 y))) = ⊤ := by
    sorry
  have : ⊤ ∈ (Set.range fun x_1 => sSup (Set.range fun (x_2 : x < x_1) => sSup (Set.range fun y => sSup (Set.range fun (_ : x < y) => edist x_1 y)))) := by
    simp only [Set.mem_range]
    use 0
    exact f 0
  exact csSup_eq_top_of_top_mem this




theorem classify_nice_chart (φ : PartialHomeomorph M NNReal) (c : NiceChart φ) :
  (∃ (a b : NNReal), φ.target = Set.Ioo a b) ∨ (∃ (b : NNReal), φ.target = Set.Iio b) := by
  let U := φ.target
  have h : (∃ x y, Set.Ioo x y = U) ∨ (∃ x, Set.Iio x = U) ∨ (∃ x, Set.Ioi x = U) ∨ U = Set.univ := by
    apply classify_connected_nnreal_interval
    exact φ.open_target
    exact isConnected_iff_connectedSpace.mpr c.connected

  rcases h with (h|h|h|h)
  · left
    rcases h with ⟨ a, b, h ⟩
    dsimp [U] at h
    rw [←h]
    use a
    use b
  · right
    dsimp [U] at h
    rcases h with ⟨ b, h ⟩
    use b
    rw [h]
  · exfalso
    rcases h with ⟨ x, hx ⟩
    have this' : ¬ Bornology.IsBounded (Set.Ioi x) := not_bounded_Ioi
    rw [hx] at this'
    exact this' c.bounded
  · exfalso
    apply not_bounded_univ
    rw [←h]
    exact c.bounded
