import Mathlib
import OneMfld.ClassifyInterval
import OneMfld.LocallyConnected

-- class OneManifold (M : Type*) [TopologicalSpace M] [T2Space M] extends ChartedSpace NNReal M

variable
  {M : Type*}
  [TopologicalSpace M]

noncomputable def improved_chart (φ : PartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : PartialHomeomorph M NNReal | (x ∈ ψ.source ∧ Bornology.IsBounded ψ.target) } := by

  let y := φ.toFun x

  by_cases h0 : y > 0
  · let interval := Set.Ioo (y-1) (y+1)
    let t := φ.target ∩ interval
    let s := φ.symm '' t
    let sOpen : IsOpen s := by
      apply (PartialHomeomorph.isOpen_symm_image_iff_of_subset_target φ (by exact
        Set.inter_subset_left)).mpr
      exact IsOpen.inter φ.open_target isOpen_Ioo
    let φ' := φ.restrOpen s sOpen

    use φ'
    apply And.intro
    · dsimp [φ']
      simp only [Set.mem_inter_iff]
      apply And.intro
      · exact h
      · dsimp [s]
        simp only [Set.mem_image]
        use y
        apply And.intro
        · apply Set.mem_inter
          · exact PartialEquiv.map_source φ.toPartialEquiv h
          · apply Set.mem_Ioo.mpr
            apply And.intro
            · refine NNReal.coe_lt_coe.mp ?_
              simp only [NNReal.coe_lt_coe, tsub_lt_self_iff, zero_lt_one, and_true]
              exact h0
            · simp only [lt_add_iff_pos_right, zero_lt_one]
        · exact PartialHomeomorph.left_inv φ h
    · have bi : Bornology.IsBounded interval := Metric.isBounded_Ioo (y - 1) (y + 1)
      apply Bornology.IsBounded.subset bi
      dsimp [φ']
      intro z hz
      have hz' : z ∈ ↑φ.symm ⁻¹' s := Set.mem_of_mem_inter_right hz
      dsimp [s] at hz'
      simp only [Set.mem_preimage, Set.mem_image] at hz'
      rcases hz' with ⟨ z', hz1, hz2 ⟩
      have : z' = z := by
        have this : Set.InjOn φ.symm φ.target := PartialHomeomorph.injOn φ.symm
        apply this
        · exact Set.mem_of_mem_inter_left hz1
        · exact Set.mem_of_mem_inter_left hz
        exact hz2
      rw [←this]
      dsimp [t] at hz1
      exact Set.mem_of_mem_inter_right hz1

  · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h0
    let interval := Set.Iio (1 : NNReal)
    let t := φ.target ∩ interval
    let s := φ.symm '' t
    let sOpen : IsOpen s := by
      apply (PartialHomeomorph.isOpen_symm_image_iff_of_subset_target φ (by exact
        Set.inter_subset_left)).mpr
      exact IsOpen.inter φ.open_target isOpen_Iio
    let φ' := φ.restrOpen s sOpen

    use φ'
    apply And.intro
    · dsimp [φ']
      simp only [Set.mem_inter_iff]
      apply And.intro
      · exact h
      · dsimp [s]
        simp only [Set.mem_image]
        use y
        apply And.intro
        · apply Set.mem_inter
          · exact PartialEquiv.map_source φ.toPartialEquiv h
          · exact Set.mem_Iio.mpr (by
                                     rw [h0]
                                     exact zero_lt_one' NNReal)
        · exact PartialHomeomorph.left_inv φ h
    · have bi : Bornology.IsBounded interval := by
        have : interval = Set.Ico 0 1 := by
          dsimp [interval]
          ext z
          simp only [Set.mem_Iio, Set.mem_Ico, zero_le, true_and]
        rw [this]
        exact Metric.isBounded_Ico 0 1
      apply Bornology.IsBounded.subset bi
      dsimp [φ']
      intro z hz
      have hz' : z ∈ ↑φ.symm ⁻¹' s := Set.mem_of_mem_inter_right hz
      dsimp [s] at hz'
      simp only [Set.mem_preimage, Set.mem_image] at hz'
      rcases hz' with ⟨ z', hz1, hz2 ⟩
      have : z' = z := by
        have this : Set.InjOn φ.symm φ.target := PartialHomeomorph.injOn φ.symm
        apply this
        · exact Set.mem_of_mem_inter_left hz1
        · exact Set.mem_of_mem_inter_left hz
        exact hz2
      rw [←this]
      dsimp [t] at hz1
      exact Set.mem_of_mem_inter_right hz1

noncomputable def improved_chart' (φ : PartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) (bounded : Bornology.IsBounded φ.target) :
  { ψ : PartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧ ConnectedSpace ψ.target } := by

  let y := φ.toFun x

  let t := connectedComponentIn φ.target y
  let s := φ.symm '' t

  let sOpen : IsOpen s := by
    apply PartialHomeomorph.isOpen_image_symm_of_subset_target φ
    apply IsOpen.connectedComponentIn
    · exact φ.open_target
    · exact connectedComponentIn_subset φ.target y

  let ψ := φ.restrOpen s sOpen
  use ψ

  apply And.intro
  · dsimp [ψ]
    simp only [Set.mem_inter_iff]
    apply And.intro
    · exact h
    · dsimp [s]
      simp only [Set.mem_image]
      use y
      apply And.intro
      · apply mem_connectedComponentIn
        exact PartialEquiv.map_source φ.toPartialEquiv h
      · exact PartialHomeomorph.left_inv φ h
  · apply And.intro
    · have : ψ.target ⊆ φ.target := by
        intro z hz
        exact Set.mem_of_mem_inter_left hz
      exact Bornology.IsBounded.subset bounded this
    · dsimp [ψ]
      apply isConnected_iff_connectedSpace.mp
      dsimp [s]
      have : (φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t)) = t := by
        have ht : t ⊆ φ.target := by exact connectedComponentIn_subset φ.target y
        ext z
        apply Iff.intro
        · intro hz
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image] at hz
          rcases hz with ⟨hz1, ⟨z', hz2, hz3⟩ ⟩
          have this : Set.InjOn φ.symm φ.target := PartialHomeomorph.injOn φ.symm
          have this' : z' = z := by
            apply this
            · apply ht
              exact hz2
            · exact hz1
            exact hz3
          rw [←this']
          exact hz2
        · intro hz
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
          apply And.intro
          · exact ht hz
          · use z
      rw [this]
      apply isConnected_connectedComponentIn_iff.mpr
      exact PartialEquiv.map_source φ.toPartialEquiv h

noncomputable def nice_chart (φ : PartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : PartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧ ConnectedSpace ψ.target } := by
  rcases (improved_chart φ x h) with ⟨ φ', h1, h2 ⟩
  rcases (improved_chart' φ' x h1 h2) with ⟨ φ'', h1, h2, h3 ⟩
  use φ''
  simp only [Set.mem_setOf_eq]
  exact ⟨ h1, ⟨ h2, h3 ⟩ ⟩

lemma nice_chart_source {φ : PartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  x ∈ (nice_chart φ x h).1.source := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.1

lemma nice_chart_bounded {φ : PartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  Bornology.IsBounded (nice_chart φ x h).1.target := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.2.1

lemma nice_chart_connected {φ : PartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  ConnectedSpace (nice_chart φ x h).1.target := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.2.2

structure NiceChartAt (x : M) where
  chart : PartialHomeomorph M NNReal
  mem_chart_source : x ∈ chart.source
  bounded : Bornology.IsBounded chart.target
  connected : ConnectedSpace chart.target

class NicelyChartedSpace (H : Type*) [TopologicalSpace H] [Bornology H] (M : Type*) [TopologicalSpace M] extends ChartedSpace H M where
    is_bounded (φ : PartialHomeomorph M H) (h : φ ∈ atlas) : Bornology.IsBounded φ.target
    is_connected (φ : PartialHomeomorph M H) (h : φ ∈ atlas) : ConnectedSpace φ.target

noncomputable def nicely_charted (ht : ChartedSpace NNReal M) : NicelyChartedSpace NNReal M where
  chartAt := by
    intro x
    let c := ht.chartAt x
    let c' := nice_chart (ht.chartAt x) x (ht.mem_chart_source x)
    exact c'.1
  atlas := let f x := (nice_chart (ht.chartAt x) x (ht.mem_chart_source x)).1
    Set.image f (Set.univ : Set M)
  mem_chart_source (x : M) := by
    simp only [Set.mem_setOf_eq]
  chart_mem_atlas (x : M) := by
    simp only [Set.mem_setOf_eq, Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  is_bounded (φ : PartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp at h
    rcases h with ⟨ y, hy ⟩
    rw [←hy]
    apply nice_chart_bounded
  is_connected (φ : PartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp at h
    rcases h with ⟨ y, hy ⟩
    rw [←hy]
    apply nice_chart_connected


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
