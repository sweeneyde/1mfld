import Mathlib
import OneMfld.UnitInterval
import OneMfld.FiniteIntervalCharts
import OneMfld.IntervalCharts
import OneMfld.NiceCharts

variable
  {M : Type*}
  [TopologicalSpace M]
  [ConnectedSpace M]

structure OChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  target_ioo : (∃ x y, (Set.Ioo x y = target))

structure HChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  target_iio : (∃ x, (Set.Iio x = target))

structure IChart (M : Type*) [TopologicalSpace M]
  extends PartialHomeomorph M NNReal where
  is_interval : (∃ x y, (Set.Ioo x y = target)) ∨ (∃ x, (Set.Iio x = target))

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

def handle_h_h (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  Homeomorph M UnitInterval := by
  sorry

def handle_o_o (a : OChart M) (b : OChart M) (h : Overlap a.source b.source) :
  (Homeomorph M Circle) ⊕ { f : OChart M | f.source = a.source ∪ b.source } := by
  sorry

def handle_o_h (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { f : HChart M | f.source = a.source ∪ b.source } := by
  sorry

noncomputable def replace_charts (ht : FinitelyIntervalChartedSpace M)
  {a : PartialHomeomorph M NNReal} (ha : a ∈ ht.atlas)
  {b : PartialHomeomorph M NNReal} (hb : b ∈ ht.atlas)
  (f : IChart M) (hf : f.source = a.source ∪ b.source ) :
  { ht' : FinitelyIntervalChartedSpace M | Nat.card ht'.atlas = Nat.card ht.atlas - 1 } := by sorry

lemma nonempty_atlas (ht : FinitelyIntervalChartedSpace M) : ht.atlas.Nonempty := by
  by_contra nonempty
  have he : Nonempty M := ConnectedSpace.toNonempty
  have x := he.some
  let chart := ht.chartAt x
  have hc : chart ∈ ht.atlas := ht.chart_mem_atlas x
  exfalso
  exact nonempty (Set.nonempty_of_mem hc)

lemma more_than_one_chart [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) : Nat.card ht.atlas > 1 := by
  have nonempty := nonempty_atlas ht
  have hzero : Nat.card ht.atlas > 0 := by
    refine (Set.natCard_pos ?_).mpr nonempty
    exact ht.is_finite
  by_contra htwo
  have hone : Nat.card ht.atlas = 1 := by linarith

  have he : ∃ (a : PartialHomeomorph M NNReal), ht.atlas = { a } := Set.ncard_eq_one.mp hone
  rcases he with ⟨a,ha⟩

  have h : a.source = Set.univ := by
    ext x
    apply Iff.intro
    · exact fun _ => trivial
    · intro hx
      let c := ht.chartAt x

      have : c ∈ ht.atlas := ht.chart_mem_atlas x
      have : c = a := by
        rw [ha] at this
        exact this
      rw [←this]
      exact ht.mem_chart_source x

  -- a.source is homeo to a.target which is not compact
  have notcompact : ¬ CompactSpace (a.target) := by
    have : a ∈ ht.atlas := by
      rw [ha]
      exact rfl
    have := ht.is_interval a this
    rcases this with (h|h)
    · rcases h with ⟨ x, y, h ⟩
      rw [←h]
      sorry
    · rcases h with ⟨ x, h ⟩
      rw [←h]
      sorry

  apply notcompact
  refine isCompact_iff_compactSpace.mp ?_
  have : a.target = a.toFun '' a.source := Eq.symm (PartialEquiv.image_source_eq_target a.toPartialEquiv)
  rw [this]
  apply IsCompact.image_of_continuousOn
  · rw [h]
    exact CompactSpace.isCompact_univ
  · exact a.continuousOn_toFun

lemma find_overlap (ht : FinitelyIntervalChartedSpace M) {a : PartialHomeomorph M NNReal} (ha : a ∈ ht.atlas) :
  ∃ (b : PartialHomeomorph M NNReal), (b ∈ ht.atlas \ {a}) ∧ (Overlap a.source b.source) := by sorry

noncomputable def classification' [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) : (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) := by
    have nonempty := nonempty_atlas ht
    let φ := nonempty.some
    by_cases nonempty' : (ht.atlas \ {φ}).Nonempty
    · have : ∃ (ψ : PartialHomeomorph M NNReal), (ψ ∈ ht.atlas \ {φ}) ∧ (Overlap φ.source ψ.source) := find_overlap ht (Set.Nonempty.some_mem nonempty)
      let ψ := this.choose
      let ⟨ hψ, overlap ⟩ := this.choose_spec
      have hφ := ht.is_interval φ (by exact Set.Nonempty.some_mem nonempty)
      by_cases hφIoo : ∃ x y, Set.Ioo x y = φ.target
      · have hψ'' := ht.is_interval ψ (Set.mem_of_mem_diff hψ)
        by_cases hψIoo : ∃ x y, Set.Ioo x y = ψ.target
        · -- the O O case
          let a : OChart M := { φ with target_ioo := hφIoo }
          let b : OChart M := { ψ with target_ioo := hψIoo }
          let result := handle_o_o a b overlap
          rcases result with (result|result)
          · left
            exact result
          · rcases result with ⟨ f, hf ⟩
            let f := f.toIChart
            have ⟨ ht', ht'' ⟩ := replace_charts ht (Set.Nonempty.some_mem nonempty) (Set.mem_of_mem_diff hψ) f hf
            simp only [Set.mem_setOf_eq] at ht''
            exact classification' ht'
        · have hψIio : ∃ x, Set.Iio x = ψ.target := Or.elim hψ'' (fun x => False.elim (hψIoo x)) id
          -- an O H case
          let a : OChart M := { φ with target_ioo := hφIoo }
          let b : HChart M := { ψ with target_iio := hψIio }
          let result := handle_o_h a b overlap

          rcases result with ⟨ f, hf ⟩
          let f := f.toIChart
          have ⟨ ht', ht'' ⟩ := replace_charts ht (Set.Nonempty.some_mem nonempty) (Set.mem_of_mem_diff hψ) f hf
          simp only [Set.mem_setOf_eq] at ht''
          exact classification' ht'

      · have hφIio : ∃ x, Set.Iio x = φ.target := Or.elim hφ (fun x => False.elim (hφIoo x)) id
        have hψ'' := ht.is_interval ψ (Set.mem_of_mem_diff hψ)
        by_cases hψIoo : ∃ x y, Set.Ioo x y = ψ.target
        · -- an H O case
          let a : HChart M := { φ with target_iio := hφIio }
          let b : OChart M := { ψ with target_ioo := hψIoo }
          let result := handle_o_h b a (overlap_symm overlap)

          rcases result with ⟨ f, hf ⟩
          let f := f.toIChart
          have ⟨ ht', ht'' ⟩ := replace_charts ht (Set.Nonempty.some_mem nonempty) (Set.mem_of_mem_diff hψ) f hf
          simp only [Set.mem_setOf_eq] at ht''
          exact classification' ht'

        · have hψIio : ∃ x, Set.Iio x = ψ.target := Or.elim hψ'' (fun x => False.elim (hψIoo x)) id
          -- the H H case
          right
          let a : HChart M := { φ with target_iio := hφIio }
          let b : HChart M := { ψ with target_iio := hψIio }
          exact handle_h_h a b overlap
    · -- A compact manifold must have more than one chart
      exfalso
      apply nonempty'
      push_neg at nonempty'
      have : ht.atlas ⊆ {φ} := Set.diff_eq_empty.mp nonempty'
      have hone : Nat.card ({φ} : Set _) = 1 := by exact Nat.card_unique
      have : Nat.card (ht.atlas) ≤ Nat.card ({φ} : Set _)  := by
        refine Nat.card_mono ?_ this
        exact Set.finite_singleton φ
      have t' := more_than_one_chart ht
      linarith

termination_by Nat.card ht.atlas
decreasing_by · simp at ht''
                rw [ht'']
                simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
                exact (Set.natCard_pos (ht.is_finite)).mpr (nonempty_atlas ht)
              · simp at ht''
                rw [ht'']
                simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
                exact (Set.natCard_pos (ht.is_finite)).mpr (nonempty_atlas ht)
              · simp at ht''
                rw [ht'']
                simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
                exact (Set.natCard_pos (ht.is_finite)).mpr (nonempty_atlas ht)

noncomputable def classification [CompactSpace M] (ht : ChartedSpace NNReal M) : (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) :=
  let ht' := nicely_charted ht
  let ht'' := interval_charted ht'
  classification' (finitely_interval_charted ht'')
