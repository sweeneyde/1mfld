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

noncomputable def subsume_charts (ht : FinitelyIntervalChartedSpace M)
  {a : PartialHomeomorph M NNReal} (ha : a ∈ ht.atlas)
  {b : PartialHomeomorph M NNReal} (hb : b ∈ ht.atlas)
  (hs : a.source ⊆ b.source) (hab : a ≠ b):
  { ht' : FinitelyIntervalChartedSpace M | Nat.card ht'.atlas = Nat.card ht.atlas - 1 } := by
    let ht' : FinitelyIntervalChartedSpace M :=
    { chartAt := by
        intro x
        by_cases h : a = ht.chartAt x
        · exact b
        · exact ht.chartAt x
    , atlas := ht.atlas \ { a }
    , chart_mem_atlas := by
        intro x
        split_ifs with h
        · apply Set.mem_diff_singleton.mpr
          apply And.intro
          · exact hb
          · exact id (Ne.symm hab)
        · apply Set.mem_diff_singleton.mpr
          apply And.intro
          · exact ChartedSpace.chart_mem_atlas x
          · exact fun a_1 => h (id (Eq.symm a_1))
    , mem_chart_source := by
        intro x
        split_ifs with h
        · rw [h] at hs
          apply hs
          exact ChartedSpace.mem_chart_source x
        · exact ChartedSpace.mem_chart_source x
    , is_finite := Set.Finite.subset ht.is_finite Set.diff_subset
    , is_interval := by
        intro φ
        intro hφ
        apply ht.is_interval
        exact Set.mem_of_mem_diff hφ
    }

    use ht'
    exact Set.ncard_diff_singleton_of_mem ha (ht.is_finite)


noncomputable def replace_charts (ht : FinitelyIntervalChartedSpace M)
  {a : PartialHomeomorph M NNReal} (ha : a ∈ ht.atlas)
  {b : PartialHomeomorph M NNReal} (hb : b ∈ ht.atlas)
  (ho : Overlap a.source b.source)
  (f : IChart M) (hf : f.source = a.source ∪ b.source ) :
  { ht' : FinitelyIntervalChartedSpace M | Nat.card ht'.atlas = Nat.card ht.atlas - 1 } := by

    let hab : a ≠ b := by
      by_contra hab
      rw [hab] at ho
      let ho1 := ho.2.1
      simp only [sdiff_self, Set.bot_eq_empty, Set.not_nonempty_empty] at ho1

    let ht' : FinitelyIntervalChartedSpace M :=
    { chartAt := by
        intro x
        by_cases h : a = ht.chartAt x
        · exact f.toPartialHomeomorph
        · by_cases h : b = ht.chartAt x
          · exact f.toPartialHomeomorph
          · exact ht.chartAt x
    , atlas := (ht.atlas \ { a, b }) ∪ ({ f.toPartialHomeomorph } : Set _)
    , chart_mem_atlas := by
        intro x
        split_ifs with h h'
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff,
          not_or, true_or]
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff,
          not_or, true_or]
        · simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_diff, chart_mem_atlas,
          Set.mem_singleton_iff, not_or, true_and]
          right
          exact ⟨fun a_1 => h (id (Eq.symm a_1)), fun a => h' (id (Eq.symm a))⟩
    , mem_chart_source := by
        intro x
        split_ifs with h h'
        · rw [hf]
          simp only [Set.mem_union]
          left
          rw [h]
          exact ChartedSpace.mem_chart_source x
        · rw [hf]
          simp only [Set.mem_union]
          right
          rw [h']
          exact ChartedSpace.mem_chart_source x
        · exact ChartedSpace.mem_chart_source x
    , is_finite := by
        have : Finite ht.atlas := ht.is_finite
        simp only [Set.union_singleton]
        exact Finite.Set.finite_insert f.toPartialHomeomorph (ChartedSpace.atlas \ {a, b})
    , is_interval := by
        intro x
        intro hx
        simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff,
          not_or] at hx

        rcases hx with (hx|hx)
        · apply ht.is_interval
          rw [hx]
          have : f.toPartialHomeomorph ∈ (ht.atlas \ { a, b }) ∪ ({ f.toPartialHomeomorph } : Set _) := by sorry
          sorry
        · apply ht.is_interval
          exact hx.1
    }

    use ht'

    sorry
      --exact Set.ncard_diff_singleton_of_mem ha (ht.is_finite)

lemma nonempty_atlas (ht : FinitelyIntervalChartedSpace M) : ht.atlas.Nonempty := by
  by_contra nonempty
  have he : Nonempty M := ConnectedSpace.toNonempty
  have x := he.some
  let chart := ht.chartAt x
  have hc : chart ∈ ht.atlas := ht.chart_mem_atlas x
  exfalso
  exact nonempty (Set.nonempty_of_mem hc)

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

lemma more_than_one_chart [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) : Nat.card ht.atlas > 1 := by
  have z := (ConnectedSpace.toNonempty : Nonempty M).some
  let φ := ht.chartAt z

  have nonempty := nonempty_atlas ht

  have hzero : Nat.card ht.atlas > 0 := by
    refine (Set.natCard_pos ?_).mpr nonempty
    exact ht.is_finite
  by_contra htwo
  have hone : Nat.card ht.atlas = 1 := by linarith

  have he : ∃ (a : PartialHomeomorph M NNReal), ht.atlas = { a } := Set.ncard_eq_one.mp hone
  rcases he with ⟨a,ha⟩

  have : φ ∈ ht.atlas := ChartedSpace.chart_mem_atlas z
  rw [ha] at this
  have hφa : φ = a := by exact this

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
  have notcompactφ : ¬ CompactSpace (φ.target) := by
    apply noncompact_target
    exact ChartedSpace.chart_mem_atlas z
    exact ChartedSpace.mem_chart_source z
  have notcompact : ¬ CompactSpace (a.target) := by
    rwa [←hφa]

  exfalso
  apply notcompact
  refine isCompact_iff_compactSpace.mp ?_
  have : a.target = a.toFun '' a.source := Eq.symm (PartialEquiv.image_source_eq_target a.toPartialEquiv)
  rw [this]
  apply IsCompact.image_of_continuousOn
  · rw [h]
    exact CompactSpace.isCompact_univ
  · exact a.continuousOn_toFun

lemma find_overlap [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) {a : PartialHomeomorph M NNReal}
  (ha : a ∈ ht.atlas) {x : M} (hx : x ∈ a.source)
  (contains : ∀ c ∈ ChartedSpace.atlas \ {a}, ¬ a.source ⊆ c.source) :
  ∃ (b : PartialHomeomorph M NNReal), (b ∈ ht.atlas \ {a}) ∧ (Overlap a.source b.source) := by
    by_contra h
    push_neg at h

    have ho : IsOpen a.source := a.open_source
    have hc : IsClosed a.source := by
      have comp : a.sourceᶜ = ⋃ (b ∈ { c ∈ ChartedSpace.atlas \ {a} | ¬ (c.source ⊆ a.source) }), b.source := by
        ext z
        apply Iff.intro
        · intro hz
          simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_iUnion,
            exists_prop]
          use ChartedSpace.chartAt z
          simp only [chart_mem_atlas, true_and, mem_chart_source, and_true]
          by_contra hza
          push_neg at hza

          apply hz
          apply hza
          by_contra hc
          rw [←hc] at hz
          simp only [Set.mem_compl_iff, mem_chart_source, not_true_eq_false] at hz
          exact ChartedSpace.mem_chart_source z
        · intro hz
          simp only [Set.mem_compl_iff]
          by_contra hza
          simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop] at hz
          rcases hz with ⟨ i, ⟨ ⟨ hia, hia' ⟩, his ⟩, hzi ⟩
          specialize h i

          have hic : i ∈ ChartedSpace.atlas \ {a} := Set.mem_diff_of_mem hia hia'
          specialize h hic

          apply h
          apply does_overlap
          · use z
            simp only [Set.mem_inter_iff]
            tauto
          · exact contains i hic
          · exact his

      refine { isOpen_compl := ?_ }
      rw [comp]
      apply isOpen_biUnion
      exact fun i a => i.open_source

    have hco : IsClopen a.source := ⟨hc, ho⟩
    have he : IsPreconnected (Set.univ : Set M) := isPreconnected_univ

    have he' := he.subset_isClopen hco

    have hn : (Set.univ ∩ a.source).Nonempty := by
      apply Set.inter_nonempty.mpr
      use x
      exact (Set.mem_ite_empty_right (x ∈ Set.univ) a.source x).mp hx
    have h' := he' hn

    have hs : a.source ⊆ Set.univ := by exact fun ⦃a_1⦄ a => trivial

    have he : a.source = Set.univ := Set.eq_univ_of_univ_subset (he' hn)

    have hcpct : ¬ CompactSpace a.target := by
      apply noncompact_target
      exact ha
      exact hx

    apply hcpct

    refine isCompact_iff_compactSpace.mp ?_
    have : a.target = a.toFun '' a.source := Eq.symm (PartialEquiv.image_source_eq_target a.toPartialEquiv)
    rw [this]
    rw [he]

    have hcpctM : IsCompact (Set.univ : Set M) := CompactSpace.isCompact_univ
    refine IsCompact.image_of_continuousOn hcpctM ?_
    rw [←he]
    exact a.continuousOn_toFun

noncomputable def classification' [CompactSpace M] (ht : FinitelyIntervalChartedSpace M) : (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) := by
    -- instead, use the fact that M is nonempty and then use chartat
    have x := (ConnectedSpace.toNonempty : Nonempty M).some
    let φ := ht.chartAt x

    have nonempty := nonempty_atlas ht
    --let φ := nonempty.some
    by_cases nonempty' : (ht.atlas \ {φ}).Nonempty
    · by_cases contains : ∃ (ψ : PartialHomeomorph M NNReal), (ψ ∈ ht.atlas \ {φ}) ∧ (φ.source ⊆ ψ.source)
      · let ψ := contains.choose
        let hψ := contains.choose_spec
        have hψ' : ψ ∈ ht.atlas := by
          have : ht.atlas \ { φ } ⊆ ht.atlas := Set.diff_subset
          apply this
          exact hψ.1
        have : φ.source ⊆ ψ.source := hψ.2
        have hd : φ ≠ ψ := by
          have : ψ ∈ ChartedSpace.atlas \ {φ} := hψ.1
          by_contra hd
          rw [←hd] at this
          have this' : φ ∉ ChartedSpace.atlas \ {φ} := by exact Set.not_mem_diff_of_mem rfl
          exact this' this
        have ⟨ ht', ht'' ⟩ := subsume_charts ht (ChartedSpace.chart_mem_atlas x) hψ' this hd
        exact classification' ht'
      · have : ∃ (ψ : PartialHomeomorph M NNReal), (ψ ∈ ht.atlas \ {φ}) ∧ (Overlap φ.source ψ.source) := by
          simp only [Set.mem_singleton_iff, not_exists, not_and, and_imp] at contains
          exact find_overlap ht (ChartedSpace.chart_mem_atlas x) (ChartedSpace.mem_chart_source x) contains
        let ψ := this.choose
        let ⟨ hψ, overlap ⟩ := this.choose_spec
        have hφ := ht.is_interval φ (ChartedSpace.chart_mem_atlas x)
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
              have ⟨ ht', ht'' ⟩ := replace_charts ht (ChartedSpace.chart_mem_atlas x) (Set.mem_of_mem_diff hψ) overlap f hf
              simp only [Set.mem_setOf_eq] at ht''
              exact classification' ht'
          · have hψIio : ∃ x, Set.Iio x = ψ.target := Or.elim hψ'' (fun x => False.elim (hψIoo x)) id
            -- an O H case
            let a : OChart M := { φ with target_ioo := hφIoo }
            let b : HChart M := { ψ with target_iio := hψIio }
            let result := handle_o_h a b overlap

            rcases result with ⟨ f, hf ⟩
            let f := f.toIChart
            have ⟨ ht', ht'' ⟩ := replace_charts ht (ChartedSpace.chart_mem_atlas x) (Set.mem_of_mem_diff hψ) overlap f hf
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
            have ⟨ ht', ht'' ⟩ := replace_charts ht (Set.mem_of_mem_diff hψ) (ChartedSpace.chart_mem_atlas x) (overlap_symm overlap) f hf
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
              · simp at ht''
                rw [ht'']
                simp only [tsub_lt_self_iff, zero_lt_one, and_true, gt_iff_lt]
                exact (Set.natCard_pos (ht.is_finite)).mpr (nonempty_atlas ht)

noncomputable def classification [CompactSpace M] (ht : ChartedSpace NNReal M) : (Homeomorph M Circle) ⊕ (Homeomorph M UnitInterval) :=
  let ht' := nicely_charted ht
  let ht'' := interval_charted ht'
  classification' (finitely_interval_charted ht'')
