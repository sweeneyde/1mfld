import Mathlib
import OneMfld.UnitInterval
import OneMfld.FiniteIntervalCharts
import OneMfld.IntervalCharts
import OneMfld.NiceCharts
import OneMfld.ClosureOverlap
import OneMfld.RealIntervals
import OneMfld.PartialHomeomorphHelpers

structure OChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
  target_ioo : (∃ x y, (Set.Ioo x y = target))

structure HChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
  target_iio : (∃ x, (Set.Iio x = target))

structure IChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
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
  : (U \ V).Nonempty := Set.sdiff_nonempty.mpr hu

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

open Classical in
/-- Turn a homeomorphism of open subtypes `A ≃ₜ B` into a partial homeomorphism `X ⇀ Y`.

The `Nonempty` hypotheses are needed, and are not an artefact of the proof: a
`PartialEquiv X Y` carries a *total* `toFun : X → Y`, so `OpenPartialHomeomorph Unit Empty`
is an empty type even though `(∅ : Set Unit) ≃ₜ (∅ : Set Empty)` with both sets open. -/
noncomputable def Homeomorph.toOpenPartialHomeomorphOnOpens
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [Nonempty Y]
    {A : Set X} {B : Set Y} (h : A ≃ₜ B) (hA : IsOpen A) (hB : IsOpen B) :
    OpenPartialHomeomorph X Y where
  toFun x := if hx : x ∈ A then (h ⟨x, hx⟩ : Y) else Classical.arbitrary Y
  invFun y := if hy : y ∈ B then (h.symm ⟨y, hy⟩ : X) else Classical.arbitrary X
  source := A
  target := B
  map_source' x hx := by simp only [dif_pos hx]; exact (h ⟨x, hx⟩).2
  map_target' y hy := by simp only [dif_pos hy]; exact (h.symm ⟨y, hy⟩).2
  left_inv' x hx := by
    simp only [dif_pos hx, dif_pos (h ⟨x, hx⟩).2]
    have : (⟨(h ⟨x, hx⟩ : Y), (h ⟨x, hx⟩).2⟩ : B) = h ⟨x, hx⟩ := rfl
    rw [this, Homeomorph.symm_apply_apply]
  right_inv' y hy := by
    simp only [dif_pos hy, dif_pos (h.symm ⟨y, hy⟩).2]
    have : (⟨(h.symm ⟨y, hy⟩ : X), (h.symm ⟨y, hy⟩).2⟩ : A) = h.symm ⟨y, hy⟩ := rfl
    rw [this, Homeomorph.apply_symm_apply]
  open_source := hA
  open_target := hB
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (A.domRestrict fun x => if hx : x ∈ A then (h ⟨x, hx⟩ : Y) else Classical.arbitrary Y)
        = fun x : A => ((h x : B) : Y) := by
      funext x; simp only [Set.domRestrict_apply, dif_pos x.2]
    rw [this]
    exact continuous_subtype_val.comp h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (B.domRestrict fun y => if hy : y ∈ B then (h.symm ⟨y, hy⟩ : X) else Classical.arbitrary X)
        = fun y : B => ((h.symm y : A) : X) := by
      funext y; simp only [Set.domRestrict_apply, dif_pos y.2]
    rw [this]
    exact continuous_subtype_val.comp h.symm.continuous

/-- An `OpenPartialHomeomorph` from a preconnected Hausdorff space onto the whole of a
compact space, with nonempty source, is a global homeomorphism: its source is compact
(hence closed) as well as open, so it is clopen and equals `univ`. -/
noncomputable def OpenPartialHomeomorph.toHomeomorphOfCompactTarget
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [T2Space X] [CompactSpace Y]
    (φ : OpenPartialHomeomorph X Y)
    (hne : φ.source.Nonempty)
    (ht : φ.target = Set.univ) :
    Homeomorph X Y := by
  have ho : IsOpen φ.source := φ.open_source
  have hc : IsClosed φ.source := by
    have cpct' : CompactSpace φ.target := by
      rw [ht]
      exact (Homeomorph.Set.univ Y).symm.compactSpace
    have h : Homeomorph φ.target φ.source := φ.toHomeomorphSourceTarget.symm
    have hcs : CompactSpace φ.source := h.compactSpace
    have cpct : IsCompact φ.source := isCompact_iff_isCompact_univ.mpr CompactSpace.isCompact_univ
    exact cpct.isClosed
  have hs : φ.source = Set.univ := by
    have hco : IsClopen φ.source := ⟨hc, ho⟩
    have he' := isPreconnected_univ.subset_isClopen hco (by simpa using hne)
    exact Set.eq_univ_of_univ_subset he'
  exact φ.toHomeomorphOfSourceEqUnivTargetEqUniv hs ht

def Interval3 := (Set.Icc (0 : Real) (3 : Real))

def handle_h_h''' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 2)
  (hb_target : b.target = Set.Iio 2)
  (ha : a.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2)
  (hb : b.toFun '' (a.source ∩ b.source) = Set.Ioo 1 2) :
  { φ : OpenPartialHomeomorph Interval3 M | φ.target = a.source ∪ b.source ∧ φ.source = Set.univ } := by sorry

def handle_h_h' (a : HChart M) (b : HChart M) (h : Overlap a.source b.source)
  (ha_target : a.target = Set.Iio 1)
  (ha : ∃ (x : NNReal), a.toFun '' (a.source ∩ b.source) = Set.Ioo x 1)
  (hb : ∃ (y : NNReal), b.toFun '' (a.source ∩ b.source) = Set.Ioo y 1) :
  { φ : OpenPartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by sorry

/-- Glue two overlapping H-charts into a single chart of `M` onto the unit interval.
This will follow from `handle_h_h'` once the normalization toolkit (Phase 1) can put
`a` and `b` into standard position. -/
def glue_h_h (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { φ : OpenPartialHomeomorph M UnitInterval | φ.source = a.source ∪ b.source ∧ φ.target = Set.univ } := by
  sorry

noncomputable def handle_h_h (a : HChart M) (b : HChart M) (h : Overlap a.source b.source) :
  Homeomorph M UnitInterval := by
  obtain ⟨φ, hφ, hs⟩ := glue_h_h a b h
  have hne : φ.source.Nonempty := by
    rw [hφ]
    exact Set.Nonempty.inl (h.1.mono Set.inter_subset_left)
  exact φ.toHomeomorphOfCompactTarget hne hs

def handle_o_o (a : OChart M) (b : OChart M) (h : Overlap a.source b.source) :
  (Homeomorph M Circle) ⊕ { f : OChart M | f.source = a.source ∪ b.source } := by
  sorry

def handle_o_h (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) :
  { f : HChart M | f.source = a.source ∪ b.source } := by
  sorry

def handle_o_h' (a : OChart M) (b : HChart M) (h : Overlap a.source b.source) (hc : IsConnected (a.source ∩ b.source)):
  { f : HChart M | f.source = a.source ∪ b.source } := by sorry
