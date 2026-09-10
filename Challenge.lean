import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The classification of compact connected 1-manifolds

This is the trusted statement file (the Palomar "Challenge" module). It states
the advertised theorem using only Mathlib vocabulary; the proof lives in the
`OneMfld` library and is connected to this statement in `Solution.lean`.

Here a topological 1-manifold, possibly with boundary, is a space `M` with a
`ChartedSpace NNReal M` instance: an atlas of partial homeomorphisms from `M`
to the half-line `ℝ≥0 = [0, ∞)` whose sources cover `M`. Charts into the
half-line make boundary points (those sent to `0`) possible, so this includes
manifolds with boundary; a chart target avoiding `0` is an ordinary interior
chart. Mathlib's `ChartedSpace` carries no separation axiom of its own, so
Hausdorffness is assumed separately; no countability hypothesis is needed
because `M` is assumed compact. Connectedness (`ConnectedSpace`) includes
nonemptiness.

`Circle` is Mathlib's unit circle in `ℂ`, and `{x : ℝ // 0 ≤ x ∧ x ≤ 1}`
is the closed unit interval `[0, 1]` as a subspace of `ℝ` (the subtype
spelling of Mathlib's `unitInterval`, written out so the statement is
self-contained).
-/

/-- **The classification of compact connected 1-manifolds (with boundary).**
Every compact, connected, Hausdorff topological space charted on the
half-line `ℝ≥0` is homeomorphic to the circle or to the closed unit
interval `[0, 1]`. -/
theorem OneMfld.homeomorph_circle_or_unitInterval
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [T2Space M] [ChartedSpace NNReal M] :
    Nonempty (M ≃ₜ Circle) ∨ Nonempty (M ≃ₜ {x : ℝ // 0 ≤ x ∧ x ≤ 1}) := by
  sorry
