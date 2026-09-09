# 1mflds — Classification of compact 1-manifolds in Lean 4

Goal: `classification` (in `OneMfld/Classification.lean`): a compact connected Hausdorff
space charted on `NNReal` is homeomorphic to `Circle` or to the unit interval.
The statement already typechecks end-to-end; the proof follows Gale's "take-home exam"
argument (induct on the size of a finite atlas of interval charts, merging overlapping
charts until two half-open charts glue to the interval, or two open charts close up
into the circle).

## Build

- Toolchain `leanprover/lean4:v4.33.1`, mathlib pinned in `lakefile.lean`. `lake build` succeeds.
- The **only** remaining `sorry`s on the build path are in `OneMfld/ClassifyOverlaps.lean`.

## File map (build path, all sorry-free unless noted)

- `OneMfld/LocallyConnected.lean` — `LocallyConnectedSpace` instances for `ℝ`, `NNReal`.
- `OneMfld/ClassifyInterval.lean` — classification of open connected subsets of `ℝ` and
  `NNReal` (`classify_connected_nnreal_interval`); the `relu` toolkit for `ℝ ⇄ NNReal`
  transfer (`relu_mono`, `relu_ioo`, `proj_relu`, …); `StrictMonoOn.injOn_Ioo`.
- `OneMfld/NiceCharts.lean` — shrink charts to bounded, connected targets
  (`nicely_charted`).
- `OneMfld/IntervalCharts.lean` — `IntervalChartedSpace`: every chart target is
  `Ioo x y` or `Iio x` (`interval_charted`).
- `OneMfld/FinitelyCharted.lean`, `OneMfld/FiniteIntervalCharts.lean` — finite subatlas
  for compact `M` (`FinitelyIntervalChartedSpace`).
- `OneMfld/Noncompact.lean`, `OneMfld/Compactness.lean` — `noncompact_target`: no single
  interval chart covers a compact `M`.
- `OneMfld/UnitInterval.lean` — `UnitInterval : Set ℝ` (defeq to `Set.Icc 0 1`, but NOT
  syntactically mathlib's `unitInterval`; add a `rfl` bridge before using mathlib's
  `Icc`/`unitInterval` API such as `iccHomeoI`).
- `OneMfld/ClassifyOverlaps.lean` — **the work front** (see below). Defines
  `OChart` (target `Ioo x y`), `HChart` (target `Iio x`), `IChart`, `Overlap`
  (nonempty intersection, neither contains the other), and the fully proved
  `Homeomorph.toOpenPartialHomeomorphOnOpens`.
- `OneMfld/Classification.lean` — the induction: `subsume_charts`, `replace_charts`
  (needs only `f : IChart M` with `f.source = a.source ∪ b.source`), `find_overlap`,
  `more_than_one_chart`, `classification'` (with termination proof), `classification`.

Sorry-free but **not yet imported** anywhere (wire these in — see Phase 0):

- `OneMfld/ClosureOverlap.lean` — `nonempty_closure_inter_diff`: an overlap component's
  closure escapes into the other chart. Engine of the "outer" lemma.
- `OneMfld/RealIntervals.lean` — `BoundedInterval` with `closure_/interior_/frontier_BoundedInterval`,
  `other_endpoint`, `classify_connected_reals`.
- `OneMfld/PartialHomeomorphHelpers.lean` — chart source connected ↔ target connected.

Scratch / quarry files (NOT on build path; do not fix, only mine):

- `OneMfld/OldClassifyOverlaps.lean` — broken scratchpad, but contains: a **complete**
  proof of `handle_h_h` from `handle_h_h'` (lines ~827–859: glued chart onto `[0,1]` ⟹
  union compact ⟹ clopen ⟹ `= univ` by connectedness); a proved `IsImage`/frontier
  block for split-point sets (lines ~648–678); a nearly complete `surj_on` for the
  normalized H-H piecewise map.
- `Gale.lean` — `IsOuter` and `overlap_oo_is_outer`, ~80% proved (closure-escape step
  done via `nonempty_closure_inter_diff`; final step missing).
- `Junk.lean`, `more-gale.lean`, `1mfld.lean`, `OneMfld/instances.lean`,
  `OneMfld/Examples.lean` — superseded, nothing salvageable.

## Remaining work: the plan

`Classification.lean` consumes exactly **three** sorries from `ClassifyOverlaps.lean`:
`handle_o_h`, `handle_o_o`, `handle_h_h`. The others (`handle_h_h'''`, `handle_h_h'`,
`handle_o_h'`) are internal stepping stones and may be restated or deleted
(recommendation: drop `handle_h_h'''`/`Interval3` entirely).

### Phase 0 — free progress (mechanical) — DONE

1. ✅ `ClosureOverlap`, `RealIntervals`, `PartialHomeomorphHelpers` are imported by
   `ClassifyOverlaps.lean` (and `PartialHomeomorphHelpers` by `NiceCharts.lean`); all
   compile on v4.33.1.
2. ✅ `handle_h_h` is fully proved, via two new pieces in `ClassifyOverlaps.lean`:
   `OpenPartialHomeomorph.toHomeomorphOfCompactTarget` (generic: partial homeo from a
   preconnected T2 space onto all of a compact space, nonempty source ⟹ global
   homeomorphism — reusable for the circle case in Phase 3) and `glue_h_h` (sorried:
   produce the glued chart `M ⇀ UnitInterval` with source `a.source ∪ b.source`,
   target `univ`; to be proved from `handle_h_h'` + Phase 1 normalization).
3. ✅ `UnitInterval_eq_Icc : UnitInterval = Set.Icc 0 1 := rfl`, `isCompact_UnitInterval`,
   `Nonempty`/`CompactSpace UnitInterval` instances in `UnitInterval.lean`;
   `restrOpen_symm_image_target` extracted into `PartialHomeomorphHelpers.lean` and used
   at the three `NiceCharts.lean` sites.

Remaining sorries in `ClassifyOverlaps.lean`: `handle_h_h'''`, `handle_h_h'`, `glue_h_h`,
`handle_o_o`, `handle_o_h`, `handle_o_h'` — of which `Classification.lean` needs only
`handle_o_o`, `handle_o_h`, and (via `handle_h_h`) `glue_h_h`.

### Phase 1 — the structure lemma (the pivot)

Prove in current vocabulary (`OpenPartialHomeomorph M NNReal`, `Overlap`):

> **Outer-overlap lemma.** For interval charts `a`, `b` with `Overlap a.source b.source`,
> each connected component `W` of the overlap has `a '' W` an *outer* subinterval of
> `a.target` (closure contains the appropriate open endpoint), and likewise in `b`.

Sources: finish `Gale.lean`'s `overlap_oo_is_outer` using `nonempty_closure_inter_diff`
+ `RealIntervals.frontier_BoundedInterval`. Alongside:

- **Monotonicity wrapper**: transition maps are strictly monotone or antitone per
  component — mathlib's `ContinuousOn.strictMonoOn_of_injOn_Ioo`
  (`Mathlib/Topology/Order/IntermediateValue.lean`), transported `NNReal ↔ ℝ` via the
  `relu` toolkit; plus orientation flip `x ↦ c - x`.
- **Normalization toolkit**: affine rescaling/reflection of chart targets via
  `OpenPartialHomeomorph.transHomeomorph`, so overlap images sit at standard positions.

### Phase 2 — gluing (interval cases)

Use mathlib's `OpenPartialHomeomorph.piecewise`
(`Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean`) — do NOT finish the
hand-rolled piecewise proofs in the old file. It takes exactly the `IsImage`/frontier
data the salvaged block produces. Order:

1. `handle_o_h` (overlap is connected here; prove that from the outer lemma).
2. `handle_h_h'` — glue, rescale to `[0,1]` with `iccHomeoI`, package via
   `Homeomorph.toOpenPartialHomeomorphOnOpens`; `handle_h_h` then closes via Phase 0.2.
3. `handle_o_o`, one-component branch — same gluing, yields the `OChart`.

The **split point** (never constructed in any draft) falls out of the outer lemma +
`frontier_BoundedInterval`.

### Phase 3 — the circle (hardest, do last)

Two-component branch of `handle_o_o`:

- `at_most_two_components`: overlap of two O-charts has ≤ 2 components (each chart end
  supports at most one outer component). Only exists as a comment at `Gale.lean:128`.
- Two components ⟹ `M ≃ₜ Circle`: map the two glued arcs onto overlapping arcs of
  `Circle` (via `Circle.exp` on intervals) and reuse the piecewise + compact-clopen
  pattern from `handle_h_h`. (Mathlib alternatives: `AddCircle.homeomorphCircle`.)

## Conventions

- Charts are `OpenPartialHomeomorph M NNReal`; the manifold-with-boundary model space is
  `NNReal`, so `Iio x` targets are boundary (H) charts and `Ioo x y` interior (O) charts.
- Props accidentally stated as `def` trigger the `linter.defProp` warning; use `theorem`.
