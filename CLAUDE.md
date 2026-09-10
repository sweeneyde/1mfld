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

The historical scratch/quarry files (`OldClassifyOverlaps.lean`, `Gale.lean`,
`Junk.lean`, `more-gale.lean`, `1mfld.lean`, `instances.lean`, `Examples.lean`) were
deleted after the classification was completed; their salvageable content was absorbed
into the files above, and the tracked ones remain in git history.

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

### Phase 1 — the structure lemma (the pivot) — DONE

All sorry-free, on the build path (imported by `ClassifyOverlaps.lean`):

- `OneMfld/Charts.lean` — `OChart`/`HChart`/`IChart`, `Overlap` and its basic lemmas
  (moved out of `ClassifyOverlaps.lean` so toolkit files can use them without an import
  cycle), plus `chart_target_nonempty` and `{O,H,I}Chart.connected_source`.
- `OneMfld/Outer.lean` — the **outer-overlap lemma**:
  - component transport: `OpenPartialHomeomorph.image_connectedComponentIn`,
    `isOpen_connectedComponentIn_chart`, `mem_connectedComponentIn_of_mem_closure`
    (components of open sets inside a chart source are open and relatively closed);
  - `image_component_ne_target`, and the escape theorem
    `not_closure_image_subset_target` (compactness trap + `nonempty_closure_inter_diff`);
  - endpoint analysis `eq_Ioo_of_closure_not_subset_Iio`,
    `eq_end_segment_of_closure_not_subset_Ioo`;
  - headline: `overlap_component_outer_Iio` (H-chart: each overlap component's image is
    `Ioo p v`) and `overlap_component_outer_Ioo` (O-chart: `Ioo p v` or `Ioo u q`).
- `OneMfld/TransitionMono.lean` — `strictMonoOn_or_strictAntiOn_of_injOn_Ioo` (direct
  from mathlib's `ContinuousOn.strictMonoOn_of_injOn_Ioo`; no ℝ-transfer needed),
  `tendsto_top/bot_of_strictMonoOn_image` (monotone maps send ends to ends, via
  `MonotoneOn.tendsto_nhdsWithin_Ioo_left/right` + `csSup_Ioo`/`csInf_Ioo`).
- `OneMfld/Normalize.lean` — `NNReal.mulHomeomorph`, `affineIooOPH` (`Ioo u v ≃ Ioo 0 1`),
  `reflectIooOPH` (`x ↦ 1 - x` on `Ioo 0 1`), and chart-level `HChart.rescale`
  (target ↦ `Iio 1`), `OChart.rescale` (target ↦ `Ioo 0 1`), `OChart.flip` — all
  preserving the source and recording the pointwise formula.

Note: `Gale.lean`'s `overlap_oo_is_outer` is now fully superseded by
`overlap_component_outer_Ioo`.

### Phase 2 — gluing (interval cases) — DONE

All three consumed gluing statements are proved; **the project's only remaining sorry is
`circle_of_disconnected_overlap` in `ClassifyOverlaps.lean` (Phase 3)**.

The construction (uniform across cases): pick a split value `μ ∈ Ioo q 1` in chart `b`'s
overlap image, let `m := b.symm μ`, `ρ := a m`; glue `b` with a rescaled copy of `a` via
mathlib's `OpenPartialHomeomorph.piecewise` along `s := b.source ∩ b⁻¹' (Iic μ)`,
`t := Iic μ` — all frontier conditions come from `IsImage.frontier` + `frontier_Iic`
(no compactness needed). New sorry-free files:

- `OneMfld/GlueCore.lean` — `overlap_connected` (the overlap of a boundary chart is
  connected: two upper end-segments must meet); `overlap_mono`/`overlap_anti`
  (**end-matching**: the transition map's direction is forced — pairing two interior
  ends makes the overlap accumulate at two distinct points, contradicting T2);
  `tendsto_top_of_strictAntiOn_image`.
- `OneMfld/GlueBlocks.lean` — `halfOPH` (`x ↦ x/2 : Iio 1 → [0,½) ⊆ UnitInterval`),
  `mobiusOPH k` (`x ↦ k/(x+k) : ℝ≥0 → (0,1]`, decreasing, no truncated-sub issues),
  `frontier_UIIic`, `reflect_image_Ioo_upper/lower`.
- `OneMfld/GlueNNReal.lean` — `glue_nnreal`: the shared O-H / O-O piecewise assembly
  (result target `(b.target ∩ Iic μ) ∪ Ioo μ (μ/ρ)`).
- `OneMfld/GlueUI.lean` — `glue_hh_ui`: the H-H assembly onto the whole unit interval
  (`b` into `[0, μ/2]` via `halfOPH`, `a` into `(μ/2, 1]` via `mobiusOPH` with
  `k = μρ/(2-μ)`).
- `ClassifyOverlaps.lean` — consumers rewritten: helper corollaries
  (`overlap_image_Iio/Ioo`, `hchart_overlap_connected`, `overlap_image_ne_target`),
  orientation choosers (`OChart.exists_orient_lower/upper`, using `OChart.flip` +
  `reflect_image_*`), and `exists_glue_h_h`/`exists_glue_o_h`/`exists_glue_o_o` as
  Prop-level `∃`-lemmas with the `handle_*` defs extracting via `Exists.choose`
  (**pattern to remember**: `def`s cannot `obtain` from `∃`/`Or` — prove existence as a
  lemma, `choose` once). `handle_h_h'''`, `handle_h_h'`, `Interval3` deleted.

### Phase 3 — the circle — DONE

**THE CLASSIFICATION IS COMPLETE**: `#print axioms classification` yields only
`[propext, Classical.choice, Quot.sound]` — no sorries anywhere in the repo.

The circle case (`circle_of_disconnected_overlap`), sorry-free:

- `OneMfld/TwoComponents.lean` — a disconnected overlap of an interior chart has
  **exactly two components**, one at each end of each chart (`two_components_structure`,
  `two_components_other_chart`); per-component end-matching `overlap_mono_on`/`_on'`
  (the extra hypothesis over GlueCore's versions: the interior endpoint is not in the
  image of the *full* overlap).
- `OneMfld/CircleBlocks.lean` — `mobiusFun c = x/(x + c(1-x))` reparametrization of
  `Ioo 0 1` (shrinks the lower component below any `ε`, preserving end-segment images);
  `affineNNRealOPH` (`Ioo 0 1 ⊆ ℝ≥0 → Ioo d (d+k) ⊆ ℝ`); arc arithmetic in
  `AddCircle 1` (window injectivity, frontier of a closed arc, closed-arc ∪ open-arc
  covers).
- `OneMfld/CircleGlue.lean` — `exists_circle_chart`: normalize + two components +
  orient (`W₀` lower in `a`, upper in `b`) + Möbius-shrink both charts below `1/4`;
  split points `ν, μ > 3/4`; slopes `kα ∈ (max((1-μ+σ)/(ν-ρ), 2/3), 1)` and
  `kg = (1-kα(ν-ρ))/(μ-σ)` (the numeric regime that keeps both arcs shorter than the
  period and the four separation inequalities strict); embed chart `a` as the arc
  `(0, kα)` and chart `b` as the wrapping arc `(g0, g0+kg)` via mathlib's
  `AddCircle.openPartialHomeomorphCoe`; glue with `piecewise` along the closed sub-arc
  `coe '' Icc (kαρ) (kαν)` whose frontier is the two split points; target is all of
  `AddCircle 1`.
- `ClassifyOverlaps.lean` — `circle_of_disconnected_overlap` extracts the chart,
  transfers along `AddCircle.homeomorphCircle` and finishes with
  `toHomeomorphOfCompactTarget` (Circle compact, M connected T2).

### Possible follow-ups

- The converse direction (Circle and UnitInterval *are* `NNReal`-charted spaces, i.e.
  1-manifolds with boundary) — would round out the classification as an iff.
- Extract reusable pieces (e.g. `toHomeomorphOfCompactTarget`, the component-transport
  lemmas in `Outer.lean`, `AddCircle` arc arithmetic) for mathlib contribution.

## Conventions

- Charts are `OpenPartialHomeomorph M NNReal`; the manifold-with-boundary model space is
  `NNReal`, so `Iio x` targets are boundary (H) charts and `Ioo x y` interior (O) charts.
- Props accidentally stated as `def` trigger the `linter.defProp` warning; use `theorem`.
