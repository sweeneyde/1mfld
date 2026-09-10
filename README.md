# classifying compact connected 1-manifolds

A Lean 4 and [mathlib](https://github.com/leanprover-community/mathlib4) proof of
the classification of compact connected 1-manifolds with boundary:

> **Theorem** (`classification`, in `OneMfld/Classification.lean`).
> Every compact, connected, Hausdorff topological space charted on `ℝ≥0` is
> homeomorphic to the circle or to the closed unit interval.

```lean
noncomputable def classification [TopologicalSpace M] [ConnectedSpace M]
    [T2Space M] [CompactSpace M] (ht : ChartedSpace NNReal M) :
    (M ≃ₜ Circle) ⊕ (M ≃ₜ ↑UnitInterval)
```

`#print axioms classification` reports only `[propext, Classical.choice, Quot.sound]`

There are no `sorry`s in the repository.

## Structure of the proof

Following [Gale's "take-home exam"](https://doi.org/10.2307/2322421) argument:

1. **Normalization** (`NiceCharts`, `ClassifyInterval`, `IntervalCharts`,
   `FiniteIntervalCharts`): every chart can be shrunk so its target is an open interval
   `Ioo x y` (interior chart) or `Iio x` (boundary chart) in `ℝ≥0`, and compactness
   yields a finite atlas of such charts.
2. **Induction on atlas size** (`Classification`): repeatedly merge two overlapping
   charts into one, or recognize the terminal cases.
3. **The outer-overlap lemma** (`Outer`): the image of any component of the overlap of
   two interval charts is an end-segment of the chart target — otherwise its closure
   would be trapped in the chart by a compactness argument, contradicting that it must
   escape into the other chart (`ClosureOverlap`).
4. **End-matching** (`GlueCore`, `TwoComponents`): the transition map on a component is
   strictly monotone in the direction forced by which interval-ends are interior; the
   wrong direction would give the overlap two distinct limit points at once,
   contradicting Hausdorffness.
5. **Gluing** (`GlueNNReal`, `GlueUI`, `ClassifyOverlaps`): two charts with connected
   overlap merge via `OpenPartialHomeomorph.piecewise`; two boundary charts glue onto
   the closed unit interval, exhibiting `M ≃ₜ [0,1]`.
6. **The circle** (`TwoComponents`, `CircleBlocks`, `CircleGlue`): a disconnected
   overlap has exactly two components, one at each end of each chart; the two charts
   then embed as overlapping arcs of `AddCircle 1` and glue to a chart of `M` onto the
   whole circle, exhibiting `M ≃ₜ Circle`.

## Building

With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get   # fetch mathlib build cache
lake build
```

The toolchain (`lean-toolchain`) and mathlib version (`lake-manifest.json`) are pinned.
