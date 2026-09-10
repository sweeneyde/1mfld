import OneMfld.Classification

/-!
# Proved solution

This module imports the full proof development and restates the Challenge
theorem with the identical name and type. The library's `classification`
(in `OneMfld/Classification.lean`) produces the homeomorphism as data, as a
term of `(M ≃ₜ Circle) ⊕ (M ≃ₜ UnitInterval)`; here we only need the
Prop-level disjunction. `OneMfld.UnitInterval` is definitionally Mathlib's
`unitInterval` (both unfold to `{x : ℝ | 0 ≤ x ∧ x ≤ 1}`).
-/

theorem OneMfld.homeomorph_circle_or_unitInterval
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [T2Space M] [ChartedSpace NNReal M] :
    Nonempty (M ≃ₜ Circle) ∨ Nonempty (M ≃ₜ unitInterval) := by
  rcases classification (M := M) ‹ChartedSpace NNReal M› with e | e
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩
