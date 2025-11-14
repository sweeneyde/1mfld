import Mathlib

lemma partial_homeo_connected {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) (conn : IsConnected h.source) : (IsConnected h.target) := by
  have ht : h.target = h.toFun '' h.source
  exact Eq.symm (PartialEquiv.image_source_eq_target h.toPartialEquiv)
  rw [ht]
  apply IsConnected.image conn ↑h.toPartialEquiv h.continuousOn_toFun

lemma partial_homeo_connected' {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) (conn : IsConnected h.target) : (IsConnected h.source) := by
  have hst : h.symm.source = h.target := rfl
  have hts : h.symm.target = h.source := rfl
  have conn' : IsConnected h.symm.source := by
    rw [hst]
    exact conn
  have h'' := partial_homeo_connected h.symm conn'
  rw [←hts]
  exact h''

lemma partial_homeo_source_connected_iff_target_connected {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) : IsConnected h.source ↔ IsConnected h.target := by
  constructor
  · exact fun a => partial_homeo_connected h a
  · exact fun a => partial_homeo_connected' h a
