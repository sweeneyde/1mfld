import Mathlib

import ClosureOverlap


lemma continuity {α : Type u} {β : Type u} [TopologicalSpace α] [TopologicalSpace β]
  (f : α → β) (U : Set α) (V : Set α) (h : V ⊆ U) (hc : ContinuousOn f U) :
  (ContinuousOn f V) := by
    exact ContinuousOn.mono hc h

lemma map_source_image {α : Type u} {β : Type u} [TopologicalSpace α] [TopologicalSpace β]
  (U : PartialHomeomorph α β) (V : Set α) (hV : V ⊆ U.source)
  : (U.toFun' '' V ⊆ U.target) := by
  rintro x hx
  simp at hx
  rcases hx with ⟨y , hyv, huy ⟩
  rw [← huy]
  exact PartialHomeomorph.map_source U (hV hyv)


structure OChart (X : Type*) [TopologicalSpace X]
  extends PartialHomeomorph X NNReal where
  target_ioo : target = Set.Ioo 0 1

structure HChart (X : Type*) [TopologicalSpace X]
  extends PartialHomeomorph X NNReal where
  target_ioo : target = Set.Ico 0 1

#check PartialHomeomorph

universe u
variable {α : Type u}
variable [TopologicalSpace α]

-- TODO: prove this
variable [LocallyConnectedSpace α]

def Overlap (U : Set α) (V : Set α) : Prop :=
  (U ∩ V).Nonempty ∧ (U \ V).Nonempty ∧ (V \ U).Nonempty

def IsUpper (S : Set NNReal) : Prop := ∃ x, S = Set.Ioo x 1
def IsLower (S : Set NNReal) : Prop := ∃ x, S = Set.Ioo 0 x
def IsOuter (S : Set NNReal) : Prop := (IsUpper S) ∨ (IsLower S)

lemma overlap_oo_is_outer {U : OChart α} {V : OChart α} (h : Overlap U.source V.source)
  (x : α) (hx : x ∈ U.source ∩ V.source) :
  IsOuter ((U.toFun') '' (connectedComponentIn (U.source ∩ V.source) x)) := by
      let phi := U.toFun'
      let W := connectedComponentIn (U.source ∩ V.source) x
      let phiW := phi '' W

      have hu : IsOpen U.source := U.open_source
      have hv : IsOpen V.source := V.open_source
      have huv := IsOpen.inter hu hv

      have ho : IsOpen phiW := by
        apply PartialHomeomorph.isOpen_image_of_subset_source
        exact IsOpen.connectedComponentIn huv
        have hwuv : W ⊆ U.source ∩ V.source := connectedComponentIn_subset (U.source ∩ V.source) x
        have huvu : (U.source ∩ V.source) ⊆ U.source := Set.inter_subset_left
        exact fun ⦃a⦄ a_1 => huvu (hwuv a_1)

      have huc : IsConnected U.source := sorry

      have hm : W ⊆ U.source := by sorry

      have hw : IsConnected W
      exact isConnected_connectedComponentIn_iff.mpr hx
      have hw' : IsConnected phiW
      apply IsConnected.image hw ↑U.toPartialHomeomorph
      have hco : ContinuousOn (↑U.toPartialHomeomorph) U.source
      exact PartialHomeomorph.continuousOn U.toPartialHomeomorph
      exact ContinuousOn.mono hco hm

      have hpt : phiW ⊆ Set.Ioo 0 1
      have hpt' : phiW ⊆ U.target := by
        rintro x hx
        rcases hx with ⟨y , hyv, huy ⟩
        rw [←huy]
        exact PartialHomeomorph.map_source U.toPartialHomeomorph (hm hyv)


--

lemma overlap_ho_is_outer {U : OChart α} {V : HChart α} (h : Overlap U.source V.source)
                          (x : α) (hx : x ∈ U.source ∩ V.source) :
                          IsOuter ((U.toFun) '' (connectedComponent x)) := sorry

lemma overlap_hh_is_outer {U : HChart α} {V : HChart α} (h : Overlap U.source V.source)
                          (x : α) (hx : x ∈ U.source ∩ V.source) :
                          IsOuter ((U.toFun) '' (connectedComponent x)) := sorry

--lemma at_most_two_components {U : HChart α} {V : HChart α} :
--                             (ConnectedComponents (U.source ∩ V.source)).encard ≤ 2 := sorry



open Function
open Set

def ici_cap_iio_empty (y : Real) : (Ici y ∩ Iio y) = ∅ := by
    have h' : Ici y ∩ Iio y = Ico y y := rfl
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ico_eq_empty]

def iic_cap_ioi_empty (y : Real) : (Iic y ∩ Ioi y) = ∅ := by
    have h' : Iic y ∩ Ioi y = Ioc y y := Iic_inter_Ioi
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ioc_eq_empty]

def not_ici (U : Set Real) (y : Real) (hu : IsOpen U) : (Ici y ≠ U) := by
  by_contra h
  rw [←h] at hu

  have h''' : IsClosed (Ici y) := by
      apply isClosed_Ici
  have ho : IsOpen (Ici y)ᶜ
  exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Ici y) ((Ici y)ᶜ) hu ho
  have huniv : Ici y ∪ (Ici y)ᶜ = univ := union_compl_self (Ici y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Ici, compl_Ici, nonempty_Iio, forall_const] at hr'
  rw [ici_cap_iio_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

def not_iic (U : Set Real) (y : Real) (hu : IsOpen U) : (Iic y ≠ U) := by
  by_contra h
  rw [←h] at hu

  have h''' : IsClosed (Iic y) := by
      apply isClosed_Iic
  have ho : IsOpen (Iic y)ᶜ
  exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Iic y) ((Iic y)ᶜ) hu ho
  have huniv : Iic y ∪ (Iic y)ᶜ = univ := union_compl_self (Iic y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Iic, compl_Iic, nonempty_Ioi, forall_const] at hr'
  rw [iic_cap_ioi_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

lemma ioc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Ioc x y) := by
  have hu : (Ioc x y) ∪ (Iio y) = (Iic y)
  ext p
  simp only [mem_union, mem_Ioc, mem_Iio, mem_Iic]
  apply Iff.intro
  intro h
  rcases h with (h1|h2)
  tauto
  exact le_of_lt h2
  by_cases hp : p = y
  intro h
  rw [hp]
  simp only [le_refl, and_true, lt_self_iff_false, or_false]
  exact hxy
  intro h
  right
  exact lt_of_le_of_ne h hp

  by_contra hopen
  have hopen' : IsOpen (Iio y) := isOpen_Iio
  have hopen'' : IsOpen (Iic y)
  rw [←hu]
  exact IsOpen.union hopen hopen'

  have hc : IsOpen ((Iic y)ᶜ)
  simp only [compl_Iic]
  exact isOpen_Ioi

  have hcon := isPreconnected_univ (Iic y) ((Iic y)ᶜ) hopen'' hc
               (by simp only [compl_Iic, Iic_union_Ioi, subset_refl])
               (by simp only [univ_inter, nonempty_Iic])
               (by simp only [compl_Iic, univ_inter, nonempty_Ioi])
  simp only [compl_Iic, univ_inter] at hcon
  rcases hcon with ⟨x,hx⟩
  simp at hx
  linarith

lemma ico_not_open (x y  : Real) (hxy : x < y) : ¬ IsOpen (Ico x y) := by
  have hxy' : -y < -x := neg_lt_neg_iff.mpr hxy
  have hn := ioc_not_open (-y) (-x) hxy'

  let f : Real → Real := fun x => - x
  let fb : Bijective f := ⟨ neg_injective, neg_surjective ⟩
  let fe := Equiv.ofBijective f fb
  have fc : Continuous fe := continuous_neg
  have fo : IsOpenMap fe := isOpenMap_neg ℝ
  have fh : Homeomorph Real Real
  apply Homeomorph.homeomorphOfContinuousOpen
  exact fc
  exact fo

  by_contra h

  have p := fo (Ico x y) h
  simp at p
  have he : fe '' (Ico x y) = Ioc (-y) (-x)
  · ext t

    have ht : ∀ s : Real, fe.symm (-s) = s := fun s => Equiv.ofBijective_symm_apply_apply f fb s
    have ht' := ht (-t)
    simp only [neg_neg] at ht'

    simp only [mem_image_equiv, mem_Ico, mem_Ioc]
    apply Iff.intro
    simp only [and_imp]
    intro h1
    intro h2
    constructor
    rw [ht'] at h1
    rw [ht'] at h2
    linarith

    rw [ht'] at h1
    rw [ht'] at h2
    linarith

    simp only [and_imp]
    intro h1
    intro h2
    rw [ht']
    constructor
    linarith
    linarith
  · rw [he] at p
    exact hn p

lemma icc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Icc x y) := by
  by_contra h
  have hc : IsClosed (Icc x y) := isClosed_Icc
  have hc'' : IsOpen ((Icc x y)ᶜ) := IsClosed.isOpen_compl

  have hcon := isPreconnected_univ (Icc x y) ((Icc x y)ᶜ) h hc''
               (by simp only [union_compl_self, subset_refl])
               (by simp only [univ_inter, nonempty_Icc]
                   linarith)
               (by simp only [univ_inter]
                   have hy : ((y + 1) ∈ (Icc x y)ᶜ)
                   simp only [mem_compl_iff, mem_Icc, add_le_iff_nonpos_right, not_and, not_le,
                     zero_lt_one, implies_true]
                   exact nonempty_of_mem hy)
  simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at hcon

lemma not_ioc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ioc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ioc x y)
    apply ioc_not_open x y
    exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ioc x y = ∅
    exact Ioc_eq_empty hxy
    rw [h] at h'
    tauto

def not_ico (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ico x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ico x y)
    apply ico_not_open x y
    exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ico x y = ∅
    exact Ico_eq_empty hxy
    rw [h] at h'
    tauto

def not_icc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Icc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Icc x y)
    apply icc_not_open x y
    exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · by_cases hyx : (x > y)
    · have h' : Icc x y = ∅
      exact Icc_eq_empty_of_lt hyx
      rw [h] at h'
      exact h'
    · have hxy' : x ≥ y := le_of_not_lt hxy
      have hyx' : x ≤ y := by exact le_of_not_lt hyx
      have hxx : x = y
      have hxy'' : (x = y) ∨ (y < x) := eq_or_lt_of_not_lt hxy
      have hyx'' : (x = y) ∨ (x < y) := by exact Or.symm (Decidable.lt_or_eq_of_le hyx')
      rcases hyx'' with (h|h)
      exact h
      tauto
      rw [←hxx] at h
      simp only [Icc_self] at h
      rw [←h] at hu
      exfalso
      have c : ¬ IsOpen {x} := not_isOpen_singleton x
      tauto

def classify_intervals (U : Set Real) (hu : IsOpen U) (hc : IsPreconnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) ∨ (U = ∅) := by
  have h : U ∈ (range (uncurry Icc)) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪  (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅})
  rw [←setOf_isPreconnected_eq_of_ordered]
  simp
  exact hc
  simp only [union_insert, union_singleton, mem_insert_iff, mem_union, mem_range, Prod.exists,
    uncurry_apply_pair] at h
  cases h
  case inl h => tauto
  case inr h =>
    cases h
    case inl h => tauto
    case inr h =>
      cases h
      case inr h =>
        cases h
        case inl h =>
          cases h
          case inr h => by_contra
                        rcases h with ⟨ x', hx ⟩
                        apply not_iic
                        exact hu
                        exact hx
          case inl h =>
            cases h
            case inr h => right ; right ; left ; assumption
            case inl h => by_contra
                          rcases h with ⟨ x', hx ⟩
                          apply not_ici
                          exact hu
                          exact hx
        case inr h => tauto
      case inl h =>
        cases h
        case inr h => left ; tauto
        case inl h =>
          cases h
          case inl h =>
            cases h
            case inl h => rcases h with ⟨ x, y, hx ⟩
                          right ; right ; right ; right
                          apply not_icc
                          exact hu
                          exact hx
            case inr h => rcases h with ⟨ x, y, hx ⟩
                          right ; right ; right ; right
                          apply not_ico
                          exact hu
                          exact hx
          case inr h => rcases h with ⟨ x, y, hx ⟩
                        right
                        right
                        right
                        right
                        apply not_ioc
                        exact hu
                        exact hx

macro "solve_disj" : tactic => `(tactic| repeat (apply Or.inl <|> apply Or.inr))

theorem classify_connected_interval (U : Set Real) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) := by
    have hpc : IsPreconnected U := by exact IsConnected.isPreconnected hc
    have hi := classify_intervals U hu hpc
    have ho : ¬ (U = ∅) := by
      by_contra hn
      rw [hn] at hc
      have he : (∅ : Set Real).Nonempty := IsConnected.nonempty hc
      exact Set.not_nonempty_empty he
    rcases hi with (h|h|h|h|h)
    left ; assumption
    right ; left ; assumption
    right ; right ; left ; assumption
    right ; right ; right ; assumption
    exfalso
    exact ho h

theorem classify_connected_nnreal_interval (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : NNReal), (U = Set.Iio x)) ∨
  (∃ (x : NNReal), (Set.Ioi x = U)) ∨
  (U = univ) := by
    by_cases h0 : 0 ∈ U
    · sorry
    · have hs : U ⊆ Ioi 0
      rintro x hx
      have hn0 : x ≠ 0 := ne_of_mem_of_not_mem hx h0
      simp only [mem_Ioi, gt_iff_lt]
      exact pos_iff_ne_zero.mpr hn0
      have hioi : IsOpen (Ioi (0 : NNReal)) := isOpen_Ioi
      let f : (Ioi (0 : NNReal)) → Real := fun a => ↑a
      let U' : Set ℝ := {x : ℝ | 0 < x ∧ (∃ y : U, y = x)}

      have hu' : IsOpen (coe '' U)

      let inclusion : (Ioi (0 : Real)) ≤ (univ : Set Real) := by simp only [le_eq_subset,
        subset_univ]

      let f := TopologicalSpace.Opens.inclusion inclusion
