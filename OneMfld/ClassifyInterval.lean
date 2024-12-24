import Mathlib

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

noncomputable def homeo_nnreal_real : (Set.Ioi 0 : Set NNReal) ≃ₜ (Set.univ : Set Real) where
  toFun := fun ⟨x,_⟩ => ⟨ Real.log x, trivial ⟩
  invFun := fun ⟨x,_⟩ => ⟨ ⟨ Real.exp x, Real.exp_nonneg x ⟩, Real.exp_pos x ⟩
  left_inv := fun ⟨ ⟨ x, nn ⟩, p ⟩  => by
    simp only [NNReal.coe_mk, Subtype.mk.injEq]
    ext
    simp only [NNReal.coe_mk]
    exact Real.exp_log p
  right_inv := fun x => by
    simp only [NNReal.coe_mk, Real.log_exp, Subtype.coe_eta]
  continuous_toFun := by
    simp only
    refine Continuous.subtype_mk ?_ fun x => trivial
    refine Continuous.log ?_ ?_
    exact Isometry.continuous fun x1 => congrFun rfl
    intro x
    rcases x with ⟨x,hx⟩
    simp only [ne_eq, NNReal.coe_eq_zero]
    exact pos_iff_ne_zero.mp hx
  continuous_invFun := by
    simp only
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.rexp
    exact continuous_subtype_val

def relu (x : ℝ) : NNReal :=
  ⟨max x 0, by simp [le_max_left]⟩

lemma relu_zero : (relu 0 = 0) := by
  have : max (0 : Real) (0 : Real) = (0 : Real) := by exact max_self 0
  dsimp [relu]
  simp only [max_self, NNReal.mk_zero]

theorem continuous_relu : Continuous relu := by
  apply Continuous.subtype_mk
  apply Continuous.max
  exact continuous_id'
  exact continuous_const


lemma proj_relu {x : ℝ} (h : x > 0) : (relu x).toReal = x := by
  have : max x 0 = x := max_eq_left_of_lt h
  exact this

lemma proj_relu' {x : ℝ} (h : x <= 0) : (relu x).toReal = 0 := by
  have : 0 = max x 0 := right_eq_sup.mpr h
  dsimp [relu]
  rw [←this]

lemma relu_proj {x : NNReal} : (relu x.toReal) = x := by
  by_cases h0 : x = 0
  · rw [h0]
    simp only [NNReal.val_eq_coe, NNReal.coe_zero]
    rw [relu_zero]
  · have : x > 0 := by exact pos_iff_ne_zero.mpr h0
    refine NNReal.eq ?_
    rw [proj_relu]
    exact this

lemma relu_mono : StrictMonoOn relu (Set.Ici 0) := by
  intro x
  intro hx
  intro y
  intro hy
  intro h
  simp only [mem_Ici] at hx
  simp only [mem_Ici] at hy
  apply NNReal.coe_lt_coe.mp

  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [NNReal.coe_lt_coe]
    by_cases hy0 : y = 0
    · rw [hy0]
      simp only [lt_self_iff_false]
      linarith
    · have hy' : y > 0 := by linarith
      apply NNReal.coe_lt_coe.mp
      rw [proj_relu hy']
      rw [relu_zero]
      simp only [NNReal.coe_zero]
      assumption
  · have hx' : x > 0 := by exact lt_of_le_of_ne hx fun a => hx0 (id (Eq.symm a))
    rw [proj_relu hx']
    by_cases hy0 : y = 0
    · rw [hy0]
      rw [relu_zero]
      simp only [NNReal.coe_zero, gt_iff_lt]
      linarith
    · have hy' : y > 0 := by linarith
      rw [proj_relu hy']
      assumption

lemma relu_interval_ioo {U : Set NNReal} {a b : Real} (h : Ioo a b = relu ⁻¹' U) :
  (relu '' (Set.Ioo a b) = U) := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · intro ⟨y,⟨ hya, hyb ⟩,hy'⟩
    have : y ∈ Set.Ioo a b := by
      apply mem_Ioo.mpr
      exact ⟨ hya, hyb ⟩
    rw [h] at this
    simp only [mem_preimage] at this
    rw [hy'] at this
    assumption
  · intro hx
    use x.1
    simp only [NNReal.val_eq_coe]
    rw [relu_proj]
    simp only [and_true]

    by_cases h0 : 0 ∈ U
    · have hneg : ¬ BddBelow (relu ⁻¹' U) := by
        by_contra hneg
        rcases hneg with ⟨ b, hb ⟩
        have hn : Set.Iio 0 ⊆ relu ⁻¹' U := by
          intro z
          simp only [mem_Iio, mem_preimage]
          intro hz
          have : (relu z) = 0 := by
            apply NNReal.coe_eq_zero.mp
            rw [proj_relu']
            linarith
          rw [this]
          assumption
      rw [←h] at hneg
      exfalso
      exact hneg bddBelow_Ioo
    · have hpos : x > 0 := by
        have hnonneg : x ≥ 0 := by exact zero_le x
        have hzero : x ≠ 0 := by exact ne_of_mem_of_not_mem hx h0
        exact pos_iff_ne_zero.mpr hzero
      have : relu (NNReal.toReal x) = x := by exact relu_proj
      rw [←this] at hx
      have : ↑x ∈ relu ⁻¹' U := by exact hx
      rw [←h] at this
      exact this

theorem StrictMonoOn.injOn_Ioo {α : Type u_1} {β : Type u_2} {f : α → β}
  [LinearOrder α] [LinearOrder β] {a : α} {b : α} (h : StrictMonoOn f (Set.Icc a b)) :
  InjOn f (Set.Ioo a b) := by
      intro x hx y hy hf
      have hx' : x ∈ Set.Icc a b := by exact mem_Icc_of_Ioo hx
      have hy' : y ∈ Set.Icc a b := by exact mem_Icc_of_Ioo hy
      by_cases hxy : x < y
      · have : f x < f y := by
          exact h hx' hy' (hxy)
        exfalso
        rw [hf] at this
        exact (lt_self_iff_false (f y)).mp this
      · by_cases hyx : y < x
        · have : f y < f x := by
            exact h hy' hx' hyx
          exfalso
          rw [hf] at this
          exact (lt_self_iff_false (f y)).mp this
        · have hyx' : x ≤ y := le_of_not_lt hyx
          have hxy' : y ≤ x := le_of_not_lt hxy
          apply le_antisymm
          assumption
          assumption

lemma relu_interval_ioo' {U : Set NNReal} {a b : Real} :
  (relu '' (Set.Ioo a b) = Set.Ioo (relu a) (relu b)) ∨
  (relu '' (Set.Ioo a b) = Set.Ico 0 (relu b)) ∨
  (relu '' (Set.Ioo a b) = { 0 }) ∨
  (relu '' (Set.Ioo a b) = ∅) := by
  by_cases ha : a > 0
  · by_cases hb : b > 0
    · left
      ext z
      simp only [mem_image, mem_Ioo]
      constructor
      · intro ⟨ x, ⟨ hx, hxz ⟩ ⟩
        have hax : relu a < relu x := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          rw [proj_relu]
          exact hx.1
        have hxb : relu x < relu b := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          rw [proj_relu]
          exact hx.2
        rw [hxz] at hax
        rw [hxz] at hxb
        exact ⟨hax, hxb⟩
      · intro ⟨ haz, hzb ⟩
        use z
        rw [relu_proj]
        simp only [and_true]
        have haz' : NNReal.toReal (relu a) < NNReal.toReal z := by exact haz
        have hzb' : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
        rw [proj_relu] at hzb'
        rw [proj_relu] at haz'
        exact ⟨haz', hzb'⟩
        exact ha
        exact hb
    · have : Ioo a b = ∅ := by
        ext z
        simp only [mem_Ioo, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro ha
        linarith
      rw [this]
      simp only [image_empty]
      simp only [or_true]
  · by_cases hb : b > 0
    · by_cases ha0 : a = 0
      · rw [ha0]
        left
        ext z
        simp only [mem_image, mem_Ioo]
        apply Iff.intro
        · intro ⟨ y, ⟨ h0y, hyb ⟩, hyz ⟩
          rw [←hyz]
          apply And.intro
          · rw [relu_zero]
            have : NNReal.toReal (relu 0) < NNReal.toReal (relu y) := by
              rw [proj_relu]
              rw [proj_relu]
              assumption
            exact pos_of_gt this
          · have : NNReal.toReal (relu y) < NNReal.toReal (relu b) := by
              rw [proj_relu]
              rw [proj_relu]
              assumption
            exact this
        · intro ⟨ h0z, hzb ⟩
          use z.toReal
          apply And.intro
          · apply And.intro
            · rw [relu_zero] at h0z
              have : 0 < NNReal.toReal (relu z) := by
                rw [proj_relu]
                exact h0z
              exact h0z
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              exact Real.lt_toNNReal_iff_coe_lt.mp hzb
          · exact relu_proj
      · right ; left
        ext z
        simp only [mem_image, mem_Ioo, mem_Ico, zero_le, true_and]
        apply Iff.intro
        · intro ⟨ y, ⟨ hay, hyb ⟩ , hyz ⟩
          rw [←hyz]
          have : NNReal.toReal (relu y) < NNReal.toReal (relu b) := by
            rw [proj_relu]
            rw [proj_relu]
            assumption
          exact this
        · intro hzb
          use NNReal.toReal z
          apply And.intro
          · apply And.intro
            · have ha0' : a < 0 := by
                simp only [gt_iff_lt, not_lt] at ha
                exact lt_of_le_of_ne ha ha0
              have h0z : 0 ≤ (relu z) := by exact zero_le (relu z)
              have h0z' : a < relu z := by exact gt_of_ge_of_gt h0z ha0'
              rw [relu_proj] at h0z'
              assumption
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              rw [proj_relu] at this
              assumption
              assumption
          · rw [relu_proj]
    · by_cases hab : a ≥ b
      · have : Ioo a b = ∅ := by
          exact Ioo_eq_empty_of_le hab
        rw [this]
        simp only [image_empty, or_true]
      · right ; right ; left
        ext z
        simp only [mem_image, mem_Ioo, mem_singleton_iff]
        constructor
        · rintro ⟨ y, hy, hyz ⟩
          have : y ≤ 0 := by linarith
          have h' := proj_relu' this
          rw [hyz] at h'
          exact NNReal.coe_eq_zero.mp h'
        · intro hz
          have hab' : a < b := by linarith
          use (a + b) / 2
          apply And.intro
          · apply And.intro
            · exact left_lt_add_div_two.mpr hab'
            · exact add_div_two_lt_right.mpr hab'
          · have hn : (a + b) / 2 ≤ 0 := by linarith
            rw [hz]
            apply NNReal.coe_eq_zero.mp
            exact proj_relu' hn


lemma relu_ioo {U : Set NNReal} (h : ∃ x y, Ioo x y = Ioi 0 ∩ NNReal.toReal '' U) :
  (∃ x y, Ioo x y = U) ∨ (∃ y, Iio y = U) ∨ ({0} = U) ∨ (∅ = U):= by
  rcases h with ⟨a,b,h⟩
  by_cases hab : a < b
  · have ha : a ≥ 0 := by
      have : sInf (Set.Ioo a b) = a := csInf_Ioo hab
      rw [h] at this
      rw [←this]
      simp only [ge_iff_le]
      apply Real.sInf_nonneg
      intro x hx
      have hx' : x ∈ Set.Ioi 0 := mem_of_mem_inter_left hx
      exact le_of_lt hx'
    have hb : b ≥ 0 := by linarith
    by_cases h0 : 0 ∈ U
    · right ; left
      use ⟨ b, hb ⟩
      ext x
      simp only [mem_Iio]
      constructor
      · intro hx
        by_cases hx0 : x > 0
        · have hi : NNReal.toReal x ∈ Set.Ioi 0 := by exact hx0
          have h : NNReal.toReal x ∈ Set.Ioo a b := by
            simp only [mem_Ioo]
            constructor

        · sorry
      · intro hx
        sorry
    · left
      use ⟨ a, ha ⟩
      use ⟨ b, hb ⟩
      ext x
      simp only [mem_Ioo]
      constructor
      · intro ⟨ha', hb'⟩
        have hx' : NNReal.toReal x ∈ Set.Ioo a b := by
          apply mem_Ioo.mpr
          exact ⟨ha', hb'⟩
        rw [h] at hx'
        have hx'' : NNReal.toReal x ∈ NNReal.toReal '' U := mem_of_mem_inter_right hx'
        simp only [mem_image, NNReal.coe_inj, exists_eq_right] at hx''
        assumption
      · intro hu
        have hx1 : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hu
        have hx2 : NNReal.toReal x ∈ Set.Ioi 0 := by
          apply mem_Ioi.mpr
          apply NNReal.coe_pos.mpr
          have : x ≠ 0 := ne_of_mem_of_not_mem hu h0
          exact pos_iff_ne_zero.mpr this
        have : NNReal.toReal x ∈ Set.Ioo a b := by
          rw [h]
          exact mem_inter hx2 hx1
        exact this
  · have : Ioo a b = ∅ := Ioo_eq_empty hab
    rw [this] at h
    by_cases h0 : 0 ∈ U
    · right ; right ; left
      ext x
      constructor
      · exact fun a => mem_of_eq_of_mem a h0
      · intro hx
        simp only [mem_singleton_iff]
        by_cases hx0 : x > 0
        · have : NNReal.toReal x ∈ Set.Ioi 0 := hx0
          have this' : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hx
          have this'' : NNReal.toReal x ∈ (∅ : Set Real) := by
            rw [h]
            exact mem_inter hx0 this'
          exact False.elim this''
        · have : x ≥ 0 := by exact zero_le x
          have this' : x ≤ 0 := by exact le_of_not_lt hx0
          exact nonpos_iff_eq_zero.mp this'
    · right ; right ; right
      ext x
      simp only [mem_empty_iff_false, false_iff]
      by_cases hx0 : x > 0
      · by_contra hu
        have : NNReal.toReal x ∈ NNReal.toReal '' U := mem_image_of_mem NNReal.toReal hu
        have this' : NNReal.toReal x ∈ Set.Ioi 0 := hx0
        have this'' : NNReal.toReal x ∈ Set.Ioi 0 ∩ NNReal.toReal '' U  := mem_inter hx0 this
        rw [←h] at this''
        exact this''
      · have : x ≥ 0 := by exact zero_le x
        have this' : x ≤ 0 := by exact le_of_not_lt hx0
        have this'' : x = 0 := by exact nonpos_iff_eq_zero.mp this'
        exact Eq.mpr_not (congrArg (Membership.mem U) this'') h0

theorem classify_connected_nnreal_interval (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : NNReal), (Set.Iio x = U)) ∨
  (∃ (x : NNReal), (Set.Ioi x = U)) ∨
  (U = univ) := by
    let U0 := U ∩ (Set.Ioi 0)
    have hu0 : IsOpen U0 := IsOpen.inter hu isOpen_Ioi

    let U' := relu ⁻¹' U0

    have hr : (relu ⁻¹' U0) = (Set.Ioi (0 : Real)) ∩ (NNReal.toReal '' U) := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_Ioi, mem_image]
      constructor
      · intro h
        have : U0 ⊆ Set.Ioi 0 := inter_subset_right
        have hr : relu x ∈ Set.Ioi 0 := this h
        simp at hr
        have hr' : 0 < x := Real.toNNReal_pos.mp (this h)
        constructor
        · exact hr'
        · use relu x
          constructor
          · have : U0 ⊆ U := by exact inter_subset_left
            exact this h
          · have hf : (relu x).1 = x := by
              apply proj_relu
              assumption
            assumption
      · rintro ⟨h1,⟨y,⟨hu,hy⟩⟩⟩
        rw [←hy]
        rw [relu_proj]
        apply mem_inter hu
        rw [←hy] at h1
        exact h1

    have hu' : IsOpen U' := Continuous.isOpen_preimage continuous_relu U0 hu0
    have hc' : IsConnected U' := by sorry

    let c := classify_connected_interval U' hu' hc'
    rcases c with (c|c|c|c)
    · dsimp [U'] at c
      simp only at c
      rcases c with ⟨x,y,c⟩
      have c' := relu_interval_ioo c

      rw [hr] at c
      have c' := relu_ioo c
      rcases c' with (c'|c')
      · left
        assumption
      · right
        left
        assumption
    · sorry
    · sorry
    · sorry
