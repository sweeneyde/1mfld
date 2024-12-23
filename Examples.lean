import Mathlib.Tactic

section

variable (X : Type*)
variable [TopologicalSpace X]

-- The set consisting of the whole space is open.
def example01 : IsOpen (Set.univ : Set X) := by
  exact isOpen_univ

end section

section

-- If A ⊂ R is open, then A ∩ (0,1) is open.
def example02 (A : Set ℝ) (h : IsOpen A) : IsOpen (A ∩ Set.Ioo 0 1) := by
  have h2 : IsOpen (Set.Ioo (0 : ℝ) 1) := by exact isOpen_Ioo
  exact IsOpen.inter h h2

end section

section

-- The "discrete topology" on Y satisfies our axioms
variable (Y : Type*)
instance example03 : TopologicalSpace Y where
  IsOpen (h : Set Y) : Prop := True
  isOpen_univ := by triv
  isOpen_inter := by
    intros s t
    intro hs ht
    triv
  isOpen_sUnion := by
    intros ss
    intro hs 
    triv

end section

section

variable (A B C : Type*)
variable [TopologicalSpace A]
variable [TopologicalSpace B]
variable [TopologicalSpace C]
variable (f : A → B) (g : B → C)

-- The composition of continuous functions is continuous
def example04 (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := Continuous.comp hg hf

end section

section

def I₁ := Set.Ioo 0 1
def I₂ := Set.Ioo 0 2

variable [TopologicalSpace I₁]
variable [TopologicalSpace I₂]

-- Building a continuous function
def example05 : ∃ (f : I₁ → I₂), Continuous f := by
  use (fun ⟨ x, p ⟩ => ⟨ x + x, by apply? ⟩ )
  apply?


end section
