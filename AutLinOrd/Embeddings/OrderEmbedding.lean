import Mathlib

variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]


theorem image_sum_eq_sum_image (f : α ⊕ₗ β ↪o γ) :
    Set.range f = Set.range (f ∘ Sum.inlₗ) ∪ Set.range (f ∘ Sum.inrₗ) := by
  ext z
  simp
