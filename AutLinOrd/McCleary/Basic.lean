import Mathlib
import AutLinOrd.OrdClosure

/-! # Basic
  This file shows that the automorphisms of a linear order
  form a lattice ordered group.

  These four properties show that `(S ≃o S)` is a lattice ordered group:
  - `Lattice (S ≃o S)`
  - `Group (S ≃o S)`
  - `MulLeftMono (S ≃o S)`
  - `MulRightMono (S ≃o S)`
-/

variable [LinearOrder S]

/--
  Automorphisms are ordered by the pointwise ordering.
-/
instance : Preorder (S ≃o S) where
  le f g := ∀s : S, f s ≤ g s
  le_refl := by simp
  le_trans f g h hf hg s := (hf s).trans (hg s)

/-- The definition of ≤ for automorphisms. -/
theorem aut_le_iff (f g : S ≃o S) : f ≤ g ↔ ∀s : S, f s ≤ g s := by rfl

instance : PartialOrder (S ≃o S) where
  le_antisymm f g f_le_g g_le_f := by
    simp only [aut_le_iff] at g_le_f f_le_g
    have (s : S) := ((f_le_g s).antisymm (g_le_f s))
    simp only [← funext_iff, DFunLike.coe_fn_eq] at this
    exact this

/--
  The supremum of two automorphisms is their pointwise maximum.
-/
def aut_sup (f g : S ≃o S) : S ≃o S where
  toFun x := max (f x) (g x)
  invFun x := min (f.symm x) (g.symm x)
  map_rel_iff' {a b} := by
    simp only [Equiv.coe_fn_mk, le_sup_iff, sup_le_iff, map_le_map_iff]
    constructor
    · rintro (⟨a_le_b, _⟩ | ⟨_, a_le_b⟩)
      <;> assumption
    · intro a_le_b
      have ga_le_gb : g a ≤ g b := OrderIso.monotone g a_le_b
      have fa_le_fb : f a ≤ f b := OrderIso.monotone f a_le_b
      obtain a_le_fb | fb_le_ga := Std.IsLinearPreorder.le_total (g a) (f b)
      · left; grind
      · right
        constructor <;> order
  left_inv := by
    simp only [Function.LeftInverse, map_sup, OrderIso.symm_apply_apply]
    intro s
    obtain fs_le_gs | gs_le_fs := Std.IsLinearPreorder.le_total (f s) (g s)
    · have : g.symm (f s) ≤ g.symm (g s) := g.symm.monotone fs_le_gs
      simp only [OrderIso.symm_apply_apply] at this
      simp [this]
    · have : f.symm (g s) ≤ f.symm (f s) := f.symm.monotone gs_le_fs
      simp only [OrderIso.symm_apply_apply] at this
      simp [this]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, map_inf, OrderIso.apply_symm_apply]
    intro s
    obtain fs_le_gs | gs_le_fs := Std.IsLinearPreorder.le_total (f.symm s) (g.symm s)
    · have : f (f.symm s) ≤ f (g.symm s) := f.monotone fs_le_gs
      simp only [OrderIso.apply_symm_apply] at this
      simp [this]
    · have : g (g.symm s) ≤ g (f.symm s) := g.monotone gs_le_fs
      simp only [OrderIso.apply_symm_apply] at this
      simp [this]

/-- The supremum of autormophisms forms a semilattice. -/
instance : SemilatticeSup (S ≃o S) where
  sup f g := aut_sup f g
  le_sup_left f g s := by simp [aut_sup]
  le_sup_right f g s := by simp [aut_sup]
  sup_le f g h f_le_h g_le_h s := by
    simp only [aut_sup, RelIso.coe_fn_mk, Equiv.coe_fn_mk, sup_le_iff]
    constructor
    · exact f_le_h s
    · exact g_le_h s

/-- The infimum of two automorphisms is their pointwise minimum. -/
def aut_inf (f g : S ≃o S) : S ≃o S where
  toFun x := min (f x) (g x)
  invFun x := max (f.symm x) (g.symm x)
  map_rel_iff' {a b} := by
    simp only [Equiv.coe_fn_mk]
    constructor
    · simp only [le_inf_iff, inf_le_iff, map_le_map_iff, and_imp]
      rintro (a_le_b | ga_le_fb) (fa_le_gb | a_le_b)
      <;> try assumption
      · obtain ga_le_gb | gb_lt_ga := le_or_gt (g a) (g b)
        · simpa using ga_le_gb
        · have : f a ≤ f b := by order
          simpa using this
    · intro a_le_b
      have ga_le_gb : g a ≤ g b := OrderIso.monotone g a_le_b
      have fa_le_fb : f a ≤ f b := OrderIso.monotone f a_le_b
      order
  left_inv := by
    simp only [Function.LeftInverse, map_inf, OrderIso.symm_apply_apply]
    intro s
    obtain fs_le_gs | gs_le_fs := Std.IsLinearPreorder.le_total (f s) (g s)
    · have : f.symm (f s) ≤ f.symm (g s) := f.symm.monotone fs_le_gs
      simp only [OrderIso.symm_apply_apply] at this
      simp [this]
    · have : g.symm (g s) ≤ g.symm (f s) := g.symm.monotone gs_le_fs
      simp only [OrderIso.symm_apply_apply] at this
      simp [this]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, map_sup, OrderIso.apply_symm_apply]
    intro s
    obtain fs_le_gs | gs_le_fs := Std.IsLinearPreorder.le_total (f.symm s) (g.symm s)
    · have : g (f.symm s) ≤ g (g.symm s) := g.monotone fs_le_gs
      simp only [OrderIso.apply_symm_apply] at this
      simp [this]
    · have : f (g.symm s) ≤ f (f.symm s) := f.monotone gs_le_fs
      simp only [OrderIso.apply_symm_apply] at this
      simp [this]

/-- The infimum of automorphisms forms a semilattice. -/
instance : SemilatticeInf (S ≃o S) where
  inf f g := aut_inf f g
  inf_le_left f g s := by simp [aut_inf]
  inf_le_right f g s := by simp [aut_inf]
  le_inf f g h f_le_h g_le_h s := by
    simp only [aut_inf, RelIso.coe_fn_mk, Equiv.coe_fn_mk, le_inf_iff]
    constructor
    · exact f_le_h s
    · exact g_le_h s

/-- The automorphisms form a lattice. -/
instance : Lattice (S ≃o S) where

/-- Group multiplication on the left is montone. -/
instance : MulLeftMono (S ≃o S) where
  elim := by simp [Covariant, aut_le_iff]

/-- Group multiplication on the right is monotone. -/
instance : MulRightMono (S ≃o S) where
  elim := by
    simp only [Covariant, aut_le_iff, RelIso.coe_mul, Function.comp_apply]
    intro f g h g_le_h s
    exact g_le_h (f s)
