import Mathlib
import AutLinOrd.NonDecrAt

variable {α : Type*} [LinearOrder α]

/--
  `z_interval f x z` is the closed open interval `[(f ^ z) x, (f ^ (z+1)) x)`.
-/
def z_interval (f : α ≃o α) (x : α) (z : ℤ := 0) : Set α :=
  let f' := non_decr_at f x
  Set.Ico ((f'^z) x) ((f'^(z+1)) x)

/--
  If `y` is in `z_interval f x z`, then
  `y` is in the orbital of `x` under `f`.
-/
theorem mem_z_interval_mem_orbital {f : α ≃o α} {x y : α} {z : ℤ}
    (mem: y ∈ z_interval f x z) : y ∈ elem_orbital f x := by
  simp only [z_interval, Set.mem_Ico] at mem
  rw [non_decr_eq_elem_orbital, mem_elem_orbital_iff]
  constructor
  · use z
    exact mem.1
  · use z + 1
    exact mem.2.le

/--
  If `y` is in `z_interval f x z`, then
  `(non_decr_at f x ^ w) y` is in the orbital of `x` under `f`.
-/
theorem mem_z_interval_non_decr_pow_mem_orbital {f : α ≃o α} {x y : α} {z w : ℤ}
    (mem: y ∈ z_interval f x z) : (non_decr_at f x ^ w) y ∈ elem_orbital f x :=
  orig_mem_orbital_pow_mem_orbital (mem_z_interval_mem_orbital mem) w

/--
  If `y` is in `z_interval f x z`, then
  `(non_decr_at f x) y` is in `z_interval f x (z+1)`.
-/
theorem up_z_interval {f : α ≃o α} {x : α} {z : ℤ} {y : α}
    (y_mem : y ∈ z_interval f x z) :
    (non_decr_at f x) y ∈ z_interval f x (z+1) := by
  simp only [z_interval, add_comm z, ← add_pows, zpow_one,
    Set.mem_Ico, map_le_map_iff, OrderIso.lt_iff_lt] at y_mem ⊢
  constructor
  · exact y_mem.1
  · simp only [
      show (non_decr_at f x) x = ((non_decr_at f x) ^ (1 : ℤ)) x by simp,
      zpow_one, add_pows, add_comm z]
    simp only [← add_pows, zpow_one, y_mem.2]

/--
  If `y` is in `z_interval f x z`, then
  `((non_decr_at f x)^(-1)) y` is in `z_interval f x (z-1)`.
-/
theorem down_z_interval {f : α ≃o α} {x : α} {z : ℤ} {y : α}
    (y_mem : y ∈ z_interval f x z) :
    ((non_decr_at f x)^(-(1 : ℤ))) y ∈ z_interval f x (z-1) := by
  simp only [z_interval, Set.mem_Ico, map_le_map_iff,
    OrderIso.lt_iff_lt] at y_mem ⊢
  simp only [sub_eq_neg_add, ←add_pows, Int.reduceNeg, zpow_one,
    map_le_map_iff, neg_add_cancel_comm]
  constructor
  · exact y_mem.1
  · apply_fun (non_decr_at f x)
    simp [add_pows_one, add_comm, y_mem.2]

/--
  If `y` is in `z_interval f x z`, then
  `((non_decr_at f x)^d) y` is in `z_interval f x (z + d)`.
-/
theorem shift_z_interval {f : α ≃o α} {x y : α} {z : ℤ}
    (y_mem : y ∈ z_interval f x z) (d : ℤ) :
    ((non_decr_at f x)^d) y ∈ z_interval f x (z + d) := by
  induction d with
  | hz => simp [y_mem]
  | hp i ih =>
    conv_rhs => rw [←add_comm 1, ←add_pows, zpow_one]
    conv_lhs => rw [←add_assoc z]
    exact up_z_interval ih
  | hn i ih =>
    conv_rhs => rw [neg_sub_comm, ←sub_pows]
    conv_lhs => rw [show z + (-(i : ℤ) - 1) = z + (-(i : ℤ)) - 1 by omega]
    exact down_z_interval ih

/--
  `z_interval f x z₁` is isomorphic to `z_interval f x z₂`.
-/
def z_interval_iso (f : α ≃o α) (x : α) (z₁ z₂ : ℤ) :
    z_interval f x z₁ ≃o z_interval f x z₂ where
  toFun y := ⟨((non_decr_at f x) ^ (z₂ - z₁)) y, by
    have := shift_z_interval y.property (z₂ - z₁)
    simpa⟩
  invFun y := ⟨((non_decr_at f x) ^ (z₁ - z₂)) y, by
    have := shift_z_interval y.property (z₁ - z₂)
    simpa⟩
  left_inv := by simp [Function.LeftInverse, add_pows]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, add_pows]
  map_rel_iff' := by simp

/--
  If `z < w`, then all elements of `z_interval f x z`
  are less than all elements of `z_interval f x w`.
-/
theorem lt_z_interval {f : α ≃o α} {x : α} {z w : ℤ} (z_lt_w : z < w)
    {a b : α} (a_mem : a ∈ z_interval f x z) (b_mem : b ∈ z_interval f x w) :
    a < b := by
  simp only [z_interval, Set.mem_Ico] at a_mem b_mem
  calc a
  _ < (non_decr_at f x ^ (z+1)) x := a_mem.2
  _ ≤ (non_decr_at f x ^ w) x := non_decr_at_pow_ge_ge z_lt_w
  _ ≤ b := b_mem.1

/--
  If `f x ≠ x` and `y` is in the orbital of `x` under `f`,
  then `get_z` returns the `z`th copy of `z_interval f x`
  that `y` lies in.
-/
noncomputable def get_z {f : α ≃o α} {x y : α} (not_fix : f x ≠ x)
    (y_mem : y ∈ elem_orbital f x) : ℤ :=
  ((not_fix_non_decr_mem_orbital_strong_iff
    (non_decr_at_fix_iff_orig_fix.mp.mt not_fix)).mp (y_mem)).choose

/--
  If `f x ≠ x` and `y` is in the orbital of `x` under `f`,
  then `get_z` returns the `z`th copy of `z_interval f x`
  that `y` lies in.
-/
theorem get_z_spec {f : α ≃o α} {x y : α} (not_fix : f x ≠ x)
    (y_mem : y ∈ elem_orbital f x) :
    ((non_decr_at f x)^(get_z not_fix y_mem)) x ≤ y ∧
    y < ((non_decr_at f x) ^ (get_z not_fix y_mem + 1)) x := by
  simp [get_z]
  exact
    ((not_fix_non_decr_mem_orbital_strong_iff
    (non_decr_at_fix_iff_orig_fix.mp.mt not_fix)).mp (y_mem)).choose_spec

/--
  If `f x ≠ x` and `y` is in the orbital of `x` under `f`,
  then letting `z` be the result of `get_z`,
  `y ∈ z_interval f x z`.
-/
theorem mem_get_z {f : α ≃o α} {x y : α} (not_fix : f x ≠ x)
    (y_mem : y ∈ elem_orbital f x) :
    y ∈ z_interval f x (get_z not_fix y_mem) := by
  simp [z_interval, get_z_spec]

/--
  If `y` is in `z_interval f x z`, then `get_z` of `y` is `z`.
-/
theorem get_z_mem {f : α ≃o α} {x y : α} (not_fix : f x ≠ x) (z : ℤ)
    (y_mem : y ∈ z_interval f x z) :
    get_z not_fix (mem_z_interval_mem_orbital y_mem) = z := by
  set m := get_z not_fix (mem_z_interval_mem_orbital y_mem)
  have y_mem_m : y ∈ z_interval f x m :=
    mem_get_z not_fix (mem_z_interval_mem_orbital y_mem)
  by_contra!
  obtain m_lt_z | m_eq_z | z_lt_m := Int.lt_trichotomy m z
  · have := lt_z_interval m_lt_z y_mem_m y_mem
    order
  · contradiction
  · have := lt_z_interval z_lt_m y_mem y_mem_m
    order

/--
  If `y` is in the orbital of `x` under `f`,
  then `get_z` of `((non_decr_at f x)^z) x` is
  `get_z` of `y` plus `z`.
-/
theorem pow_get_z_pow {f : α ≃o α} {x y : α} {z : ℤ} (not_fix : f x ≠ x)
    (y_mem : y ∈ elem_orbital f x) :
    get_z (y := (non_decr_at f x ^ z) y) not_fix (by
      rw [non_decr_eq_elem_orbital] at y_mem ⊢
      exact pow_mem_elem_orbital z y_mem) = get_z not_fix y_mem + z := by
  have := shift_z_interval (mem_get_z not_fix y_mem) z
  exact get_z_mem not_fix ((get_z not_fix y_mem) + z) this

/--
  If `y` is in the zeroth copy,
  then `get_z` of `(non_decr_at f x ^ z) y` is `z`.
-/
theorem mem_zeroth_copy_shift_get_z {f : α ≃o α} {x y : α} (z : ℤ)
    (not_fix : f x ≠ x) (mem : y ∈ z_interval f x) :
    get_z (y := (non_decr_at f x ^ z) y) not_fix
      (mem_z_interval_non_decr_pow_mem_orbital mem) = z := by
  have y_mem_orbital := mem_z_interval_mem_orbital mem
  have : z = get_z not_fix y_mem_orbital + z := by
    simp [get_z_mem not_fix 0 mem]
  rw [this]
  convert pow_get_z_pow not_fix y_mem_orbital (z := z)
  exact this.symm

/--
  If `t` is in the orbital of `x` under `f`,
  then `zeroth_copy t` is the element of `z_interval f x`
  that is analgous to `t` (aka some power of `f` maps
  `zeroth_copy t` to `t`).
-/
noncomputable def zeroth_copy {f : α ≃o α} {x : α} (not_fix : f x ≠ x)
    (t : elem_orbital f x) : z_interval f x :=
  let z := get_z not_fix t.property
  let z_spec := get_z_spec not_fix t.property
  ⟨((non_decr_at f x)^(-z)) t, by
      have := shift_z_interval z_spec (-z)
      simpa [z]⟩

/--
  `zsum_z_interval_iso` is an order isomorphism from
  the orbital of `x` under `f` and `ℤ ×ₗ (z_interval f x)`.
-/
noncomputable def zsum_z_interval_iso {f : α ≃o α} {x : α} (not_fix : f x ≠ x) :
    elem_orbital f x ≃o ℤ ×ₗ (z_interval f x) where
  toFun t := toLex (get_z not_fix t.property, zeroth_copy not_fix t)
  invFun t := ⟨((non_decr_at f x)^((ofLex t).1)) (ofLex t).2, by
    have := mem_z_interval_mem_orbital (ofLex t).2.property
    exact orig_mem_orbital_pow_mem_orbital this (ofLex t).1⟩
  left_inv := by simp [Function.LeftInverse, zeroth_copy]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, zeroth_copy,
      zpow_neg, Lex.forall, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq,
      Prod.forall, Prod.mk.injEq, Subtype.forall, Subtype.mk.injEq]
    intro z t t_mem
    constructor
    · exact mem_zeroth_copy_shift_get_z z not_fix t_mem
    · simp [mem_zeroth_copy_shift_get_z z not_fix t_mem]
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, Subtype.forall, Subtype.mk_le_mk]
    intro a a_mem b b_mem
    constructor
    · intro h
      simp only [Prod.Lex.toLex_le_toLex] at h
      obtain az_lt_bz | ⟨az_eq_bz, azero_lt_bzero⟩ := h
      ·  exact (lt_z_interval az_lt_bz
            (get_z_spec not_fix a_mem) (get_z_spec not_fix b_mem)).le
      · simpa [zeroth_copy, az_eq_bz] using azero_lt_bzero
    · intro a_le_b
      simp [Prod.Lex.toLex_le_toLex]
      sorry
