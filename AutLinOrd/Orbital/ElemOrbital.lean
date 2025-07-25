import AutLinOrd.IncrDecr
import AutLinOrd.OrdClosure
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Order.Group.Action.End
import Mathlib.Data.Int.LeastGreatest
import Mathlib.GroupTheory.GroupAction.Defs

/-!
  This file defines `elem_orbit f x`, which is the orbit of `x` under `f`.
  It then defines `elem_orbital f x`, the orbital of `x` under `f`,
  as the `OrdClosure` of the orbit of `x`
  under `f`. It then proves many key facts about the oribtal of `x` under `f`.
-/

variable {α : Type*} [LinearOrder α]

/--
  The orbit of `x` under an automorphism `f`.
-/
def elem_orbit (f : α ≃o α) (x : α) :=
  MulAction.orbit (Subgroup.zpowers f) x

/--
  If `y` lies between powers of `x` under `f`,
  then `x` lies between powers of `x` under `f`.
-/
theorem swap_between {f : α ≃o α} {x y : α}
    (between : (∃l : ℤ, (f ^ l) x ≤ y) ∧ (∃u : ℤ, y ≤ (f ^ u) x)) :
    (∃l : ℤ, (f ^ l) y ≤ x) ∧ (∃u : ℤ, x ≤ (f ^ u) y) := by
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := between
  rw [show y = (f ^ (0 : ℤ)) y by simp] at hl hu
  constructor
  · exact above_pow_any_above hu 0
  · exact below_pow_any_below hl 0

/--
  `y` is in the orbit of `x` under `f` if and only if
  there exists an integer `z` such that `(f^z) x = y`.
-/
theorem mem_elem_orbit_iff (f : α ≃o α) (x y : α) :
    y ∈ elem_orbit f x ↔ ∃z : ℤ, (f^z) x = y := by
  simp [elem_orbit, MulAction.mem_orbit_iff, HSMul.hSMul, SMul.smul]

/--
  `x` is in the orbit of `x` under `f`.
-/
theorem reflexive_elem_orbit (f : α ≃o α) (x : α) : x ∈ elem_orbit f x := by
  rw [mem_elem_orbit_iff]
  use 0
  simp

/--
  If `f x = x`, then the orbit of `x` under `f`
  is `{x}`.
-/
theorem fix_orbit_eq {f : α ≃o α} {x : α} (fix : f x = x) :
    elem_orbit f x = {x} := by
  ext z
  constructor
  · intro h
    rw [mem_elem_orbit_iff] at h
    obtain ⟨m, hm⟩ := h
    rw [Set.mem_singleton_iff]
    have : (f ^ m) x = x := by
      exact fix_pow_fix fix m
    order
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact reflexive_elem_orbit f x

/--
  The orbital of `x` under an automorphism `f`.
-/
def elem_orbital (f : α ≃o α) (x : α) := (elem_orbit f x).ordClosure

/--
  The orbital of `x` under `f` is `OrdConnected`.
-/
theorem elem_orbital_ordConnected (f : α ≃o α) (x : α) :
    (elem_orbital f x).OrdConnected := by
  rw [elem_orbital]
  exact ordConnected_ordClosure (elem_orbit f x)

/--
  The orbit of `x` under `f` is a subset of the
  orbital of `x` under `f`.
-/
theorem elem_orbit_subset_elem_orbital (f : α ≃o α) (x : α) :
    elem_orbit f x ⊆ elem_orbital f x := by
  simp [elem_orbit, elem_orbital, subset_ordClosure]

/--
  `y` is in the orbital of `x` under `f` if and only if
  there exists integers `l` and `u` such that
  `(f^l) x ≤ y` and `y ≤ (f^u) x`.
-/
theorem mem_elem_orbital_iff (f : α ≃o α) (x y : α) :
    y ∈ elem_orbital f x ↔ (∃l : ℤ, (f^l) x ≤ y) ∧ (∃u : ℤ, y ≤ (f^u) x) := by
  constructor
  <;> simp [elem_orbital, mem_ordClosure, mem_elem_orbit_iff]

/--
  If `f` is increasing at `x` and `y` is
  upper and lower bounded by powers of `x` under `f`,
  then there exists an integer `z` such that
  `(f ^ z) x ≤ y` and `y < (f ^ (z+1)) x`.
-/
theorem incr_mem_elem_orbital_strong {f : α ≃o α} {x y : α}
    (incr : isIncreasingAt f x) {l u : ℤ} (hl : (f ^ l) x ≤ y)
    (hu : y ≤ (f ^ u) x) : ∃z : ℤ, (f ^ z) x ≤ y ∧ y < (f ^ (z + 1)) x := by
  have small_exp_bdd : ∃u : ℤ, ∀z : ℤ, (f ^ z) x ≤ y → z ≤ u := by
    use u
    intro z hz
    exact incr_ge_pow_ge incr (by order)
  obtain ⟨m, ⟨m_le_y, hm⟩⟩ :=
    Int.exists_greatest_of_bdd small_exp_bdd (by use l)
  use m
  constructor
  · trivial
  · by_contra! h
    have := hm (m+1) h
    omega

/--
  If `f` is decreasing at `x` and `y` is
  upper and lower bounded by powers of `x` under `f`,
  then there exists an integer `z` such that
  `(f ^ (z+1)) x ≤ y` and `y < (f ^ z) x`.
-/
theorem decr_mem_elem_orbital_strong {f : α ≃o α} {x y : α}
    (decr : isDecreasingAt f x) {l u : ℤ} (hl : (f ^ l) x ≤ y)
    (hu : y ≤ (f ^ u) x) : ∃z : ℤ, (f ^ (z + 1)) x ≤ y ∧ y < (f ^ z) x := by
  have small_exp_bdd : ∃u : ℤ, ∀z : ℤ, (f ^ z) x ≤ y → u ≤ z := by
    use u
    intro z hz
    exact decr_ge_pow_ge decr (by order)
  obtain ⟨m, ⟨m_le_y, hm⟩⟩ :=
    Int.exists_least_of_bdd small_exp_bdd (by use l)
  use (m-1)
  constructor
  · simp [m_le_y]
  · by_contra!
    have := hm (m-1) this
    omega

/--
  If `y` is in the orbital of `x` under `f`,
  then either `f x = y` or there is an integer `z`
  such that `y` is between `f ^ z` and `f ^ (z+1)`.
-/
theorem mem_elem_orbital_mp_strong (f : α ≃o α) (x y : α) :
    y ∈ elem_orbital f x →
      (f x = y) ∨ (∃z : ℤ, (f ^ z) x ≤ y ∧ y < (f ^ (z + 1)) x) ∨
      (∃z : ℤ, (f ^ (z+1)) x ≤ y ∧ y < (f ^ z) x) := by
  rw [mem_elem_orbital_iff]
  intro between
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := between
  by_cases h : x < f x
  · right; left
    exact incr_mem_elem_orbital_strong h hl hu
  simp only [not_lt] at h
  obtain eq | lt := h.eq_or_lt
  · left
    rw [fixed_all_pow_eq eq] at hl hu
    rw [eq]
    order
  · right; right
    exact decr_mem_elem_orbital_strong lt hl hu

/--
  If `f x = y` or there is an integer `z` such that
  `y` is between `f ^ z` and `f ^ (z+1)`, then
  `y` is in the orbital of `x` under `f`.
-/
theorem mem_elem_orbital_mpr_strong (f : α ≃o α) (x y : α) :
    (f x = y) ∨ (∃z : ℤ, (f ^ z) x ≤ y ∧ y < (f ^ (z + 1)) x) ∨
    (∃z : ℤ, (f ^ (z+1)) x ≤ y ∧ y < (f ^ z) x) → y ∈ elem_orbital f x := by
  intro h
  rw [mem_elem_orbital_iff]
  obtain fixed | incr | decr := h
  · constructor
    <;> (use 1; simp [fixed])
  · obtain ⟨z, ⟨hz, hz1⟩⟩ := incr
    constructor
    · use z
    · use (z+1)
      exact hz1.le
  · obtain ⟨z, ⟨hz1, hz⟩⟩ := decr
    constructor
    · use (z+1)
    · use z
      exact hz.le

/--
  `y` is in the orbital of `x` under `f` if and only if
  either `f x = y` or there is an integer `z` such that
  `y` is between `f ^ z` and `f ^ (z+1)`.
-/
theorem mem_elem_orbital_strong_iff (f : α ≃o α) (x y : α) :
    y ∈ elem_orbital f x ↔
      (f x = y) ∨ (∃z : ℤ, (f ^ z) x ≤ y ∧ y < (f ^ (z + 1)) x) ∨
      (∃z : ℤ, (f ^ (z+1)) x ≤ y ∧ y < (f ^ z) x) := by
  constructor
  · exact fun a ↦ mem_elem_orbital_mp_strong f x y a
  · exact fun a ↦ mem_elem_orbital_mpr_strong f x y a

/--
  `x` is in the orbital of `x` under `f`.
-/
theorem mem_elem_orbital_reflexive (f : α ≃o α) (x : α) :
    x ∈ elem_orbital f x := by
  rw [mem_elem_orbital_iff]
  constructor
  <;> (use 0; simp)

/--
  If `y` is in the orbital of `x` under `f`,
  then `x` is in the orbital of `y` under `f`.
-/
theorem mem_elem_orbital_symmetric {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) : x ∈ elem_orbital f y := by
  simp only [mem_elem_orbital_iff] at y_mem ⊢
  exact swap_between y_mem

/--
  If `x` is in the orbital of `y` under `f`
  and `y` is in the orbital of `z` under `f`,
  then `x` is in the orbital of `z` under `f`.
-/
theorem mem_elem_orbital_transitive {f : α ≃o α} {x y z : α}
    (hxy : x ∈ elem_orbital f y) (hyz : y ∈ elem_orbital f z) :
    x ∈ elem_orbital f z := by
  rw [mem_elem_orbital_iff] at hxy hyz ⊢
  obtain ⟨⟨ly, hly⟩, ⟨uy, huy⟩⟩ := hxy
  obtain ⟨⟨lz, hlz⟩, ⟨uz, huz⟩⟩ := hyz
  constructor
  · use (ly + lz)
    calc (f ^ (ly + lz)) z
    _ = (f ^ ly) ((f ^ lz) z) := by rw [←add_pows]
    _ ≤ (f ^ ly) y := by simp [hlz]
    _ ≤ x := by simp [hly]
  · use (uy + uz)
    calc x
    _ ≤ (f ^ uy) y := by simp [huy]
    _ ≤ (f ^ uy) ((f ^ uz) z) := by simp [huz]
    _ = (f ^ (uy + uz)) z := by simp [add_pows]

/--
  If `y` is in the orbital of `x` under `f`
  and `z` is in the orbit of `x` under `f`,
  then `z` is lower and upper bounded by
  powers of `y`.
-/
theorem mem_elem_orbital_orbit_between {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) {z : α} (z_mem_orbit : z ∈ elem_orbit f x) :
    (∃l : ℤ, (f ^ l) y ≤ z) ∧ (∃u : ℤ, z ≤ (f ^ u) y) := by
  rw [mem_elem_orbit_iff] at z_mem_orbit
  simp only [mem_elem_orbital_iff] at y_mem
  obtain ⟨m, f_pow_m_eq_z⟩ := z_mem_orbit
  rw [show y = (f ^ (0 : ℤ)) y by simp] at y_mem
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · convert above_pow_any_above hu m
    exact f_pow_m_eq_z.symm
  · convert below_pow_any_below hl m
    exact f_pow_m_eq_z.symm

/--
  If `y` is in the orbital of `x` under `f`,
  then the orbital of `y` under `f` is equal to the
  orbital of `x` under `f`.
-/
theorem mem_elem_orbital_eq {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) : elem_orbital f y = elem_orbital f x := by
  apply ordClosure_eq_ordClosure
  <;> intro z z_mem_orbit
  <;> simp only [mem_elem_orbit_iff, exists_exists_eq_and]
  · exact mem_elem_orbital_orbit_between y_mem z_mem_orbit
  · apply mem_elem_orbital_symmetric at y_mem
    exact mem_elem_orbital_orbit_between y_mem z_mem_orbit

/--
  If `y` is in the orbital of `x` under `f`,
  then, for any integer `z`, `(f^z) y` is in
  the oribtal of `x` under `f`.
-/
theorem pow_mem_elem_orbital {f : α ≃o α} {x y : α} (z : ℤ)
    (y_mem : y ∈ elem_orbital f x) : (f ^ z) y ∈ elem_orbital f x := by
  simp only [mem_elem_orbital_iff] at y_mem ⊢
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use (z + l)
    simp [←add_pows, hl]
  · use (z + u)
    simp [←add_pows, hu]

/--
  If `y` is in the orbital of `x` under `f`,
  then `f y` is in the orbital of `x` under `f`.
-/
theorem pow_mem_elem_orbital_one {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) : f y ∈ elem_orbital f x := by
  rw [show f = f ^ 1 by simp]
  exact pow_mem_elem_orbital 1 y_mem

/--
  If `f x = x`, then the orbital of `x` under `f`
  is `{x}`.
-/
theorem fix_orbital_eq {f : α ≃o α} {x : α}
    (fix : f x = x) : elem_orbital f x = {x} := by
  rw [elem_orbital, fix_orbit_eq fix]
  exact ordClosure_of_ordConnected Set.ordConnected_singleton

/--
  If `f x ≠ x`, then the orbital of `x` under `f`
  is not `{x}`.
-/
theorem not_fix_orbital_not_singleton {f : α ≃o α} {x : α}
    (not_fix : f x ≠ x) : elem_orbital f x ≠ {x} := by
  intro orbital_singleton
  have : f x ∈ elem_orbital f x :=
    pow_mem_elem_orbital_one (mem_elem_orbital_reflexive f x)
  simp only [orbital_singleton, Set.mem_singleton_iff] at this
  contradiction

/--
  `f x = x` if and only if
  the orbital of `x` under `f` is `{x}`.
-/
theorem fix_iff_singleton_orbital {f : α ≃o α} {x : α} :
    f x = x ↔ elem_orbital f x = {x} := by
  constructor
  · exact fun a ↦ fix_orbital_eq a
  · simpa using not_fix_orbital_not_singleton.mt

/--
  If `y` is in the orbital of `x` under `f`
  and `f y = y`, then `x = y`.
-/
theorem fix_mem_orbital_eq {f : α ≃o α} {x y : α}
    (y_mem : y ∈ elem_orbital f x) (fix : f y = y) : x = y := by
  have x_mem := mem_elem_orbital_symmetric y_mem
  simp only [fix_orbital_eq fix, Set.mem_singleton_iff] at x_mem
  trivial

/--
  If the orbital of `x` under `f` is `{y}`,
  then it is `{x}`.
-/
theorem singleton_orbital_swap {f : α ≃o α} {x y : α}
    (singleton_orbital : elem_orbital f x = {y}) : elem_orbital f x = {x} := by
  have : x ∈ elem_orbital f x := mem_elem_orbital_reflexive f x
  simp only [singleton_orbital, Set.mem_singleton_iff] at this
  subst_vars
  trivial

/--
  If the orbital of `x` under `f` is not `{x}`, then for any
  element `y`, the orbital of `x` under `f` is not `{y}`.
-/
theorem not_singleton_at_not_singleton_all {f : α ≃o α} {x : α}
    (not_single : elem_orbital f x ≠ {x}) (y : α) :
    elem_orbital f x ≠ {y} := by
  intro h
  absurd not_single
  exact singleton_orbital_swap h

/--
  If the orbital of `x` under `f` is not equal
  to the orbital of `y` under `f`, then `x`
  is not in the orbital of `y` under `f`.
-/
theorem neq_orbitals_not_mem_orbital {f : α ≃o α} {x y : α}
    (neq_orbitals : elem_orbital f x ≠ elem_orbital f y) :
    x ∉ elem_orbital f y := by
  intro hx
  exact (neq_orbitals (mem_elem_orbital_eq hx)).elim
