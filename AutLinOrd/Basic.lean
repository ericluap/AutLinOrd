import Mathlib
import AutLinOrd.OrdClosure
import AutLinOrd.MulAction
import AutLinOrd.Pow
import AutLinOrd.IncrDecr

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
  The orbital of `x` under an automorphism `f`.
-/
def elem_orbital (f : α ≃o α) (x : α) := (elem_orbit f x).ordClosure

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

theorem incr_mem_elem_orbital_iff_strong {f : α ≃o α} {x y : α}
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

theorem decr_mem_elem_orbital_iff_strong {f : α ≃o α} {x y : α}
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

theorem mem_elem_orbital_mp_strong (f : α ≃o α) (x y : α) :
    y ∈ elem_orbital f x →
      (f x = y) ∨ (∃z : ℤ, (f ^ z) x ≤ y ∧ y < (f ^ (z + 1)) x) ∨
      (∃z : ℤ, (f ^ (z+1)) x ≤ y ∧ y < (f ^ z) x) := by
  rw [mem_elem_orbital_iff]
  intro between
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := between
  by_cases h : x < f x
  · right; left
    exact incr_mem_elem_orbital_iff_strong h hl hu
  simp only [not_lt] at h
  obtain eq | lt := h.eq_or_lt
  · left
    rw [fixed_all_pow_eq eq] at hl hu
    rw [eq]
    order
  · right; right
    exact decr_mem_elem_orbital_iff_strong lt hl hu

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
theorem mem_elem_orbital_symmetric (f : α ≃o α) (x y : α)
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
theorem pow_mem_elem_orbital (f : α ≃o α) (x y : α) (z : ℤ)
    (y_mem : y ∈ elem_orbital f x) : (f ^ z) y ∈ elem_orbital f x := by
  simp only [mem_elem_orbital_iff] at y_mem ⊢
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use (z + l)
    simp [←add_pows, hl]
  · use (z + u)
    simp [←add_pows, hu]

theorem incr_at_incr_all {f : α ≃o α} {x y : α}
    (incr : isIncreasingAt f x) (y_mem : y ∈ elem_orbital f x) :
    isIncreasingAt f y := by
  sorry

/--
  The set of all non-singleton orbitals of `f`.
-/
def orbitals (f : α ≃o α) :=
  {z : Set α | ∃x : α, elem_orbital f x = z ∧ ¬∃z : α, elem_orbital f x = {z}}

/--
  An automorphism `f` is a bump if it only has
  a single orbital (that is not a singleton).
-/
def isBump (f : α ≃o α) := (orbitals f).ncard = 1

/--
  If `f` is a bump, then it has an orbital.
-/
theorem exists_orbital {f : α ≃o α} (is_bump : isBump f) :
    ∃x : Set α, x ∈ orbitals f := by
  rw [isBump, Set.ncard_eq_one] at is_bump
  obtain ⟨x, hx⟩ := is_bump
  use x
  simp [hx]

open Classical in
/--
  The orbital of a bump `f`.
  (If `f` is not a bump, then it returns junk)
-/
def orbital (f : α ≃o α) :=
  if h : ∃x, x ∈ orbitals f then
    h.choose
  else
    ∅

theorem mem_orbital_iff {f : α ≃o α} {x : α} :
    x ∈ orbital f ↔ ∃y, y ∈ orbital f ∧ x ∈ elem_orbital f y := by
  constructor
  · intro x_mem
    use x
    exact ⟨x_mem, mem_elem_orbital_reflexive f x⟩
  · intro exists_elem
    by_cases h : ∃ x, x ∈ orbitals f
    · simp [orbital, h] at exists_elem ⊢
      obtain ⟨y, ⟨hy, hx⟩⟩ := exists_elem
      obtain ⟨g, ⟨hg, not_singleton⟩⟩ := h.choose_spec.out
      rw [←hg] at hy ⊢
      exact mem_elem_orbital_transitive hx hy
    · obtain ⟨y, hy, _⟩ := exists_elem
      simp [orbital, h] at hy

theorem elem_in_orbital {f : α ≃o α} {x : α} (x_mem : x ∈ orbital f) : f x ∈ orbital f := by
  rw [mem_orbital_iff, mem_elem_orbital_mp_strong]

abbrev leftBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, x < y
abbrev rightBoundedOrbital (f : α ≃o α) := ∃x, ∀y ∈ orbital f, y < x

/--
  A bounded bump is a bump whose
  only orbital is bounded to the left or right.
-/
def isBoundedBump (f : α ≃o α) :=
  isBump f ∧ (leftBoundedOrbital f ∨ rightBoundedOrbital f)

/--
  Two points are related by `bubbleR` if they
  are both in the orbital of a bounded bump.
-/
abbrev bubbleR (x y : α) :=
  (∃f : α ≃o α, isBoundedBump f ∧ x ∈ orbital f ∧ y ∈ orbital f) ∨ x = y

/--
  The `bubbleR` relation is reflexive.
-/
theorem reflexive_bubbleR (x : α) : bubbleR x x := by
  simp [bubbleR]

/--
  The `bubbleR` relation is symmetric.
-/
theorem symmetric_bubbleR {x y : α} : bubbleR x y → bubbleR y x := by
  simp [bubbleR, And.comm, eq_comm]

def isIncreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, x < f x
def isDecreasingOnOrbitl (f : α ≃o α) := ∀x ∈ orbital f, f x < x

def isNotDecreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, x ≤ f x
def isNotIncreasingOnOrbital (f : α ≃o α) := ∀x ∈ orbital f, f x ≤ x

theorem combine_bumps {f g : α ≃o α}
    (hf : isBump f) (hg : isBump g) (inter : ∃x, x ∈ orbital f ∩ orbital g) :
    ∃h : α ≃o α, isBump h ∧ orbital h = orbital f ∪ orbital g := by
  sorry

/--
  The `bubbleR` relation is transitive.
-/
theorem transitive_bubbleR {x y z : α} :
    bubbleR x y → bubbleR y z → bubbleR x z := by
  intro hxy hyz
  have hxy' := hxy
  have hyz' := hyz
  obtain ⟨f, f_boundedbump, x_in_f_orbital, y_in_f_orbital⟩ | rfl := hxy
  <;> obtain ⟨g, g_boundedbump, y_in_g_orbital, z_in_g_orbital⟩ | rfl := hyz
  · sorry
  · exact hxy'
  · exact hyz'
  · exact hxy'
