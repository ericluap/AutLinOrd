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

/--
  If `f` is increasing at `x` and `y` is
  upper and lower bounded by power of `x` under `f`,
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
  upper and lower bounded by power of `x` under `f`,
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
  If `f` is increasing at `x` and `y` is in the orbital of `x` under `f`,
  then `f` is increasing at `y`.
-/
theorem incr_at_incr_all {f : α ≃o α} {x y : α}
    (incr : isIncreasingAt f x) (y_mem : y ∈ elem_orbital f x) :
    isIncreasingAt f y := by
  rw [mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  · rw [isIncreasingAt] at incr ⊢
    subst_vars
    exact OrderIso.GCongr.orderIso_apply_lt_apply f incr
  · obtain ⟨z, hz, hz1⟩ := incr
    rw [isIncreasingAt]
    have : (f ^ (z + 1)) x ≤ f y := by simp [add_comm z, ←add_pows, hz]
    order
  · obtain ⟨z, hz1, hz⟩ := decr
    rw [isIncreasingAt] at incr
    have : (f ^ (z + 1)) x < (f ^ z) x := by order
    simp [←add_pows] at this
    order

/--
  `non_decr_at f x` is either `f` or `f⁻¹`
  in order to make `x ≤ (non_decr_at f x) x`.
-/
def non_decr_at (f : α ≃o α) (x : α) : α ≃o α :=
  if x ≤ f x then
    f
  else
    f⁻¹

/--
  Either `x ≤ f x` and `non_decr_at f x = f` or
  `f x < x` and `non_decr_at f x = f⁻¹`.
-/
theorem non_decr_at_def (f : α ≃o α) (x : α) :
    (x ≤ f x ∧ non_decr_at f x = f) ∨ (f x < x ∧ non_decr_at f x = f⁻¹) := by
  by_cases h : x ≤ f x
  · left
    constructor
    · trivial
    · simp only [non_decr_at, ite_eq_left_iff, not_le]
      order
  · right
    constructor
    · order
    · simp [non_decr_at, h]

/--
  We have that `non_decr_at f x` is not decreasing at `x`.
-/
theorem non_decr_at_non_decr (f : α ≃o α) (x : α) :
    ¬isDecreasingAt (non_decr_at f x) x := by
  obtain eq |inv := non_decr_at_def f x
  · simp [eq]
  · simp only [inv, gt_iff_lt, not_lt]
    exact ((map_inv_lt_iff f⁻¹).mp inv.1).le

/--
  The orbital of `x` under `f⁻¹` is a subset
  of the orbital of `x` under `f`.
-/
theorem inv_subset_elem_orbital (f : α ≃o α) (x : α) :
    elem_orbital f⁻¹ x ⊆ elem_orbital f x := by
  intro y y_mem
  rw [mem_elem_orbital_iff] at y_mem ⊢
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := y_mem
  constructor
  · use -l
    simpa using hl
  · use -u
    simpa using hu

/--
  The orbital of `x` under `f` is equal to the orbital
  of `x` under `f⁻¹`.
-/
theorem finv_elem_orbital_eq (f : α ≃o α) (x : α) :
    elem_orbital f x = elem_orbital f⁻¹ x := by
  apply Set.eq_of_subset_of_subset
  · exact inv_subset_elem_orbital f⁻¹ x
  · exact inv_subset_elem_orbital f x

/--
  The orbital of `x` under `f` is equal to the orbital
  of `x` under `non_decr_at f x`.
-/
theorem non_decr_eq_elem_orbital (f : α ≃o α) (x : α) :
    elem_orbital f x = elem_orbital (non_decr_at f x) x := by
  obtain eq | inv := non_decr_at_def f x
  · simp [eq]
  · simp [inv, ←finv_elem_orbital_eq]

/--
  Given automorphisms `f` and `g` and an element `x`,
  `combinat_at f g x` is an automorphism who orbital at
  `x` is the union of that of `f` and `g`.
-/
def combine_at (f g : α ≃o α) (x : α) : α ≃o α :=
  (non_decr_at f x).trans (non_decr_at g x)

/--
  `combine_at f g x` is not decreasing at `x`.
-/
theorem not_decr_combine_at (f g : α ≃o α) (x : α) :
    ¬isDecreasingAt (combine_at f g x) x := by
  simp [isDecreasingAt, combine_at]
  have f_incr := non_decr_at_non_decr f x
  have g_incr := non_decr_at_non_decr g x
  simp only [gt_iff_lt, not_lt] at f_incr g_incr
  have : (non_decr_at g x) x ≤ (non_decr_at g x) ((non_decr_at f x) x) :=
    OrderIso.GCongr.orderIso_apply_le_apply (non_decr_at g x) f_incr
  order

theorem combine_at_cases (f g : α ≃o α) (x : α) :
    (x ≤ f x ∧ x ≤ g x ∧ combine_at f g x = f.trans g) ∨
    (x ≤ f x ∧ g x < x ∧ combine_at f g x = f.trans g⁻¹) ∨
    (f x < x ∧ x ≤ g x ∧ combine_at f g x = f⁻¹.trans g) ∨
    (f x < x ∧ g x < x ∧ combine_at f g x = f⁻¹.trans g⁻¹) := by
  obtain ⟨le_f, eq_f⟩ | ⟨gt_f, inv_f⟩ := non_decr_at_def f x
  <;> obtain ⟨le_g, eq_g⟩ | ⟨gt_g, inv_g⟩ := non_decr_at_def g x
  <;> simp only [combine_at, *]
  <;> tauto

theorem first_in_combine_maps (f g : α ≃o α) (x y : α)
    (y_mem : y ∈ elem_orbital f x) : y ∈ elem_orbital (combine_at f g x) x := by
  rw [non_decr_eq_elem_orbital, mem_elem_orbital_strong_iff] at y_mem
  obtain fix | incr | decr := y_mem
  simp only [mem_elem_orbital_iff, combine_at]
  all_goals sorry

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

/--
  `x` is an element of the orbital of `f`
  if and only if the orbital of `f` is equal to
  the orbital of `x` under `f`.
-/
theorem mem_orbital_iff {f : α ≃o α} {x : α} :
    x ∈ orbital f ↔ orbital f = elem_orbital f x := by
  constructor
  · intro x_mem
    by_cases h : ∃x, x ∈ orbitals f
    · simp only [orbital, h, ↓reduceDIte] at x_mem ⊢
      have := h.choose_spec
      simp only [orbitals, not_exists, Set.mem_setOf_eq] at this x_mem ⊢
      obtain ⟨z, eq_elem_orbital, not_singleton⟩ := this
      simp [←eq_elem_orbital] at x_mem ⊢
      exact (mem_elem_orbital_eq x_mem).symm
    · simp [orbital, h] at x_mem
  · intro eq_orbital
    rw [eq_orbital]
    exact mem_elem_orbital_reflexive f x

theorem pow_mem_orbital {f : α ≃o α} {x : α} (x_mem : x ∈ orbital f) (z : ℤ) :
    (f ^ z) x ∈ orbital f := by
  rw [mem_orbital_iff] at x_mem
  rw [x_mem]
  exact pow_mem_elem_orbital z (mem_elem_orbital_reflexive f x)

theorem pow_mem_orbital_one {f : α ≃o α} {x : α} (x_mem : x ∈ orbital f) :
    f x ∈ orbital f := pow_mem_orbital x_mem 1

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
