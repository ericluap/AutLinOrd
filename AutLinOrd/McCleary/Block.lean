import AutLinOrd.McCleary.Basic
open MulAction
open Pointwise

/-! # Block
  In this file we define what an extensive o-block is and
  prove basic theorems about it.
-/

variable [LinearOrder S] (G : Subgroup (S ≃o S))

/-- `B` is an o-block if it is a convex block. -/
def IsOBlock (B : Set S) := B.OrdConnected ∧ IsBlock G B

/-- The block orbit of `b` in a block `B` is its orbit
  restricted to the block `B`.
-/
def blockOrbit {B : Set S} (b : B) := MulAction.orbit G b.val ∩ B
theorem blockOrbit_iff {B : Set S} (b : B) :
  blockOrbit G b = MulAction.orbit G b.val ∩ B := by rfl

/-- If for some `b ∈ B` we have that `gb ∈ B`,
  then for any `z`, `g^z B = B`. -/
theorem mem_block_pow_fixed {g : G} {B : Set S} {b : B}
    (is_block : IsBlock G B) (mem_block : g • b.val ∈ B) (z : ℤ) :
    g ^ z • B = B := by
  induction z with
  | zero => simp
  | succ n ih =>
    norm_cast at ⊢ ih
    simp [add_comm n, pow_add, mul_smul, ih,
      IsBlock.smul_eq_of_mem is_block b.prop mem_block]
  | pred n ih =>
    simp only [sub_eq_add_neg, add_comm (-n : ℤ), zpow_add, mul_smul, ih]
    conv_lhs => rw [←IsBlock.smul_eq_of_mem is_block b.prop mem_block]
    simp

/-- If for some `b ∈ B` we have that `gb ∈ B`,
  then for any `n`, `g^n b ∈ B`. -/
theorem mem_block_power_mem_block {g : G} {B : Set S} {b : B}
    (is_block : IsBlock G B) (mem_block : g • b.val ∈ B) (z : ℤ) :
    g ^ z • b.val ∈ B := by
  simp +singlePass only [← (mem_block_pow_fixed G is_block mem_block z),
    Set.smul_mem_smul_set_iff]
  simp

/-- The block orbit of `b` in block `B` is a subset of `B`. -/
theorem blockOrbit_subset_block {B : Set S} (b : B) :
  blockOrbit G b ⊆ B := by simp [blockOrbit_iff]

/-- A block `B` is extensive if for any element of it `b`,
  the block orbit of `b` is cofinal and coinitial.
-/
def IsExtensive (B : Set S) := ∃b : B,
  IsCofinalFor B (blockOrbit G b) ∧ IsCoinitialFor B (blockOrbit G b)
theorem isExtensive_iff : IsExtensive G B ↔
  ∃b : B, IsCofinalFor B (blockOrbit G b) ∧ IsCoinitialFor B (blockOrbit G b) := by rfl

/-- The block orbit of `b` in `B` is cofinal in `B` if and only if
  for every `b'` in `B`, there exists a `g` such that `b' ≤ gb`
  and `gb` is in `B`. -/
theorem isCofinalForBlockOrbit_iff {B : Set S} (b : B) :
    IsCofinalFor B (blockOrbit G b) ↔
    ∀b' : B, ∃g : G, b' ≤ g • b.val ∧ g • b.val ∈ B := by
  constructor
  · intro is_cofinal c
    obtain ⟨gs, ⟨⟨gs_mem_orbit, gs_mem_B⟩, c_le_gs⟩⟩ := is_cofinal c.prop
    simp only [mem_orbit_iff, Subtype.exists, Subgroup.mk_smul, RelIso.smul_def,
      exists_prop] at gs_mem_orbit
    obtain ⟨g, ⟨g_mem_G, rfl⟩⟩ := gs_mem_orbit
    use ⟨g, g_mem_G⟩
    simp [c_le_gs, gs_mem_B]
  · intro h s s_mem_b
    obtain ⟨g, hg⟩ := h ⟨s, s_mem_b⟩
    use (g • b)
    simp [blockOrbit_iff, hg]

/-- The block orbit of `b` in `B` is coinitial in `B` if and only if
  for every `b'` in `B`, there exists a `g` such that `gb ≤ b'`
  and `gb` is in `B`. -/
theorem isCoinitialForBlockOrbit_iff {B : Set S} (b : B) :
    IsCoinitialFor B (blockOrbit G b) ↔
    ∀b' : B, ∃g : G, g • b.val ≤ b' ∧ g • b.val ∈ B := by
  constructor
  · intro is_cofinal c
    obtain ⟨gs, ⟨⟨gs_mem_orbit, gs_mem_B⟩, c_le_gs⟩⟩ := is_cofinal c.prop
    simp only [mem_orbit_iff, Subtype.exists, Subgroup.mk_smul, RelIso.smul_def,
      exists_prop] at gs_mem_orbit
    obtain ⟨g, ⟨g_mem_G, rfl⟩⟩ := gs_mem_orbit
    use ⟨g, g_mem_G⟩
    simp [c_le_gs, gs_mem_B]
  · intro h s s_mem_b
    obtain ⟨g, hg⟩ := h ⟨s, s_mem_b⟩
    use (g • b)
    simp [blockOrbit_iff, hg]

/-- Every singleton is a block. -/
theorem singleton_block (b : S) : IsBlock G {b} := by simp [IsBlock]
/-- Every singleton is an o-block. -/
theorem singleton_oblock (b : S) : IsOBlock G {b} := by
  simp [IsOBlock, singleton_block, Set.ordConnected_singleton]
/-- Every singleton is extensive. -/
theorem singleton_extensive (b : S) : IsExtensive G {b} := by
  simp [isExtensive_iff, blockOrbit_iff]

/-- If `s < g • s`, then `g • s < g^2 • s`. -/
theorem lt_squared_smul_of_lt {g : G} {s : S} (lt : s < g • s) :
    g • s < g^2 • s := by
  simp only [(show g ^ 2 = g ^ (1 + 1) by simp), Nat.reduceAdd]
  simp only [pow_add, mul_smul, pow_one]
  unfold_projs
  simpa

/-- If `B` is an extensive block that is nontrivial,
  it has no largest element.  -/
theorem no_top_of_not_singleton_extensive {B : Set S}
    (is_block : IsBlock G B) (b_extensive : IsExtensive G B)
    (nontrivial : B.Nontrivial) : ∀b : B, ∃u : B, b < u := by
  -- We have two distinct elements of `B`.
  let c : B := ⟨nontrivial.choose.1, Set.Nontrivial.choose_fst_mem nontrivial⟩
  let d : B := ⟨nontrivial.choose.2, Set.Nontrivial.choose_snd_mem nontrivial⟩
  have c_ne_d : c ≠ d := by
    simp [Subtype.eq_iff]
    exact (Set.Nontrivial.choose_fst_ne_choose_snd nontrivial)

  intro b
  -- Since `B` is extensive, the block orbit of `b'` is cofinal and coinitial in `B`.
  obtain ⟨b', ⟨cofinal_b', coinitial_b'⟩⟩ := b_extensive
  /- Since `b'` is cofinal in `B`, there exists a `u ∈ B` such that
    `g · b' = u` and `b ≤ u`. -/
  obtain ⟨u, ⟨⟨⟨g, hg⟩, u_mem_B⟩, b_le_u⟩⟩ := cofinal_b' b.prop
--  obtain ⟨l, ⟨⟨⟨f, hf⟩, l_mem_B⟩, l_le_b⟩⟩ := coinitial_b' b.prop
  simp only at hg --hf

  obtain b'_lt_u | b'_eq_u | u_lt_b' := lt_trichotomy b' ⟨u, u_mem_B⟩
  -- If `g` is increasing, we use `g^2` to get something larger than `b`.
  · have : b'.val < g • b'.val := by
      have : b'.val < u := b'_lt_u
      simpa [←hg]
    have : u < g^2 • b' := by
      calc u
      _ = g • b' := hg.symm
      _ < g^2 • b' := lt_squared_smul_of_lt G this
    have g2B_eq_B : g^2 • B = B :=
      let smul_mem : g • b'.val ∈ B := Set.mem_of_eq_of_mem hg u_mem_B
      mem_block_pow_fixed G is_block smul_mem 2
    have g2b'_mem : g^2 • b'.val ∈ B := by
      simp +singlePass only [← g2B_eq_B, Set.smul_mem_smul_set_iff]
      simp
    use ⟨g^2 • b'.val, g2b'_mem⟩
    have : b.val < g^2 • b'.val := by order
    simpa
  -- If `g` does nothing, we need to use the distint points we have to
  -- create an increasing automorphism.
  ·
    obtain c_eq_b' | c_ne_b' := eq_or_ne c b'
    · /-
        If `d < b'`, I need a map `f` such that `f • b' ≤ d`
        and then `f⁻¹` is increasing at `b'`.
        If `b' < d`, I need a map `f` such that `d ≤ f • b'`
        and then `f` is increasing at `b'`.
      -/
      obtain d_lt_b' | d_eq_b' | b'_lt_d := lt_trichotomy d b'
      -- First, we look at the case where `d < b'`.
      · -- We have a map `f` such that `f • b' ≤ d`.
        have ⟨t, ⟨⟨⟨f, hf⟩, t_mem_B⟩, c_le_t⟩⟩ := coinitial_b' d.prop
        simp only at hf
        -- Therefore, `f` is decreasing.
        have : f • b'.val < b' := by
          have : d < b'.val := d_lt_b'
          order
        -- And so `f⁻¹` is increasing
        have finv_incr : b' < f⁻¹ • b'.val := by
          unfold_projs at ⊢ this
          simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
            RelIso.coe_toRelEmbedding] at ⊢ this
          exact (OrderIso.symm_apply_lt f⁻¹.val).mp this
        have finv_mem : f⁻¹ • b'.val ∈ B := by
          have : f⁻¹ • B = B := by
            have smul_mem : f • b'.val ∈ B := Set.mem_of_eq_of_mem hf t_mem_B
            exact mem_block_pow_fixed G is_block smul_mem (-1)
          simp +singlePass [←this]
        use ⟨f⁻¹ • b'.val, finv_mem⟩
        -- Which gives us that `b < f⁻¹ • b'`
        have : b.val < f⁻¹ • b'.val := by
          have : u = b'.val := by simp [b'_eq_u]
          order
        simpa
      -- Next, we look at the case where `d = b'`, this is impossible.
      · have d_ne_b' : d ≠ b' := by order
        exact (d_ne_b' d_eq_b').elim
      -- Lastly, wee look at the case where `b' < d`.
      · -- We have a map `f` such that `d ≤ f • b'`.
        have ⟨t, ⟨⟨⟨f, hf⟩, t_mem_B⟩, c_le_t⟩⟩ := cofinal_b' d.prop
        simp only at hf
        -- Therefore, `f` is increasing.
        have : b' < f • b'.val := by
          have : b' < d.val := b'_lt_d
          order
        have fb_mem_B : f • b'.val ∈ B := Set.mem_of_eq_of_mem hf t_mem_B
        use ⟨f • b'.val, fb_mem_B⟩
        have : b.val < f • b'.val := by
          have : u = b'.val := by simp [b'_eq_u]
          order
        simpa
    · sorry
  · sorry
