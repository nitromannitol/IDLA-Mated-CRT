import MatedCRT.FirstPass.Derived.AreaCellDiameter

/-! # Eventual smallness of the cells meeting a bounded set

For a continuous curve `η` with `η(t) → ∞` as `|t| → ∞` and mesh parameters `ε n → 0`, every cell
`η([ε n (k-1), ε n k])` meeting a fixed bounded set has diameter at most `d` for all large `n`
(uniform continuity of `η` on a compact time interval). For an area parametrized curve this is
the mesh bound on the cells of `areaCellConfig` needed by the shifted area-cell transfers. -/
set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric ReflectedGMS.GMS

/-- For a continuous proper curve and mesh parameters tending to `0`, eventually all cells
meeting a bounded set have diameter at most `d`. -/
theorem eventually_diam_cell_le_of_cellVertices {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {B : Set ℂ} (hB : Bornology.IsBounded B)
    {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n in atTop, ∀ k ∈ cellVertices (ε n) η B, Metric.diam (cell (ε n) η k) ≤ d := by
  have hpre : IsCompact (η ⁻¹' closure B) :=
    (isProperMap_iff_tendsto_cocompact.mpr ⟨hη, hp⟩).isCompact_preimage hB.isCompact_closure
  obtain ⟨T, hT⟩ := hpre.isBounded.subset_closedBall 0
  have huc := (isCompact_Icc (a := -(T + 1)) (b := T + 1)).uniformContinuousOn_of_continuous
    hη.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (d / 2) (half_pos hd)
  have hev : ∀ᶠ n in atTop, ε n < min δ 1 :=
    hε0.eventually (gt_mem_nhds (lt_min hδ one_pos))
  filter_upwards [hev] with n hn
  intro k hk
  obtain ⟨z, hzc, hzB⟩ := hk
  obtain ⟨s, hs, rfl⟩ := hzc
  have hsT : |s| ≤ T := by
    have h := hT (show s ∈ η ⁻¹' closure B from subset_closure hzB)
    rwa [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
  have hεn : ε n < δ := lt_of_lt_of_le hn (min_le_left _ _)
  have hε1 : ε n < 1 := lt_of_lt_of_le hn (min_le_right _ _)
  have hlen : ∀ s' ∈ Icc (ε n * ((k : ℝ) - 1)) (ε n * k), ∀ s'' ∈ Icc (ε n * ((k : ℝ) - 1)) (ε n * k),
      |s' - s''| ≤ ε n := by
    intro s' hs' s'' hs''
    have hk1 : ε n * ((k : ℝ) - 1) = ε n * k - ε n := by ring
    rw [abs_le]
    constructor <;> linarith [hs'.1, hs'.2, hs''.1, hs''.2]
  have hmem : ∀ s' ∈ Icc (ε n * ((k : ℝ) - 1)) (ε n * k), s' ∈ Icc (-(T + 1)) (T + 1) := by
    intro s' hs'
    have h1 := hlen s' hs' s hs
    rw [abs_le] at h1 hsT
    constructor <;> linarith [h1.1, h1.2, hsT.1, hsT.2]
  refine Metric.diam_le_of_forall_dist_le hd.le ?_
  rintro _ ⟨s1, hs1, rfl⟩ _ ⟨s2, hs2, rfl⟩
  have hd12 : dist s1 s2 < δ := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hlen s1 hs1 s2 hs2) hεn
  have := hδ' s1 (hmem s1 hs1) s2 (hmem s2 hs2) hd12
  linarith

/-- For an area parametrized proper curve and mesh parameters tending to `0`, eventually every
cell of `areaCellConfig` meeting a bounded set of the plane has diameter at most `d`. -/
theorem eventually_areaCellConfig_diam_le_of_meeting {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (m : ℕ → ℤ → ℤ → ℕ) {U : Set ReflectedGMS.Plane} (hU : Bornology.IsBounded U)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n in atTop, ∀ K : (areaCellConfig h (hε n) (m n)).cells,
      ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty →
        Metric.diam (K.1 : Set ReflectedGMS.Plane) ≤ d := by
  have hB : Bornology.IsBounded (Complex.orthonormalBasisOneI.repr ⁻¹' U) :=
    Complex.orthonormalBasisOneI.repr.isometry.antilipschitzWith.isBounded_preimage hU
  filter_upwards [eventually_diam_cell_le_of_cellVertices h.1 hp hB hε0 hd] with n hn
  exact areaCellConfig_diam_le_of_meeting h (hε n) (m n) U d hn

end MatedCRT
