import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactEvent

/-! # Locality of the `3/4`-clusters and of volume growth under restriction to `B_1` (closure of Proposition 4.2)

The raw `3/4`-clusters of a measure `ν` depend only on `ν|_{B_1}`: the supersolutions on `B_{3/4}` test the Laplacian
only against test functions supported in `B_{3/4} ⊆ B_1` (`LaplacianLE`), and the Green function does not involve `ν`.
This is the locality input for passing the premature-contact event through the restricted laws of fact (2)
(IDLA eq. (2.4) on `B_1`). Volume growth at radius `3/4` is also preserved by the restriction (balls of radius `< 1/4`
centred in `B_{3/4}` lie in `B_1`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- `LaplacianLE` on an open set `U ⊆ B_1` depends on the measure only through `B_1`: a test function supported in `U`
vanishes off `B_1`, so its integral against `μ` and against `μ|_{B_1}` agree, and it is integrable for one iff for the
other. -/
theorem laplacianLE_restrict_ball_one {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ} (hU : U ⊆ ball (0 : ℂ) 1) :
    LaplacianLE w (μ.restrict (ball (0 : ℂ) 1)) U ↔ LaplacianLE w μ U := by
  have hvan : ∀ φ : ℂ → ℝ, IsTestFunction U φ → ∀ x, x ∉ ball (0 : ℂ) 1 → φ x = 0 := by
    intro φ hφ x hx
    by_contra hne
    exact hx (hU (hφ.2.2 (subset_tsupport φ (Function.mem_support.mpr hne))))
  have hint : ∀ φ : ℂ → ℝ, IsTestFunction U φ →
      (Integrable φ (μ.restrict (ball (0 : ℂ) 1)) ↔ Integrable φ μ) := by
    intro φ hφ
    have hind : (ball (0 : ℂ) 1).indicator φ = φ := by
      funext x
      by_cases hx : x ∈ ball (0 : ℂ) 1
      · simp [hx]
      · simp [hx, hvan φ hφ x hx]
    constructor
    · intro h
      have h' : Integrable ((ball (0 : ℂ) 1).indicator φ) μ :=
        (integrable_indicator_iff measurableSet_ball).mpr h
      rwa [hind] at h'
    · intro h
      exact h.integrableOn
  have hsum : ∀ φ : ℂ → ℝ, IsTestFunction U φ →
      ∫ x, φ x ∂(μ.restrict (ball (0 : ℂ) 1)) = ∫ x, φ x ∂μ := fun φ hφ =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hvan φ hφ x hx
  unfold LaplacianLE
  constructor
  · rintro ⟨hloc, h⟩
    refine ⟨hloc, fun φ hφ hpos hint' => ?_⟩
    rw [← hsum φ hφ]
    exact h φ hφ hpos ((hint φ hφ).mpr hint')
  · rintro ⟨hloc, h⟩
    refine ⟨hloc, fun φ hφ hpos hint' => ?_⟩
    rw [hsum φ hφ]
    exact h φ hφ hpos ((hint φ hφ).mp hint')

/-- The supersolutions of the `3/4`-cluster depend only on the restriction to `B_1`. -/
theorem supersolutions_three_quarter_restrict (μ : Measure ℂ) (z : ℂ) (t : ℝ) :
    supersolutions (μ.restrict (ball (0 : ℂ) 1)) (3 / 4) z t = supersolutions μ (3 / 4) z t := by
  have hU : ball (0 : ℂ) (3 / 4) ⊆ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num)
  unfold supersolutions
  ext w
  simp only [mem_ofPred_eq, laplacianLE_restrict_ball_one hU]

/-- **Locality of the `3/4`-cluster.** The raw cluster `cluster ν (3/4) z t` of a measure equals the cluster of its
restriction to `B_1`. -/
theorem cluster_three_quarter_restrict (μ : Measure ℂ) (z : ℂ) (t : ℝ) :
    cluster (μ.restrict (ball (0 : ℂ) 1)) (3 / 4) z t = cluster μ (3 / 4) z t := by
  unfold cluster leastSupersolution
  rw [supersolutions_three_quarter_restrict]

/-- The premature half-ball contact of the raw `3/4`-clusters depends only on the restriction to `B_1`. -/
theorem halfBallPrematureContact_restrict_iff (μ : Measure ℂ) :
    halfBallPrematureContact (fun t : Ioi (0 : ℝ) =>
        interior (closure (cluster (μ.restrict (ball (0 : ℂ) 1)) (3 / 4) 0 t))) ↔
      halfBallPrematureContact (fun t : Ioi (0 : ℝ) => interior (closure (cluster μ (3 / 4) 0 t))) := by
  simp only [cluster_three_quarter_restrict]

/-- Volume growth at radius `3/4` passes to the restriction to `B_1`. -/
theorem volumeGrowth_restrict_ball_one {μ : Measure ℂ} {βm βp : ℝ} (hV : VolumeGrowth μ (3 / 4) βm βp) :
    VolumeGrowth (μ.restrict (ball (0 : ℂ) 1)) (3 / 4) βm βp := by
  obtain ⟨hm, hp, r₀, hr₀, hbd⟩ := hV
  refine ⟨hm, hp, min r₀ (1 / 4), lt_min hr₀ (by norm_num), fun r hr hrlt z hz => ?_⟩
  have hr₁ : r < r₀ := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hr₂ : r < 1 / 4 := lt_of_lt_of_le hrlt (min_le_right _ _)
  have hsub : ball z r ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    have h1 : dist w z < r := hw
    have h2 : dist z 0 < 3 / 4 := hz
    rw [mem_ball]
    calc dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ < r + 3 / 4 := add_lt_add h1 h2
      _ < 1 := by linarith
  rw [Measure.restrict_apply measurableSet_ball, Set.inter_eq_left.mpr hsub]
  exact hbd r hr hr₁ z hz

/-- The restriction of a locally finite measure to `B_1` is locally finite. -/
theorem isLocallyFiniteMeasure_restrict_ball_one (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.restrict (ball (0 : ℂ) 1)) :=
  inferInstance

end MatedCRT
