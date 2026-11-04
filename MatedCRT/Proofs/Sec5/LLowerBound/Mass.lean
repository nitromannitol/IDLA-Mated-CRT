import MatedCRT.Proofs.Sec5.LLowerBound.Geometry

/-!
# Positive local LQG mass

An area-parametrized continuous space-filling curve forces the associated
measure to charge every nonempty open set.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- A measure that parametrizes a continuous surjection has full support. -/
theorem open_pos_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) : μ.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨z, hz⟩ := hne
  obtain ⟨t, rfl⟩ := hη.2.2.1 z
  have hopen : IsOpen (η ⁻¹' U) := hU.preimage hη.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen t hz
  have hsub : η '' Icc (t - r / 2) (t + r / 2) ⊆ U := by
    rintro w ⟨s, hs, rfl⟩
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hmass := hη.2.2.2 (t - r / 2) (t + r / 2) (by linarith)
  have hpos : 0 < μ (η '' Icc (t - r / 2) (t + r / 2)) := by
    rw [hmass]
    exact ENNReal.ofReal_pos.2 (by linarith)
  exact (hpos.trans_le (measure_mono hsub)).ne'

/-- On a compact set, balls of a fixed positive radius have a uniform
positive lower bound under any measure of full support. -/
theorem uniform_ball_mass_of_compact {μ : Measure ℂ} (hμ : μ.IsOpenPosMeasure)
    {K : Set ℂ} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ENNReal.ofReal c ≤ μ (ball z r) := by
  classical
  have := hμ
  let f : ℂ → ℝ := fun z => (min (μ (ball z (r / 2))) 1).toReal
  have hf : ∀ z, 0 < f z := by
    intro z
    apply ENNReal.toReal_pos
    · exact (lt_min (measure_ball_pos μ z (by linarith)) zero_lt_one).ne'
    · exact (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
  have hfbound : ∀ z, ENNReal.ofReal (f z) ≤ μ (ball z (r / 2)) := by
    intro z
    dsimp only [f]
    rw [ENNReal.ofReal_toReal (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne]
    exact min_le_left _ _
  have hfinite : ∀ F : Finset ℂ, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ F, c ≤ f z := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert z F hz ih =>
      obtain ⟨c, hc, hcb⟩ := ih
      refine ⟨min c (f z), lt_min hc (hf z), ?_⟩
      intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hcb w hw)
  obtain ⟨T, _, hT, hcover⟩ := finite_cover_balls_of_compact hK (show 0 < r / 2 by linarith)
  obtain ⟨c, hc, hcb⟩ := hfinite hT.toFinset
  refine ⟨c, hc, ?_⟩
  intro z hz
  obtain ⟨w, hwT, hwz⟩ : ∃ w ∈ T, z ∈ ball w (r / 2) := by
    simpa only [mem_iUnion, exists_prop] using hcover hz
  have hsub : ball w (r / 2) ⊆ ball z r := by
    intro u hu
    rw [mem_ball] at hwz hu ⊢
    have htri := dist_triangle u w z
    rw [dist_comm w z] at htri
    linarith
  exact (ENNReal.ofReal_le_ofReal (hcb w (hT.mem_toFinset.2 hwT))).trans
    ((hfbound w).trans (measure_mono hsub))

/-- A proper area-parametrized space-filling curve gives finite mass to every
bounded Euclidean ball. -/
theorem ball_mass_lt_top_of_proper {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (z : ℂ) (r : ℝ) : μ (ball z r) < ⊤ := by
  have hcompact : IsCompact (η ⁻¹' closedBall z r) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη.1, hp⟩).isCompact_preimage (isCompact_closedBall z r)
  obtain ⟨T, hT⟩ := hcompact.isBounded.subset_closedBall 0
  let B : ℝ := |T| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hsub : ball z r ⊆ η '' Icc (-B) B := by
    intro w hw
    obtain ⟨t, rfl⟩ := hη.2.2.1 w
    refine ⟨t, ?_, rfl⟩
    have ht : |t| ≤ T := by
      have := hT (show t ∈ η ⁻¹' closedBall z r from ball_subset_closedBall hw)
      simpa [Real.dist_eq] using this
    have hT' := le_abs_self T
    have htb := abs_le.1 ht
    dsimp [B]
    constructor <;> linarith
  have hmass := hη.2.2.2 (-B) B (by linarith)
  exact (measure_mono hsub).trans_lt (by rw [hmass]; exact ENNReal.ofReal_lt_top)

/-- The uniform fixed-radius lower bound as a real-valued mass. -/
theorem uniform_ball_toReal_of_area_parametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    {K : Set ℂ} (hK : IsCompact K) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ (μ (ball z r)).toReal := by
  obtain ⟨c, hc, hb⟩ := uniform_ball_mass_of_compact (open_pos_of_area_parametrized hη) hK hr
  exact ⟨c, hc, fun z hz => (ENNReal.ofReal_le_iff_le_toReal (ball_mass_lt_top_of_proper hη hp z r).ne).1 (hb z hz)⟩

end MatedCRT
