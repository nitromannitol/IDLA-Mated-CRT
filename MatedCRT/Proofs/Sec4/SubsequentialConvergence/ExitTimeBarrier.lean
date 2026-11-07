import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DiscreteBoundaryLayer

/-! The normalized exit time bounds the odometer up to the boundary. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- The pointwise version of the odometer bounds, including vertices outside
the killed domain. This is the exit-time barrier used in Lemma 4.6. -/
theorem abs_matedLeastSupersolution_le_normExitTime
    {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ}
    (h43 : ∀ a ∈ cellVertices ε η (closedBall 0 ρ),
      max (-normExitTime m (ballInterior ε η ρ) a) (matedObstacle m ε η ρ t a) ≤
        matedLeastSupersolution m ε η ρ t a ∧ matedLeastSupersolution m ε η ρ t a ≤ 0)
    (a : ℤ) : |matedLeastSupersolution m ε η ρ t a| ≤
      normExitTime m (ballInterior ε η ρ) a := by
  by_cases ha : a ∈ cellVertices ε η (closedBall 0 ρ)
  · obtain ⟨hlo, hhi⟩ := h43 a ha
    have hlo' := (le_max_left _ _).trans hlo
    rw [abs_of_nonpos hhi]
    linarith
  · have hai : a ∉ ballInterior ε η ρ := fun h =>
      ha (Equibounded.mem_cellVertices_closedBall_of_mem_ballInterior h)
    rw [normExitTime_eq_zero_of_not_mem m hai]
    unfold matedLeastSupersolution
    rw [Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem hai ha, abs_zero]

/-- Rescaling preserves the exit-time barrier, without requiring any sign
assumption on the median. -/
theorem abs_rescaledMatedLeastSupersolution_le_rescaled_normExitTime
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ρ t ε : ℝ} {ω : Ω}
    (h43 : ∀ a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ),
      max (-normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a)
          (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a) ≤
        matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ∧
        matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ≤ 0)
    (x : ℂ) : |rescaledMatedLeastSupersolution S ρ t ε ω x| ≤
      |rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ)) x| := by
  unfold rescaledMatedLeastSupersolution rescale
  rw [abs_mul, abs_mul, abs_of_nonneg (normExitTime_nonneg _ _ _)]
  exact mul_le_mul_of_nonneg_left (abs_matedLeastSupersolution_le_normExitTime h43 _) (abs_nonneg _)

/-- Almost surely the barrier holds for every time, mesh and point together. -/
theorem ae_abs_rescaledOdometer_le_rescaled_normExitTime
    (𝒮 : SpaceFillingSLEModel) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε → ∀ x : ℂ,
      |rescaledMatedLeastSupersolution S ρ t ε ω x| ≤
        |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ)) x| := by
  filter_upwards [discreteBasicProperties 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hω
  intro t ε ht hε x
  exact abs_rescaledMatedLeastSupersolution_le_rescaled_normExitTime (hω t ε ht hε).1 x

/-- The exit-time boundary estimate controls all odometers simultaneously in
probability, uniformly over their positive time parameter. -/
theorem odometer_boundary_small_of_statements
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {δ : ℝ} (hδ : 0 < δ) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < ρ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ t : ℝ, 0 < t ∧ ∃ x ∈ closedBall 0 ρ \ closedBall 0 r',
        δ < |rescaledMatedLeastSupersolution S ρ t ε ω x|} ≤ e := by
  let R := (ρ + 1) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hρR : ρ ≤ R := by dsimp [R]; linarith
  obtain ⟨r', hr'0, hr'ρ, hb⟩ := discreteExitBoundary_of_statements 𝒮 h33 h35 h217
    hγ hγ2 hR hR1 S hS hρ (ball_subset_ball hρR) hδ he
  refine ⟨r', hr'0, hr'ρ, ?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with ε hb hε
  have hε' : 0 < ε := hε
  calc
    S.P {ω | ∃ t : ℝ, 0 < t ∧ ∃ x ∈ closedBall 0 ρ \ closedBall 0 r',
        δ < |rescaledMatedLeastSupersolution S ρ t ε ω x|} ≤
      S.P {ω | ∃ x ∈ closedBall (0 : ℂ) ρ \ closedBall 0 r',
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ)) x|} := by
      apply measure_mono_ae
      filter_upwards [ae_abs_rescaledOdometer_le_rescaled_normExitTime 𝒮 hγ hγ2 hρ hρ1 S hS] with ω hω
      rintro ⟨t, ht, x, hx, hδx⟩
      exact ⟨x, hx, hδx.trans_le (hω t ε ht hε' x)⟩
    _ ≤ e := hb

end MatedCRT
