import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ObstacleConvergence
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialVertex
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.External.SLE
import MatedCRT.Draft.Section4

/-! Initial stopped-odometer estimates away from the source.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open Filter Topology Set Metric MeasureTheory HarmonicBalls

/-- Uniform convergence of the least supersolution and the obstacle bounds
individual normalized odometers on cells where the continuum gap is small.
The estimate is simultaneous over all such cells, including random families
of cells. -/
theorem normalized_odometer_le_of_small_continuum_gap (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t δ q : ℝ) (ht : 0 < t) (hδ : 0 < δ) (O : Set ℂ)
    (hO : O ⊆ ball 0 ρ) (hO' : O ⊆ closedBall 0 ρ \ {0})
    (hdist : 0 < infDist (0 : ℂ) O) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a : ℤ, cell ε (S.η ω) a ⊆ O →
        (∀ x ∈ cell ε (S.η ω) a,
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q) →
        (S.mε ε)⁻¹ * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a ≤ q + 2 * δ} := by
  have hw := h41 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht δ hδ
  have hφ := obstacle_convergence_off_origin 𝒮 h33 γ hγ hγ' ρ hρ hρ' Ω S hS
    t δ ht hδ O hO' hdist
  unfold ProbTendsToOne at hφ
  unfold TendsToOneOn
  have hsum := hw.add hφ
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply le_trans ?_ (measure_union_le _ _)
  apply measure_mono_ae
  filter_upwards [hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hp harea
  rintro ⟨hT, hbad⟩
  by_cases hwbad : ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|
  · exact Or.inl ⟨hT, hwbad⟩
  · by_cases hφgood : ∀ x ∈ O,
        |rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)| ≤ δ
    · exfalso
      apply hbad
      intro a hcell hgap
      obtain ⟨x, hx, ha⟩ := exists_vertexOf_eq_of_area_parametrized harea hp hε a
      have hxO := hcell hx
      have hw' := le_of_not_gt (fun hh => hwbad ⟨x, hO hxO, hh⟩)
      have hφ' := hφgood x hxO
      have hgap' := hgap x hx
      have haW : a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ) :=
        ⟨x, hx, ball_subset_closedBall (hO hxO)⟩
      simp only [stoppedOdometer, haW, ↓reduceIte]
      change |rescale (S.mε ε) ε (S.η ω)
        (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) x - _| ≤ δ at hw'
      simp only [rescale, ha] at hw' hφ'
      have hw'' := (abs_le.mp hw').2
      have hφ'' := (abs_le.mp hφ').1
      nlinarith
    · exact Or.inr hφgood

/-- The upper median scaling turns a normalized odometer estimate into the
mesh-normalized estimate used to initialize the shell iteration. -/
theorem mesh_odometer_le_of_normalized_le {ε m u b C : ℝ}
    (hε : 0 < ε) (hm : 0 < m) (hb : 0 ≤ b)
    (hscale : m ≤ C * ε⁻¹) (hu : m⁻¹ * u ≤ b) : ε * u ≤ C * b := by
  have hu' : u ≤ b * m := (div_le_iff₀ hm).mp (by simpa [div_eq_mul_inv, mul_comm] using hu)
  have hscale' : ε * m ≤ C := by
    have h := mul_le_mul_of_nonneg_left hscale hε.le
    have heq : ε * (C * ε⁻¹) = C := by field_simp
    simpa only [heq] using h
  have hmul := mul_le_mul_of_nonneg_left hu' hε.le
  have hmul' := mul_le_mul_of_nonneg_right hscale' hb
  nlinarith

/-- A simultaneous vertex estimate bounds the graph-boundary supremum,
including when the boundary is empty. -/
theorem mesh_boundary_iSup_le {m : ℤ → ℤ → ℕ} {Θ : Set ℤ}
    {ε B : ℝ} {u : ℤ → ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (h : ∀ a ∈ vBoundary m Θ, ε * u a ≤ B) :
    ε * (⨆ a : vBoundary m Θ, u a) ≤ B := by
  have hsup : (⨆ a : vBoundary m Θ, u a) ≤ B / ε := by
    apply Real.iSup_le
    · intro a
      exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using h a a.property)
    · positivity
  have hmul := mul_le_mul_of_nonneg_left hsup hε.le
  calc
    ε * (⨆ a : vBoundary m Θ, u a) ≤ ε * (B / ε) := hmul
    _ = B := by field_simp

/-- On the event before the cluster exits, cells separated from the source
with small continuum gap have small mesh-normalized stopped odometer, with
probability tending to one. -/
theorem mesh_odometer_le_of_small_continuum_gap (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q : ℝ), 0 < t → 0 < δ → 0 ≤ q → ∀ O : Set ℂ,
      O ⊆ ball 0 ρ → O ⊆ closedBall 0 ρ \ {0} → 0 < infDist (0 : ℂ) O →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ∀ a : ℤ, cell ε (S.η ω) a ⊆ O →
          (∀ x ∈ cell ε (S.η ω) a,
            S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
              (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x) ≤ q) →
          ε * stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hscale⟩ := hscale γ hγ hγ'
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  refine ⟨C, hC, ?_⟩
  intro t δ q ht hδ hq O hO hO' hdist
  have hnormal := normalized_odometer_le_of_small_continuum_gap 𝒮 h41 h33 γ hγ hγ'
    ρ hρ hρ' Ω S hS Λ hΛ t δ q ht hδ O hO hO' hdist
  unfold TendsToOneOn at hnormal ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnormal
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hε hε'
  obtain ⟨hlower, hupper⟩ := hscale ε hε hε'
  have hm : 0 < S.mε ε := lt_of_lt_of_le
    (mul_pos (inv_pos.mpr (by linarith : 0 < C)) (inv_pos.mpr hε)) hlower
  apply measure_mono
  rintro ω ⟨hT, hbad⟩
  refine ⟨hT, ?_⟩
  intro hgood
  apply hbad
  intro a ha hgap
  exact mesh_odometer_le_of_normalized_le hε hm (by linarith) hupper (hgood a ha hgap)

end MatedCRT.Sec7
