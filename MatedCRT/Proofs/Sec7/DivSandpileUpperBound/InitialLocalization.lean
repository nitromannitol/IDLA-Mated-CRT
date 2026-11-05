import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialCellSizes
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.RandomGapLimit

/-! Localization of the initial boundary estimate by countably many events.
The mating-of-trees infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric

/-- An almost-everywhere countable exhaustion transfers conditional convergence
from increasing null-measurable events to the original event. -/
theorem tendsToOneOn_of_ae_subset_iUnion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Set Ω) (G : ℕ → Set Ω) (E : ℝ → Set Ω)
    (hmono : Monotone G) (hmeas : ∀ n, NullMeasurableSet (G n) P)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ n, ω ∈ G n)
    (hE : ∀ n, TendsToOneOn P (G n) E) : TendsToOneOn P F E := by
  have hlim := tendsToOneOn_iUnion_of_monotone P G E hmono hmeas hE
  unfold TendsToOneOn at hlim ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  apply measure_mono_ae
  filter_upwards [hcover] with ω hω hω'
  exact ⟨mem_iUnion.mpr (hω hω'.1), hω'.2⟩


/-- A measurable increasing exhaustion of fixed localization events promotes
the fixed-localization estimate to the full before-exit event. -/
theorem initial_boundary_odometer_of_localization_exhaustion
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∃ C : ℝ, 1 < C ∧ ∀ (t δ q : ℝ), 0 < t → 0 < δ → 0 ≤ q →
      ∀ (G : ℕ → Set Ω) (d : ℕ → ℝ) (O : ℕ → Set ℂ),
      Monotone G → (∀ n, NullMeasurableSet (G n) S.P) →
      (∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∃ n, ω ∈ G n) →
      (∀ n, 0 < d n ∧ O n ⊆ ball 0 ρ ∧ O n ⊆ closedBall 0 ρ \ {0} ∧
        0 < infDist (0 : ℂ) (O n)) →
      (∀ n ω, ω ∈ G n → t < clusterExitTime (Λ ω) ρ ∧
        cthickening (2 * d n) (frontier (Λ ω t)) ⊆ O n ∧
        ∀ x ∈ cthickening (2 * d n) (frontier (Λ ω t)),
          S.c₀ / 6 * _root_.HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x -
            (-t * (S.c₀ / 6) * _root_.HarmonicBalls.greenFunction (ball 0 ρ) 0 x) ≤ q) →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ε * (⨆ a : vBoundary (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)),
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) ≤ C * (q + 2 * δ)} := by
  obtain ⟨C, hC, hfixed⟩ := initial_boundary_odometer_of_fixed_localization
    𝒮 h41 h33 hscale γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro t δ q ht hδ hq G d O hmono hmeas hcover hO hG
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply tendsToOneOn_of_ae_subset_iUnion S.P _ G _ hmono hmeas hcover
  intro n
  obtain ⟨hd, hO1, hO2, hdist⟩ := hO n
  have hn := hfixed t δ q (d n) ht hδ hq hd (O n) hO1 hO2 hdist
  unfold TendsToOneOn at hn ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
    (Eventually.of_forall fun _ => zero_le) ?_
  exact Eventually.of_forall fun ε => measure_mono fun ω hω => ⟨hG n ω hω.1, hω.2⟩

end MatedCRT.Sec7
