import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.WeightedDirichletPotential
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMassGrowth

/-! Buffered Green potentials in the mated-CRT environment. -/

namespace MatedCRT

open MeasureTheory Metric Filter Set Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- Lemma 2.17 gives the continuum Dirichlet identity for every fixed bounded
nonnegative measurable source in a mated-CRT environment. -/
theorem weightedGreenPotential_ae_satisfies_dirichlet
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∀ x, φ x ≤ 1) :
    ∀ᵐ ω ∂S.P,
      let q := fun x => S.c₀ * ∫ y in ball z r,
        greenFunction (ball z r) x y * φ y ∂S.μ ω
      ContinuousOn q (closedBall z r) ∧
        HasLaplacian q ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * -φ x))
          ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * -φ x))) (ball z r) ∧
        ∀ x ∈ sphere z r, q x = 0 := by
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  filter_upwards [hmass, hS.isLQGMeasure] with ω hmassω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  apply weightedGreenPotential_satisfies_dirichlet (S.μ ω) hr hr₀ hβ S.c₀_nonneg
  · intro s hs hs₀ x hx
    exact hup s hs hs₀ x (hball hx)
  · exact hφm
  · exact hφ0
  · exact hφ1

end MatedCRT
