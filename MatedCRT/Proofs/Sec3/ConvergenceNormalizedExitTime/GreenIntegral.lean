import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AwayFromPole
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.MassTight
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.UniformIntegrable

/-!
# Truncated Green integrals in probability

Uniform Green-kernel convergence away from the pole implies convergence of
its integrals over a fixed set. The area-parametrized curve supplies tightness
of the mass and discrete integrability; the same Green-kernel convergence
gives continuum integrability without a Hölder estimate on an annulus.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal

/-- Lemma 3.3 integrated over a fixed set separated from the pole. -/
theorem greenIntegral_converges_away_from_pole
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (D : Set ℂ) (hD : D ⊆ closedBall z r \ {y}) (hDρ : D ⊆ ball 0 ρ)
    (hdist : 0 < infDist y D) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x in D, rescale (S.mε ε) ε (S.η ω)
        (fun a => ε⁻¹ * greenKernel (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) a) x ∂S.μ ω)
      (fun ω => ∫ x in D, (S.c₀ / 6) * greenFunction (ball z r) y x ∂S.μ ω) := by
  apply tendstoInProbability_setIntegral_of_uniformOn S.P S.μ D _ _
  · intro e he
    obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1
      (hS.tendsto_measure_large_ball_mass ρ) e he).exists
    refine ⟨2 * ((n : ℝ) + 1), by positivity, ?_⟩
    exact (measure_mono fun ω hω => lt_of_lt_of_le hω (measure_mono hDρ)).trans hn
  · intro ε hε
    have hint := greenFunction_ae_integrableOn_away_from_pole 𝒮 h33 hγ hγ2 hρ hρ1
      S hS hr hball hy D hD hDρ hdist
    filter_upwards [hS.ae_integrableOn_rescale_ball hε ρ (fun ω a =>
      ε⁻¹ * greenKernel (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) a), hint]
      with ω hd hc
    exact ⟨hd.mono_set hDρ, hc⟩
  · intro δ hδ
    have h := h33 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy δ hδ D hD hdist
    simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le, exists_prop] using h

end MatedCRT
