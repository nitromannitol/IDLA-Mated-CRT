import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# First pass: frozen external input of the cone-scaling repair (q2, task fp-S4S6c)

`FrozenConeScalingLaw` replaces `FrozenConeEnvironmentScaling` (Frozen/S3S4.lean), which is FALSE
(notes/fp-gaps/TRUTH-CHECK-2.md, 2026-11-09). It keeps only the quantum-cone facts that the volume-growth
transfer of Section 4 uses: the cone scale radius `R_b` is a.s. positive and measurable, and the rescaled
LQG measure `b⁻¹ μ_h(R_b ·)` has the same law as `μ_h`. It asserts nothing about the SLE curve `η`, the
Brownian pair `bm`, the clock, or the predicate `IsSLE`.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Cone scaling in law. For every valid environment `S` with cone parameter `γ` and every
`b > 0`, with `R_b ω = coneScaleRadius γ (S.hcirc ω) b`:
(1) `R_b > 0` almost surely and `R_b` is almost everywhere measurable;
(2) `μ = S.μ` is a random measure (almost everywhere measurable into `Measure ℂ`), and `ω ↦ b⁻¹ μ_h(R_b ·)`
(`rescaledMeasure (S.μ ω) (R_b ω) b`) is a random measure with the same law as `μ`.
Source: Duplantier–Miller–Sheffield (2014, *Mating of trees*, arXiv:1409.7055v4), Proposition 4.13(i) (quantum cone
scaling), together with the canonical GMC covariance of the LQG measure (the law of `μ_{h^b}` for `h^b = h(R_b ·) +
Q log R_b - γ⁻¹ log b`). Locator: DMS14 Proposition 4.13(i), arXiv:1409.7055v4 page of the proposition pending.
Used by: firstPass_4_1_coneLaw (MatedCRT/FirstPass/S4S6c.lean). -/
def FrozenConeScalingLaw (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ b : ℝ, 0 < b →
      (∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b) ∧
      AEMeasurable (fun ω => coneScaleRadius γ (S.hcirc ω) b) S.P ∧
      AEMeasurable S.μ S.P ∧
      AEMeasurable (fun ω => rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b) S.P ∧
      Measure.map (fun ω => rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b) S.P =
        Measure.map S.μ S.P

end MatedCRT
