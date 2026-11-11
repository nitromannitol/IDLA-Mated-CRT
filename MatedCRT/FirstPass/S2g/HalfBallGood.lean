import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.HalfBallLocal

/-!
# Good set of measures for the canonical half-ball family

`ConeCanonicalHalfBallStep` (S2g.lean) reduces, deterministically, to the almost sure pathwise inputs of the cone measures
(`ae_canonical_family_of_pathwise`, HalfBallFamily.lean). Passing from the whole-plane source model to a cone field is the
transfer H2 of ; it is packaged here as one named step.

Terminology: quantum cone and LQG measure (Duplantier-Miller-Sheffield), harmonic balls and the canonical half-ball time
(Armstrong-Kuusi-Mourrat), Green functions and superharmonic minimum principle (Armitage-Gardiner).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- **Named hypothesis (see docs/campaign/COUNTED.md).** Good set of measures for the pathwise half-ball inputs of
a quantum cone field: there is a measurable set `G` of measures on `ℂ` such that every `ν ∈ G` satisfies
`ConePathwiseHalfBallInputs ν`, and `μ ω ∈ G` almost surely. H1-H2 (the source model from `FrozenConeLogLocalCodeLaw`, `MatedCRT/FirstPass/Frozen/S2h.lean:29`; the full-image
set of `FullImage.lean`; the transfer `pathwiseInputs_of_restrict_eq` of `HalfBallLocal.lean`). Measurability of the
good set: the S1c / pattern (analytic bad set and `FrozenUniversalMeasurabilityOfAnalytic`).
Same shape as `ConeClosureGoodMeasureLawStep` (S2f.lean:26). -/
def ConeHalfBallGoodMeasureLawStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ (∀ ν ∈ G, ConePathwiseHalfBallInputs ν) ∧ ∀ᵐ ω ∂P, μ ω ∈ G

/-- **Reduction (deterministic).** The good-set step gives `ConeCanonicalHalfBallStep`, given the frozen potential-theory
inputs `FrozenSuperharmonicMinimumPrinciple`, `FrozenGreenBallCentre`, `FrozenGreenDiscPole` (FirstPass/Frozen/S2g.lean) and
the Draft statement `HarmonicBalls.GreenFunctionBallStmt`, exactly the hypotheses of `ae_canonical_family_of_pathwise`. -/
theorem coneCanonicalHalfBallStep_of_good (hgood : ConeHalfBallGoodMeasureLawStep)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole) : ConeCanonicalHalfBallStep := by
  intro γ hγ0 hγ2 Ω _ P hC' hcirc μ hcone
  obtain ⟨G, -, hG, hae⟩ := hgood γ hγ0 hγ2 Ω P hC' hcirc μ hcone
  have hin : ∀ᵐ ω ∂P, ConePathwiseHalfBallInputs (μ ω) := hae.mono fun ω hω => hG _ hω
  filter_upwards [ae_canonical_family_of_pathwise P μ hmin hC hGB hpole hin] with ω hω
  exact hω

end MatedCRT
