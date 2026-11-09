import MatedCRT.FirstPass.S2g

/-!
# First-pass frozen inputs of the canonical factorization (fp-S2i, z2)

EXTERNAL facts about the `γ`-quantum cone (Duplantier-Miller-Sheffield) used by the canonical factorization
`ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`). They concern the law of the field, not the paper's clusters,
harmonic balls or IDLA processes.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Uniqueness in law of the circle average process of the `γ`-quantum cone, for `0 < γ < 2`: any two
cone fields (`IsConeField`, which encodes `IsQuantumCone` and the LQG measure) have the same law of the circle average
process `circleProcess`, a random element of `(0, ∞) × ℂ → ℝ` with the product σ-algebra. The law of the radial process is
determined by the conditioned Brownian motion `ν` of `IsQuantumCone.radial_law`, the lateral part is the whole-plane GFF
(`IsQuantumCone.lateral_law`), and the circle averages are measurable functions of these two.
Source: Duplantier-Miller-Sheffield, "Liouville quantum gravity as a mating of trees" (arXiv:1409.7055), quantum cone of
Definition 4.1 and its uniqueness; the paper's cone is Definition 2.1 (paper/idla_mated_crt-corrected.tex, lines 427-439).
Standard; locator pending.
Used by: coneCanonicalFactor_proved (MatedCRT/FirstPass/S2i.lean). -/
def ConeCircleLawUniqueStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ)
      (μ' : Ω' → Measure ℂ), IsConeField γ P' hC' hcirc' μ' →
    P.map (fun ω => circleProcess (hcirc ω)) = P'.map (fun ω => circleProcess (hcirc' ω))

/-- FIRST-PASS FROZEN. Existence of a standard Borel model of the `γ`-quantum cone, for `0 < γ < 2`: there is a standard
Borel probability space carrying an `IsConeField` (the cone is a random field, realised on a Polish space of generalized
functions and its circle averages). The standard Borel structure is used only to make the image of a measurable set of
samples under the joint circle-and-family code analytic.
Source: Duplantier-Miller-Sheffield, arXiv:1409.7055, existence of the quantum cone (Definition 4.1 and the construction
of the field); the paper's cone is Definition 2.1 (paper/idla_mated_crt-corrected.tex, lines 427-439). Standard; locator
pending.
Used by: coneCanonicalFactor_proved (MatedCRT/FirstPass/S2i.lean). -/
def ConeReferenceExistsStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ

end MatedCRT
