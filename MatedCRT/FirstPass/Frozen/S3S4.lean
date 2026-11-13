import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec1.Convergence

/-!
# Frozen external inputs of Sections 3 and 4

Each `def` below is an external input (general mathematics or a cited result of the paper), used as an explicit hypothesis. Nothing here is a claim about this paper's clusters, odometers, harmonic balls or IDLA processes beyond the cited statement itself.
-/

namespace MatedCRT

/-- Lemma 3.2 (`lemma:discrete-holder-continuity`, paper line 1018), corrected form, cited from `\cite{gwynne2019harmonic}` Theorem 3.9 (locator: GMS Theorem 3.9, (3.30)-(3.33), arXiv:1807.07511v3; the paper's citation is "Theorem 3.9").
The printed Draft `DiscreteHolderContinuityStmt` is FALSE; this is the corrected statement.
Truth check: UNSURE (see docs/campaign/FROZEN-PROVENANCE.md) for an unconstrained SLE model; TRUE under the certified reference law, see `SLEReferenceExistsInput`. -/
def FrozenDiscreteHolderContinuityCorrected (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteHolderContinuityCorrectedStep 𝒮

/-- Regular exit of planar Brownian motion from a disk: almost surely, immediately after the first exit time from `ball z r` the path makes an outward radial excursion (`0 < ⟪b(τ) - z, b(t) - b(τ)⟫` for arbitrarily small `t > τ`). Source: Mörters-Peres, *Brownian Motion* (Cambridge 2010), Theorem 2.7 and Theorem 2.16 (strong Markov property at the exit time and Blumenthal's 0-1 law; standard). The statement is about planar Brownian motion only, not about this paper's objects.
Truth check: TRUE. The disk and starting point are fixed before the almost-sure quantifier.
Discharged: `MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (`MatedCRT/FirstPass/LPBridge/BrownianOutwardExcursion.lean:113`) proves it unconditionally. -/
def FrozenBrownianOutwardExcursionAtExit : Prop :=
  BrownianOutwardExcursionAtExitStep

/-- Truth check: TRUE for every model `𝒮` that satisfies the three SLE closure inputs (`SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput`): it is then given by `ConeEnvironmentScalingUnderSLE 𝒮` (Frozen/S1d.lean). The cone-law step uses `FrozenConeScalingLaw` (Frozen/S4S6c.lean) instead.
Scaling of the quantum cone environment and of the mating-of-trees coupling: for `b > 0` there is a valid environment `S'` on the same probability space with `η^b = R_b⁻¹ η(b ·)`, `bm^b = b^{-1/2} bm(b ·)` and `μ^b = b⁻¹ μ_h(R_b ·)`, where `R_b` is the cone scale radius. Source: Duplantier-Miller-Sheffield (2014, *Mating of trees*; the arXiv identifier as cited in `MatedCRT/External/QuantumCone.lean`), Proposition 4.13(i) (quantum cone scaling, DMS14 eq:quantum-cone-scaling) together with the Brownian scaling of the mating-of-trees pair. It concerns the quantum cone environment only, not clusters, odometers, harmonic balls or IDLA processes. Locator: standard; locator not yet pinned. -/
def FrozenConeEnvironmentScaling (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeEnvironmentScalingStep 𝒮

end MatedCRT
