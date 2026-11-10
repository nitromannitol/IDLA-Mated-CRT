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
Q log R_b - γ⁻¹ log b`). Locator: DMS Proposition 4.13(i) (arXiv:1409.7055v4) + DS Proposition 2.1 (Duplantier–Sheffield, arXiv:0808.1560v2), per notes/fp-gaps/CHATGPT-frozen-locators.md.
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

/-- FIRST-PASS FROZEN. Measurability of the LQG measure in the field, almost surely. For every valid environment `S` with
cone parameter `γ`, the LQG measure `S.μ` agrees almost surely with a `σ(h)`-measurable random measure `g`
(`Measurable[S.fieldSigma] g`). This is the almost-everywhere form: the everywhere form is not freezable, since
`IsLQGMeasure` (Harmonic-Balls-LQG HarmonicBalls/Defs/LQG.lean:63-65) holds almost surely only. Source: Duplantier–Sheffield
(2011, arXiv:0808.1560v2), Proposition 1.1 (the LQG measure is the almost sure limit of the regularised measures `μ_ε`, each
a measurable function of the field), with the locality of the regularisations; locator pending (standard, per
notes/fp-gaps/CHATGPT-frozen-locators.md). Used by: goodAnnulusCover_dyadic_of_frozen (MatedCRT/FirstPass/S4S6c/CoverMinorantAE.lean). -/
def FrozenLQGMeasureFieldMeasurable (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ g : Ω → Measure ℂ, Measurable[S.fieldSigma] g ∧ ∀ᵐ ω ∂S.P, S.μ ω = g ω

/-- RETIRED (proved from `IsValid.matingOfTrees`, operator 23:11 UTC): the statement is
`MatedCRT.MatedCRTEnv.IsValid.ae_tendsto_cocompact` (Proofs/Infra/MatingOfTrees.lean:77), used by
`ExitAe68.ae_exit_ne_top_of_bounded` and `TraceInputs68.cellVertices_finite_of_tendsto`. Not used in any
proof from now on; kept unchanged (never delete).

RETIRED (proved from IsValid.matingOfTrees, operator 23:11 UTC; proof: `MatedCRT.MatedCRTEnv.IsValid.ae_tendsto_cocompact`,
Proofs/Infra/MatingOfTrees.lean:77, used by TraceInputs68.lean). Not used in any proof from now on; kept unchanged (never delete).

FIRST-PASS FROZEN (original). Properness of the space-filling curve, almost surely. For every valid environment `S` with
cone parameter `γ`, almost surely `η(t) → ∞` as `|t| → ∞`: `Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)`, so that a
bounded set of the plane is met by `η` only on a bounded interval of parameters (whole-plane space-filling SLE from
`∞` to `∞`). Source: standard; locator pending (a truth check follows, operator note 2026-11-09 22:25 UTC). Used by: none yet; reserved for the Good event of firstPass_6_8 (LEMMA68 C2, cellVertices
finiteness). -/
def FrozenProperEta (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, Filter.Tendsto (S.η ω) (Filter.cocompact ℝ) (Filter.cocompact ℂ)

end MatedCRT
