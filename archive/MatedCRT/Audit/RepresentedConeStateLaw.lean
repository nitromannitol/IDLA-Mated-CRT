import MatedCRT.Proofs.Sec1.EnvironmentScaling.RepresentedCircleCodeLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-!
# Represented cone state law: consumer audit

Consumers audited, with their definitions in `MatedCRT/Proofs/Sec1/EnvironmentScaling/Field.lean` (lines 1103-1176):
* `RescaledConeObservableLawStep`: the law of every admissible observable of the rescaled field
  (the boundary of env-steps.tex:299-335);
* `RescaledConeRepresentedLawStep`: a same-space represented distribution `H'` of the rescaled pairing, with the law of `H`
  and the circle identity on one event;
* `RescaledConeDistributionCircleStep`: pathwise circle recovery of the rescaled distribution at all `r > 0` and `z`;
* `RescaledConeDistributionCircleGridStep`: the same identity at the countable dyadic and grid indices;
* `RescaledConeDistributionLawStep`: the law of the rescaled distribution equals the law of `H`.

Proved countable-law identification used here: `map_eq_of_codeTests_map_eq` (CountableObservableIdentification.lean,
commit af180eb), for which the code embedding `planeDistributionCode.embedding` is Leonardo Bonanno's countable
distribution code (DistributionCode.lean, `LatticeProb.Bonanno.LQGMetric.Field`).

Residual premises that remain, with full Lean types:
* `RescaledConeDistributionCircleGridStep 𝒮` (pathwise grid recovery; no law identity implies it);
* `RescaledConeDistributionCodeLawStep 𝒮` (defined below). It implies `RescaledConeDistributionLawStep 𝒮` (proved below), so it
  is at least as strong as that residual; the converse is the same measure-map argument through the measurable code and is
  not formalized here;
* `QuantumConeScalingInput` (literature input, MatedCRT/External/QuantumCone.lean:19).

`rescaledConeFieldStep_of_residuals` is a conditional assembly, not a closure. The WPN-53 premise is not used on this chain.
The reference-law identifications of CountableObservableIdentification.lean (`map_countableObservables_eq_reference`,
`map_codeTests_eq_of_reference`, `map_represented_distribution_eq_of_reference`) take WPN-53 as `hF` and need `IsQuantumCone`
for each environment. The rescaled pair has that property only as the conclusion of `RescaledConeFieldStep`, so they do not
discharge the residuals. `map_eq_of_codeTests_map_eq`, the one used here, takes neither.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open MatedCRT MatedCRT.Sec1

namespace MatedCRT.Audit

/-- Countable form of `RescaledConeDistributionLawStep`: the joint law of the test-pairing code
`(rescaledDistribution γ b (H ω) (R ω) (planeDistributionCode.test c))_c` equals the code law of `H`. The quantifiers,
the representation of `S.hC` by `H` and the normalization `R = coneScaleRadius` are those of the consumer. -/
def RescaledConeDistributionCodeLawStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ b : ℝ, 0 < b →
    ∀ (H : Ω → LQGMetric.DistC) (R : Ω → ℝ), Measurable H → Measurable R →
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      (∀ᵐ ω ∂S.P, R ω = coneScaleRadius γ (S.hcirc ω) b) →
      S.P.map (fun ω (c : LQGMetric.CoordJ) =>
          rescaledDistribution γ b (H ω) (R ω) (planeDistributionCode.test c)) =
        S.P.map (fun ω (c : LQGMetric.CoordJ) => H ω (planeDistributionCode.test c))

/-- The distribution-law consumer follows from its countable form. The rescaled distribution is measurable as the composite
of `measurable_rescaledDistribution` with `(H, R)`, and `map_eq_of_codeTests_map_eq` then identifies the laws. The two
distributions live on the same space `S.P`, so no same-space representative is asserted from equality in law. -/
theorem rescaledConeDistributionLawStep_of_codeLaw {𝒮 : SpaceFillingSLEModel}
    (hcode : RescaledConeDistributionCodeLawStep 𝒮) : RescaledConeDistributionLawStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hH hR hrep hRn
  have hpair : Measurable fun ω => (H ω, R ω) := hH.prodMk hR
  have hmeas0 := (measurable_rescaledDistribution γ b).fun_comp hpair
  have hmeas : Measurable fun ω => rescaledDistribution γ b (H ω) (R ω) := hmeas0
  exact map_eq_of_codeTests_map_eq hmeas hH (hcode γ hγ hγ2 Ω S hS b hb H R hH hR hrep hRn)

/-- Conditional assembly of the represented cone chain, not a closure. From the scaling input, the pathwise grid recovery
and the countable code law, the existing Field.lean steps give `RescaledConeFieldStep`: grid to circles
(`rescaledConeDistributionCircleStep_of_grid`), circles and law to the represented law
(`rescaledConeRepresentedLawStep_of_distribution`), represented law to the observable law
(`rescaledConeObservableLawStep_of_represented_law`), and observable law to the field step
(`rescaledConeFieldStep_of_observable_law`). The three arguments are the residuals that remain. -/
theorem rescaledConeFieldStep_of_residuals (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (hgrid : RescaledConeDistributionCircleGridStep 𝒮) (hcode : RescaledConeDistributionCodeLawStep 𝒮) :
    RescaledConeFieldStep 𝒮 :=
  rescaledConeFieldStep_of_observable_law 𝒮 hscale
    (rescaledConeObservableLawStep_of_represented_law 𝒮
      (rescaledConeRepresentedLawStep_of_distribution 𝒮 hscale
        (rescaledConeDistributionCircleStep_of_grid 𝒮 hscale hgrid)
        (rescaledConeDistributionLawStep_of_codeLaw hcode)))

end MatedCRT.Audit

end
