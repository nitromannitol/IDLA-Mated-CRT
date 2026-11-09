import MatedCRT.Proofs.Sec5.FieldCircleVersionProof
import MatedCRT.Proofs.Sec5.StoppedInterior
import MatedCRT.Proofs.Sec5.StoppedMarginStepAssembly

/-!
# The stopped margin from the checked producers of the actual code

Task `z5-stopped-margin-producer-integration`. Source: `notes/wpn-steps2/steps2-r3.tex`, lines 3386-3435 (audited,
sha256 `88dfb1f9`): the erosion minimum `M̂ = m(K, f)` of the actual code, the everywhere positive choice
`c_pos = M̂` where `M̂ > 0` and `1` otherwise, and the almost-sure identity `t < T → M̂ = M` on the good event.

The two residual producers of `StoppedMarginStepAssembly`, `CodeSectionStmt` and `FieldCircleVersionStmt`, are no longer
hypotheses here. `ConeOriginNull.codeSectionStmt_holds` (`SupersolutionSectionIdentity.lean:92`) and
`fieldCircleVersionStmt_holds` (`FieldCircleVersionProof.lean:22`) supply them, and
`StoppedActualMarginCode.stoppedMarginCode_of_preston` (`FieldCircleVersionProof.lean:64`) gives
`StoppedInterior.StoppedMarginCodeStep` from the three explicit Preston inputs. These Preston statements are faithful
literature inputs (`MatedCRT/Proposed/PrestonAnalytic2008.lean`, lines 43, 35, 60); they are not promoted here.

* `cPos_margin_of_preston`: `cPos_margin_spec` at `stoppedMarginCode_of_preston`. There is an `S.envSigma`-measurable,
  everywhere positive `c` with `c = cPos (rawMargin S Λ ρ δ s t)` almost surely on `{t < T}`.
* `stoppedSurplusInteriorStep_of_preston`: `StoppedInterior.stoppedSurplusInterior_of_gap`, with the measurable margin
  from `StoppedActualMarginCode.stoppedInteriorMeasurableStep_of_preston`. The strict obstacle gap
  `HarmonicBallStrictObstacleGapStep`, the pole `StoppedSurplusPoleStep`, the geometry `StoppedInteriorGeometryStep` and
  `MepsScalingInput` stay hypotheses at their present scope.

Geometric consumers that remain named hypotheses. None is proved here, and no measurability of a degree is assumed:
* `StoppedInteriorGeometryStep` (`StoppedInterior.lean:156`) requires WPN-51-geometry
  (`docs/campaign/GAPS-TAKEOVER-20261108.md`, section WPN-51-geometry).
* `StoppedSurplusPoleStep` (`StoppedInterior.lean:137`) requires WPN-51-pole. Its inner-degree lintegral route needs the
  measurability of `gmsInnerDegree ∘ η`, which is WPN-51-canonical-inner-degree-measurability
  (`GAPS-TAKEOVER-20261108.md`, line 656). The hypothesis is `hMeas` of
  `StoppedPoleInnerDegreeMoments.canonical_innerDegree_lintegral_lt_top` (line 875). The outer-moment form
  `canonical_innerDegree_outer_lt_top` (line 888) has no such hypothesis.

No Section 5.1 closure is claimed, and nothing here is a numbered result.
-/

namespace MatedCRT.StoppedMarginProducerAssembly

open MeasureTheory Filter Topology Set Metric
open MatedCRT.StoppedMarginStepAssembly (cPos rawMargin)

/-- **The environment-measurable positive margin under the Preston inputs** (steps2-r3 lines 3386-3435). The producers of
the actual code give `StoppedMarginCodeStep`, and `cPos_margin_spec` then yields an `S.envSigma`-measurable everywhere
positive `c` with `c = c_pos(M)` almost surely on `{t < T}`, where `M = rawMargin` is the continuum margin. No
`CodeSectionStmt` or `FieldCircleVersionStmt` hypothesis is assumed. The family `Λ` is arbitrary, with its almost-sure
`IsConeHarmonicBallFamily` premise. -/
theorem cPos_margin_of_preston (𝒮 : SpaceFillingSLEModel)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ s t : ℝ) (hδ : 0 < δ) (hs : 0 < s) (ht : 0 < t) :
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → c ω = cPos (rawMargin S Λ ρ δ s t) ω :=
  MatedCRT.StoppedMarginStepAssembly.cPos_margin_spec 𝒮
    (MatedCRT.StoppedActualMarginCode.stoppedMarginCode_of_preston 𝒮 hP hCantor hT61)
    γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ s t hδ hs ht

/-- **`StoppedSurplusInteriorStep` under the Preston inputs.** The repaired consumer
`StoppedInterior.stoppedSurplusInterior_of_gap` receives its margin from
`stoppedInteriorMeasurableStep_of_preston`, so no measurability of the margin is assumed. The strict obstacle gap `hgap`,
the pole `hpoleS`, the geometry `hgeo` and the scaling input `hmeps` are the consumer's named hypotheses, unchanged in
scope. `hgeo` and `hpoleS` are WPN-51 items (see the module docstring). -/
theorem stoppedSurplusInteriorStep_of_preston (𝒮 : SpaceFillingSLEModel)
    (hgap : MatedCRT.HarmonicBallStrictObstacleGapStep 𝒮)
    (hpoleS : MatedCRT.StoppedInterior.StoppedSurplusPoleStep 𝒮)
    (hgeo : MatedCRT.StoppedInterior.StoppedInteriorGeometryStep 𝒮)
    (hmeps : MatedCRT.MepsScalingInput 𝒮)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt) :
    MatedCRT.StoppedSurplusInteriorStep 𝒮 :=
  MatedCRT.StoppedInterior.stoppedSurplusInterior_of_gap 𝒮 hgap hpoleS hgeo
    (MatedCRT.StoppedActualMarginCode.stoppedInteriorMeasurableStep_of_preston 𝒮 hP hCantor hT61) hmeps

end MatedCRT.StoppedMarginProducerAssembly
