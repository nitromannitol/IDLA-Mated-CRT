import MatedCRT.FirstPass.S2g.ScaleInvariance

/-! # Lemma 2.6 with measurable joint laws (q1, fp-S2g-2-4-2-5-corrected)

The Draft form `ConeScaleInvarianceStmt` states the equality of the push-forwards
`P.map (circle, globalFamilyProcess)` and its rescaled version, with no measurability clause. `Measure.map` of a map that is
not AEMeasurable is `0`, so the Draft equality is weak. The corrected law `ConeScaleInvarianceAEStmt` keeps that equality
verbatim and adds the a.e. measurability of both joint processes. The measurability is not an extra input: the a.s.
factorization of `ConeGlobalFamilyFactorStep` makes each joint process a.e. equal to the pair (circle process, measurable
function of the circle process). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **Corrected Lemma 2.6, measurable law form (`ConeScaleInvarianceAEStmt`, q1).** For a cone field, a global family `Λ` of
harmonic balls almost surely, and `b > 0`: the joint process (circle process, global family process) and the joint process of
the rescaled circle and rescaled family are both almost everywhere measurable, and their push-forward laws agree (the Draft
`ConeScaleInvarianceStmt`). Lemma 2.6 of the corrected paper, with its law stated through AE-measurable maps. -/
def ConeScaleInvarianceAEStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
  ∀ b : ℝ, 0 < b →
    AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P ∧
    AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P ∧
    P.map (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) =
      P.map (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b)))

/-- **Lemma 2.6, measurable law, from the a.s. factorization (q1).** The equality of laws is
`coneScaleInvariance_of_globalFamilyFactor`; the two AE-measurability clauses come from the a.s. identities
`globalFamilyProcess (Λ ω) = Φ (circleProcess (hcirc ω))` with `Φ` AE-measurable on the circle law. -/
theorem coneScaleInvarianceAE_of_globalFamilyFactor (hfac : ConeGlobalFamilyFactorStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) :
    ConeScaleInvarianceAEStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
  have hmap := coneScaleInvariance_of_globalFamilyFactor hfac hscale h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hΛ b hb
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨Φ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨hΦ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hmeasb := coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
  have hlqg := coneLQGScalingStep_of_steps h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) ∈ G :=
    ae_mem_of_law_eq_measurable hGm hmeasc hmeasb hlaw hGc
  have hFa : ∀ᵐ ω ∂P, globalFamilyProcess (Λ ω) = Φ (circleProcess (hcirc ω)) := by
    filter_upwards [hΛ, hcont, hcone.2.2, hGc] with ω hω hc hl hg
    exact hchar (hcirc ω) hg hc (μ ω) hl (Λ ω) hω
  have hFb : ∀ᵐ ω ∂P,
      globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) =
        Φ (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
    filter_upwards [hΛ, hcont, hlqg, hGb] with ω hω hc hs hg
    exact hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2 _
      (hω.rescaledFamily coneHarmonicBallFamilyOnScalingStep hs.1 hb)
  have hΦa : AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω)) := hΦ
  have hΦb : AEMeasurable Φ
      (P.map fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
    rw [hlaw]
    exact hΦ
  refine ⟨?_, ?_, hmap⟩
  · refine (hmeasc.prodMk (hΦa.comp_aemeasurable hmeasc)).congr ?_
    filter_upwards [hFa] with ω hω
    exact Prod.ext rfl hω.symm
  · refine (hmeasb.prodMk (hΦb.comp_aemeasurable hmeasb)).congr ?_
    filter_upwards [hFb] with ω hω
    exact Prod.ext rfl hω.symm

end MatedCRT
