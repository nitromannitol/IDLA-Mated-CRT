import MatedCRT.FirstPass.S2g.LawCode
import MatedCRT.FirstPass.S2g.ScaleInvariance

/-! # Lemmas 2.5 and 2.6 in coded law form

The frozen Draft statements `ConeScaleInvarianceStmt` (Draft `Section2.lean:108`) and
`ConeScaleInvarianceUpToFixedTimeStmt` (Draft `Section2.lean:88`) compare raw processes by `P.map` equality. The
corrected first-pass forms compare the countable codes of `LawCode.lean` by `IdentDistrib`, which also records the
almost-sure measurability of both joint codes. This file proves the coded Lemma 2.6 from `ConeGlobalFamilyFactorStep`
 (`ScaleInvariance.lean`, used as a hypothesis). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **Lemma 2.6, coded law.** For a cone field, a family `Λ` of harmonic balls for `μ` almost surely, and
`b > 0`: the joint law of the circle process and of the global code of the family is that of the rescaled circle process
and of the global code of the rescaled family `t ↦ R_b⁻¹ Λ_{bt}`, as an `IdentDistrib` (so both maps are a.e.
measurable). -/
def ConeScaleInvarianceCodedStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
  ∀ b : ℝ, 0 < b →
    IdentDistrib (fun ω => (circleProcess (hcirc ω), globalCode (Λ ω)))
      (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        globalCode (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P P

/-- **Lemma 2.6, coded law, from the a.s. factorization.** The almost-sure identities of
`ConeGlobalFamilyFactorStep` make both joint processes a.e. equal to measurable functions of the circle process, so they
are a.e. measurable; the equality of the raw joint laws (`coneScaleInvariance_of_globalFamilyFactor`) is then an
`IdentDistrib`, and the code map `(x, F) ↦ (x, code F)` transports it. -/
theorem firstPass_2_6_coded_of_globalFamilyFactor (hfac : ConeGlobalFamilyFactorStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) : ConeScaleInvarianceCodedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
  have hpos := coneScaleRadiusPosStep_of_input hscale
  have hmap := coneScaleInvariance_of_globalFamilyFactor hfac hscale h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hΛ b hb
  obtain ⟨Φ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨hΦ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hP : IsProbabilityMeasure P := hcone.1
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hmeasb := coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
  have hlqg := coneLQGScalingStep_of_steps h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) ∈ G :=
    ae_mem_of_law_eq_measurable hGm hmeasc hmeasb hlaw hGc
  have hΦb : AEMeasurable Φ (P.map fun ω => circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b)) := by
    rw [hlaw]
    exact hΦ
  have hA : AEMeasurable (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω))) P := by
    refine (hmeasc.prodMk (hΦ.comp_aemeasurable hmeasc)).congr ?_
    filter_upwards [hΛ, hcont, hcone.2.2, hGc] with ω hω hc hl hg
    rw [hchar (hcirc ω) hg hc (μ ω) hl (Λ ω) hω]
    rfl
  have hB : AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b), globalFamilyProcess (rescaledFamily (Λ ω)
      (coneScaleRadius γ (hcirc ω) b) b))) P := by
    refine (hmeasb.prodMk (hΦb.comp_aemeasurable hmeasb)).congr ?_
    filter_upwards [hΛ, hcont, hlqg, hGb] with ω hω hc hs hg
    rw [hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2 _
      (hω.rescaledFamily coneHarmonicBallFamilyOnScalingStep hs.1 hb)]
    rfl
  have hid : IdentDistrib (fun ω => (circleProcess (hcirc ω), globalFamilyProcess (Λ ω)))
      (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        globalFamilyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b))) P P :=
    ⟨hA, hB, hmap⟩
  exact hid.comp (measurable_prod_processCode (X := Ioi (0 : ℝ) × ℂ → ℝ))

end MatedCRT
