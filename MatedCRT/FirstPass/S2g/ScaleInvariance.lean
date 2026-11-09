import MatedCRT.Steps.Sec2.ConeScaleInvariance
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Measurability.ConeRescaledCircle
import MatedCRT.Draft.Section2

/-! # Lemma 2.6 (scale invariance of the global family) from the a.s. factorization (q1, fp-S2g)

The first-pass theorem `firstPass_2_6` (`FirstPass/S1S2S8SA.lean:83`) takes the retired input
`FrozenConeHarmonicBallFunctional` (all continuous circle processes, `FirstPass/Frozen/S1S2S8SA.lean:35`), which is not
admissible. Its proof, `coneScaleInvariance_core` (`Steps/Sec2/ConeScaleInvariance.lean`), uses that input only pointwise
along a.e. `ω`, for the field and for its rescaled version. This file replaces the input by an almost-sure factorization on
a measurable set of circle processes of full cone law (`ConeGlobalFamilyFactorStep`), and proves Lemma 2.6 from it.

Written argument of the new step: `notes/fp-gaps/G-S2-2-5-2-6.md` Sections 2–3 (formulas (9)–(10)), which use Theorem 1
(stopped code) of Section 1 and the good support of `notes/fp-gaps/G-S2-measurable.md` Section 3. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **OPEN NEW step (q1, fp-S2g; neither proved nor frozen): the global family is a measurable functional of the circle
process on the cone-law support.** There are a map `Φ` from circle average processes to space-time processes and a
measurable set `G` of circle average processes such that: (i) on `G`, for every continuous circle average process `c` with
`circleProcess c ∈ G`, every LQG limit `ν` of `c` and every global family `Λ` for `ν`, the process `globalFamilyProcess Λ`
equals `Φ (circleProcess c)`; (ii) for every cone field, `Φ` is a.e. measurable for the law of the circle process, and the
circle process lies in `G` almost surely. Unlike the retired `FrozenConeHarmonicBallFunctional`, the identity is not
asserted for every continuous `c`, only on the full-law set `G`. -/
def ConeGlobalFamilyFactorStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ (Φ : (Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop) (G : Set (Ioi (0 : ℝ) × ℂ → ℝ)),
    MeasurableSet G ∧
    (∀ c : ℝ → ℂ → ℝ, circleProcess c ∈ G → ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ) →
      ∀ ν : Measure ℂ, IsLQGLimit γ c ν → ∀ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily ν Λ →
        globalFamilyProcess Λ = Φ (circleProcess c)) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω)) ∧ ∀ᵐ ω ∂P, circleProcess (hcirc ω) ∈ G

/-- Transfer of an almost sure membership along equality in law, for a measurable set. -/
theorem ae_mem_of_law_eq_measurable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {f g : Ω → X} {G : Set X} (hG : MeasurableSet G) (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hlaw : P.map g = P.map f) (hfG : ∀ᵐ ω ∂P, f ω ∈ G) : ∀ᵐ ω ∂P, g ω ∈ G := by
  have h1 : ∀ᵐ y ∂(P.map f), y ∈ G := (ae_map_iff hf (p := fun y => y ∈ G) hG).2 hfG
  rw [← hlaw] at h1
  exact (ae_map_iff hg (p := fun y => y ∈ G) hG).1 h1

/-- **Lemma 2.6 from the a.s. factorization (q1, fp-S2g).** The scale invariance of the global family: the joint law of the
circle process and of the global family is invariant under the cone rescaling, given `ConeGlobalFamilyFactorStep`,
the quantum-cone scaling law and the LQG measure properties. The proof is `coneScaleInvariance_core` with the identity
applied almost surely, the rescaled circle process lying in `G` almost surely by equality in law. -/
theorem coneScaleInvariance_of_globalFamilyFactor (hfac : ConeGlobalFamilyFactorStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) :
    ConeScaleInvarianceStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb
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
  refine map_prod_eq_of_ae_eq hmeasc hmeasb hlaw hΦ ?_ ?_
  · filter_upwards [hΛ, hcont, hcone.2.2, hGc] with ω hω hc hl hg
    exact hchar (hcirc ω) hg hc (μ ω) hl (Λ ω) hω
  · filter_upwards [hΛ, hcont, hlqg, hGb] with ω hω hc hs hg
    exact hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2 _
      (hω.rescaledFamily coneHarmonicBallFamilyOnScalingStep hs.1 hb)

/-- **Lemma 2.6** (`ConeScaleInvarianceStmt`, Draft `Section2.lean:108`), first-pass form, conditional on the one OPEN
step `ConeGlobalFamilyFactorStep`. Replaces `firstPass_2_6` of `FirstPass/S1S2S8SA.lean:83` (retired input). -/
theorem firstPass_2_6_of_globalFamilyFactor (hfac : ConeGlobalFamilyFactorStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) : ConeScaleInvarianceStmt :=
  coneScaleInvariance_of_globalFamilyFactor hfac hscale h22 (coneScaleRadiusPosStep_of_input hscale)

end MatedCRT
