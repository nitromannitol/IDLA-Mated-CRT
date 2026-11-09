import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.LawCode
import MatedCRT.FirstPass.S2g.ScaleInvariance
import MatedCRT.FirstPass.S2g.Canonical

/-! # Lemma 2.5 in coded law form (q1, fp-S2g)

The corrected Lemma 2.5 compares the stopped codes `stoppedCode T Λ = (T, code of the masked process)` of the circle process
and of the rescaled family by `IdentDistrib`. The canonical lifetime `T = halfBallTime` and the masked process are, almost
surely, measurable functions of the circle process (`ConeCanonicalFactorStep`, `S2g/Canonical.lean`, z2's open step, used
as a hypothesis). The rescaled family `Λb` is the transfer, by `rescaledFamily_transfer_fp`, of the canonical family of the
rescaled measure `rescaledMeasure (μ ω) R_b b`, whose existence is clause (ii) of the same step applied to the rescaled
circle process (`ConeLQGScalingStep`, `QuantumConeScalingInput`). -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **Lemma 2.5, coded law (q1, fp-S2g).** For a cone field, a family `Λ` which is almost surely the canonical stopped family
of `μ` (positive time `halfBallTime (μ ω)`, family on `(0, T)`, stopped at `∂B_{1/2}`), and `b > 0`, with `R` the cone scale
radius and `Tb = halfBallTime (rescaledMeasure (μ ω) R b)`: the lifetime `Tb` is a.e. measurable, there is a family `Λb` for
`μ` which is unique on `(0, b Tb)` and whose rescaling is stopped at `∂B_{1/2}` at `Tb`, and the stopped codes of the circle
process and of the family agree in law, as an `IdentDistrib` of `(circle process, stoppedCode)` pairs. -/
def ConeScaleInvarianceUpToFixedTimeCodedStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ,
    (∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall (Λ ω) (halfBallTime (μ ω))) →
  ∀ b : ℝ, 0 < b →
    let R := fun ω => coneScaleRadius γ (hcirc ω) b
    let Tb := fun ω => halfBallTime (rescaledMeasure (μ ω) (R ω) b)
    AEMeasurable Tb P ∧ ∃ Λb : Ω → ℝ → Set ℂ,
      (∀ᵐ ω ∂P, 0 < Tb ω ∧ UniqueConeFamilyOn (μ ω) (Λb ω) (b * Tb ω) ∧
        IsStoppedAtHalfBall (rescaledFamily (Λb ω) (R ω) b) (Tb ω)) ∧
      IdentDistrib (fun ω => (circleProcess (hcirc ω), stoppedCode (halfBallTime (μ ω)) (Λ ω)))
        (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b),
          stoppedCode (Tb ω) (rescaledFamily (Λb ω) (R ω) b))) P P

/-- **Lemma 2.5, coded law, from the canonical factorization (q1, fp-S2g).** The factor identities of
`ConeCanonicalFactorStep` at the circle process and at the rescaled circle process express both stopped codes as the same
measurable map of the circle process, and the rescaled circle process has the same law (`QuantumConeScalingInput`). -/
theorem firstPass_2_5_coded_of_canonicalFactor (hfac : ConeCanonicalFactorStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeScaleInvarianceUpToFixedTimeCodedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone Λ hΛ b hb R Tb
  have hP : IsProbabilityMeasure P := hcone.1
  have hpos := coneScaleRadiusPosStep_of_input hscale
  obtain ⟨ΨT, Ψ, G, hGm, hchar, hfull⟩ := hfac γ hγ0 hγ2
  obtain ⟨hΨT, hΨ, hGc⟩ := hfull Ω P hC hcirc μ hcone
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hmeasb := coneRescaledCircleAEMeasurableStep_of_pos hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
  have hlqg := coneLQGScalingStep_of_steps h22 hpos γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
  have hcont := hcone.2.1.ae_continuousOn_circle
  have hGb : ∀ᵐ ω ∂P, circleProcess (rescaledCircle γ (hcirc ω) (R ω) b) ∈ G :=
    ae_mem_of_law_eq_measurable hGm hmeasc hmeasb hlaw hGc
  have hΨTb : AEMeasurable ΨT (P.map fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) := by
    rw [hlaw]
    exact hΨT
  have hHm : AEMeasurable (fun x : Ioi (0 : ℝ) × ℂ → ℝ => (ΨT x, processCode (Ψ x)))
      (P.map fun ω => circleProcess (hcirc ω)) :=
    hΨT.prodMk (measurable_processCode.comp_aemeasurable hΨ)
  have hHmb : AEMeasurable (fun x : Ioi (0 : ℝ) × ℂ → ℝ => (ΨT x, processCode (Ψ x)))
      (P.map fun ω => circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) := by
    rw [hlaw]
    exact hHm
  -- the canonical data of the rescaled measure, and its lifetime as a function of the rescaled circle process
  have hcanB : ∀ᵐ ω ∂P, 0 < Tb ω ∧ Tb ω = ΨT (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) ∧
      (∃ Λ' : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (R ω) b) Λ' (Tb ω) ∧
        IsStoppedAtHalfBall Λ' (Tb ω)) ∧
      ∀ (T' : ℝ) (Λ'' : ℝ → Set ℂ), 0 < T' → IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (R ω) b) Λ'' T' →
        IsStoppedAtHalfBall Λ'' T' → familyProcess Λ'' T' = Ψ (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) := by
    filter_upwards [hlqg, hGb, hcont] with ω hs hg hc
    obtain ⟨hi, ⟨Λ', h1, h2⟩, hp, hiii⟩ := hchar _ hg (continuousOn_rescaledCircle hc hs.1) _ hs.2
    exact ⟨hp, hi, ⟨Λ', h1, h2⟩, hiii⟩
  have hTb : AEMeasurable Tb P :=
    (hΨTb.comp_aemeasurable hmeasb).congr (by
      filter_upwards [hcanB] with ω hω
      exact hω.2.1.symm)
  -- a canonical family of the rescaled measure, chosen measurably in ω
  obtain ⟨x, hx⟩ : ∃ x : Ω → ℝ → Set ℂ, ∀ᵐ ω ∂P, IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (R ω) b)
      (x ω) (Tb ω) ∧ IsStoppedAtHalfBall (x ω) (Tb ω) := by
    refine ⟨fun ω => Classical.epsilon (fun Λ' : ℝ → Set ℂ =>
      IsConeHarmonicBallFamilyOn (rescaledMeasure (μ ω) (R ω) b) Λ' (Tb ω) ∧ IsStoppedAtHalfBall Λ' (Tb ω)), ?_⟩
    filter_upwards [hcanB] with ω hω
    exact Classical.epsilon_spec hω.2.2.1
  refine ⟨hTb, fun ω => rescaledFamily (x ω) (R ω)⁻¹ b⁻¹, ?_, ?_⟩
  · filter_upwards [hx, hcanB, hlqg] with ω hx' hω hs
    have key := rescaledFamily_transfer_fp hs.1 hb hx'.1 hx'.2
    exact ⟨hω.1, uniqueConeFamilyOn_of_family key.1, key.2.1⟩
  · -- the joint laws: the circle process paired with the stopped code is `Φ` of the circle process a.s.
    have hA : ∀ᵐ ω ∂P, stoppedCode (halfBallTime (μ ω)) (Λ ω) =
        (ΨT (circleProcess (hcirc ω)), processCode (Ψ (circleProcess (hcirc ω)))) := by
      filter_upwards [hΛ, hcont, hcone.2.2, hGc] with ω hω hc hl hg
      obtain ⟨hi, _, _, hiii⟩ := hchar (hcirc ω) hg hc (μ ω) hl
      unfold stoppedCode
      rw [hiii _ (Λ ω) hω.1 hω.2.1 hω.2.2, hi]
    have hB : ∀ᵐ ω ∂P, stoppedCode (Tb ω) (rescaledFamily (rescaledFamily (x ω) (R ω)⁻¹ b⁻¹) (R ω) b) =
        (ΨT (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)),
          processCode (Ψ (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)))) := by
      filter_upwards [hx, hcanB, hlqg] with ω hx' hω hs
      unfold stoppedCode
      rw [rescaledFamily_rescaledFamily_inv (x ω) hs.1.ne' hb.ne']
      rw [hω.2.2.2 (Tb ω) (x ω) hω.1 hx'.1 hx'.2, hω.2.1]
    have hA' : ∀ᵐ ω ∂P, stoppedCode (halfBallTime (μ ω)) (Λ ω) =
        (fun x : Ioi (0 : ℝ) × ℂ → ℝ => (ΨT x, processCode (Ψ x))) (circleProcess (hcirc ω)) := hA
    have hB' : ∀ᵐ ω ∂P, stoppedCode (Tb ω) (rescaledFamily (rescaledFamily (x ω) (R ω)⁻¹ b⁻¹) (R ω) b) =
        (fun x : Ioi (0 : ℝ) × ℂ → ℝ => (ΨT x, processCode (Ψ x)))
          (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b)) := hB
    have hmapA : AEMeasurable (fun ω => (circleProcess (hcirc ω), stoppedCode (halfBallTime (μ ω)) (Λ ω))) P :=
      (hmeasc.prodMk (hHm.comp_aemeasurable hmeasc)).congr (by
        filter_upwards [hA'] with ω hω
        exact congrArg (fun y => (circleProcess (hcirc ω), y)) hω.symm)
    have hmapB : AEMeasurable (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b),
        stoppedCode (Tb ω) (rescaledFamily (rescaledFamily (x ω) (R ω)⁻¹ b⁻¹) (R ω) b))) P :=
      (hmeasb.prodMk (hHmb.comp_aemeasurable hmeasb)).congr (by
        filter_upwards [hB'] with ω hω
        exact congrArg (fun y => (circleProcess (rescaledCircle γ (hcirc ω) (R ω) b), y)) hω.symm)
    have hmap := map_prod_eq_of_ae_eq hmeasc hmeasb hlaw hHm hA' hB'
    exact ⟨hmapA, hmapB, hmap⟩

end MatedCRT
