import MatedCRT.FirstPass.S2g.Draft24

/-!
# FIRST PASS, Draft Lemma 2.5 from its corrected canonical form (q4, fp-S4d-4-2-assembly)

`ConeScaleInvarianceUpToFixedTimeStmt` (Draft `Section2.lean:88`; paper `lemma:scale-invariance-up-to-fixed-time`,
`idla_mated_crt-corrected.tex:548`) is stated for an arbitrary stopping time `T` and adds the uniqueness of the rescaled
stopping time. The corrected canonical form `ConeScaleInvarianceUpToFixedTimeCanonicalStmt` (`FirstPass/S2g.lean:51`,
proved by `firstPass_2_5_corrected`, `S2g/Assembly2456.lean`) is stated at the canonical half-ball time `halfBallTime`.

This file bridges the two statements with two inputs:
* the identity `halfBallTime (μ ω) = T'` for every stopped family `Λ'` on `(0, T')`, proved here from the canonical
  Lemma 2.4 and the closure step, exactly as the uniqueness clause of `coneHarmonicBallsUpToFixedTimeStmt_of_canonical`
  (`S2g/Draft24.lean`);
* `ConeRescaledHalfBallHorizonUniqueStep` (`Proofs/Sec2/ConeFamilyMeasurable/ScaledUniqueness.lean`): two families for the
  same measure, each stopped at `∂B_{1/2}` after rescaling by `R_b`, have the same rescaled horizon. It is an explicit
  hypothesis of `coneScaleInvarianceUpToFixedTimeStmt_of_canonical` (NEW, OPEN; the paper's proof of Lemma 2.5 uses it
  implicitly through Lemma 2.4 for `μ_{h^b}`, "T^b = sup{t : R_b^{-1} Λ_{bt} ⊂ B_{1/2}}"). It is not derived from the Draft
  statement here, since `ConeRescaledHalfBallHorizonUniqueStep_of_lemmas` takes `ConeScaleInvarianceUpToFixedTimeStmt` as input.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Rescaled half-ball horizon uniqueness (NEW step, OPEN; q4, fp-S4d-4-2-assembly).** Copy of the statement of
`ConeRescaledHalfBallHorizonUniqueStep` (`Proofs/Sec2/ConeFamilyMeasurable/ScaledUniqueness.lean:13`), restated here
because that file is outside the fleet build closure. For a cone field and `b > 0`, almost surely, two families `Λ`, `Γ`
for `μ(ω)` on `(0, b T)` and `(0, b S)` whose rescalings by the cone scale radius `R_b` are stopped at `∂B_{1/2}` at `T`
and `S` satisfy `S = T` (paper `lemma:scale-invariance-up-to-fixed-time`, line 548: `T^b = sup{t : R_b^{-1} Λ_{bt} ⊂ B_{1/2}}`
is determined by the family). No proof is given here. -/
def ConeRescaledHalfBallHorizonUniqueFPStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
    ∀ (T S : ℝ) (Λ Γ : ℝ → Set ℂ),
      0 < T → IsConeHarmonicBallFamilyOn (μ ω) Λ (b * T) →
      IsStoppedAtHalfBall (rescaledFamily Λ (coneScaleRadius γ (hcirc ω) b) b) T →
      0 < S → IsConeHarmonicBallFamilyOn (μ ω) Γ (b * S) →
      IsStoppedAtHalfBall (rescaledFamily Γ (coneScaleRadius γ (hcirc ω) b) b) S → S = T

/-- **Stopping time of every stopped family is the canonical half-ball time (q4, fp-S4d-4-2-assembly).** For a cone field,
almost surely every family `Λ'` of harmonic balls on `(0, T')` which is stopped at `∂B_{1/2}` at `T'` has
`T' = halfBallTime (μ ω)`. The proof is the uniqueness clause of `coneHarmonicBallsUpToFixedTimeStmt_of_canonical`
(`S2g/Draft24.lean`, `hTT`), with the canonical family of Lemma 2.4 as reference family. -/
theorem halfBallTime_eq_of_stopped_fp (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (T' : ℝ) (Λ' : ℝ → Set ℂ), 0 < T' → IsConeHarmonicBallFamilyOn (μ ω) Λ' T' →
      IsStoppedAtHalfBall Λ' T' → halfBallTime (μ ω) = T' := by
  filter_upwards [hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone, hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone] with ω hω hcl'
  obtain ⟨Λ, hT, hΛ, hst⟩ := hω
  intro T' Λ' hT' hΛ' hst'
  exact stopped_unique_of_closureInside_fp hT hT' hst hst' hΛ.2.1.monotoneOn hΛ'.2.1.monotoneOn (hΛ.eqOn hΛ')
    (hcl' _ _ hΛ hst) (hcl' _ _ hΛ' hst')

/-- **Draft Lemma 2.5 (`ConeScaleInvarianceUpToFixedTimeStmt`) from the corrected canonical form (q4, fp-S4d-4-2-assembly).**
The stopping time of the given family is `halfBallTime` almost surely (`halfBallTime_eq_of_stopped_fp`), so the canonical
form applies to the given family. Its time `Tb` is `halfBallTime` of the rescaled measure `ENNReal.ofReal (b⁻¹) • μ(R_b ·)`,
and the uniqueness clause of the Draft statement is `ConeRescaledHalfBallHorizonUniqueStep` applied to the canonical family
`Λb` (stopped at `Tb`) and to the given rescaled-stopped family. The joint law is the canonical one after the almost sure
replacement `T ω = halfBallTime (μ ω)` (`Measure.map_congr`). -/
theorem coneScaleInvarianceUpToFixedTimeStmt_of_canonical (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (hc25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt)
    (hU : ConeRescaledHalfBallHorizonUniqueFPStep) : ConeScaleInvarianceUpToFixedTimeStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone T Λ hTΛ b hb
  have hTeq : ∀ᵐ ω ∂P, halfBallTime (μ ω) = T ω := by
    filter_upwards [halfBallTime_eq_of_stopped_fp hcan hcl γ hγ0 hγ2 Ω P hC hcirc μ hcone, hTΛ] with ω hω hTω
    exact hω (T ω) (Λ ω) hTω.1 hTω.2.1 hTω.2.2
  have hcanHyp : ∀ᵐ ω ∂P, 0 < halfBallTime (μ ω) ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (halfBallTime (μ ω)) ∧
      IsStoppedAtHalfBall (Λ ω) (halfBallTime (μ ω)) := by
    filter_upwards [hTeq, hTΛ] with ω h1 h2
    rw [h1]
    exact h2
  obtain ⟨-, Λb, hΛb, -, -, hlaw⟩ := hc25 γ hγ0 hγ2 Ω P hC hcirc μ hcone Λ hcanHyp b hb
  refine ⟨fun ω => halfBallTime (ENNReal.ofReal (b⁻¹) • (μ ω).map (fun z : ℂ => z / ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ))),
    Λb, ?_, ?_⟩
  · filter_upwards [hΛb, hU γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb] with ω hω hUω
    obtain ⟨h0, huniq, hstop⟩ := hω
    refine ⟨h0, huniq.1, hstop, fun T' Λ' hT' hΛ' hst' => ?_⟩
    have hST := hUω _ _ _ _ h0 huniq.1 hstop hT' hΛ' hst'
    rw [hST] at hΛ'
    exact ⟨hST, huniq.2 Λ' hΛ'⟩
  · have hJ : (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω))) =ᵐ[P]
        (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (halfBallTime (μ ω)))) := by
      filter_upwards [hTeq] with ω hω
      simp only [hω]
    exact (Measure.map_congr hJ).trans hlaw

end MatedCRT
