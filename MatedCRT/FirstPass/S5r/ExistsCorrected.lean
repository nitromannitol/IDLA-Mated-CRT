import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.FirstPass.S2b

/-!
# Family process for the corrected Lemma 2.4 (fp-S5r)

Copy of `MatedCRTEnv.IsValid.exists_measurable_familyProcess` (Proofs/Measurability/BoundaryLayer.lean:369) with the
hypothesis `h24` retyped to `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43), the provider form of
Lemma 2.4 (operator note 05:30 UTC; notes/fp-gaps/CHATGPT-idla-h24-T.md). The proof uses only the existence part of
Lemma 2.4 (`⟨T, hT, Λ', hΛ', hstop, -⟩`), so the body is unchanged. The original file is not edited.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

theorem MatedCRTEnv.IsValid.exists_measurable_familyProcess_corrected {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hfam : ConeFamilyAEMeasurableStep) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) :
    ∃ X : Ω → ℝ × ℂ → Prop, (∀ p, Measurable fun ω => X ω p) ∧ ∀ᵐ ω ∂S.P, ∃ (T : ℝ) (Λ' : ℝ → Set ℂ),
      0 < T ∧ IsConeHarmonicBallFamilyOn (S.μ ω) Λ' T ∧ IsStoppedAtHalfBall Λ' T ∧
        ∀ (t : ℝ) (x : ℂ), X ω (t, x) ↔ t ∈ Ioo 0 T ∧ x ∈ Λ' t := by
  have hcone := hS.isConeField
  have hpr : ∀ᵐ ω ∂S.P, 0 < (stoppedConeFamily (S.μ ω)).1 ∧
      IsConeHarmonicBallFamilyOn (S.μ ω) (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1 ∧
      IsStoppedAtHalfBall (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1 := by
    filter_upwards [h24c γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hcone] with ω hω
    obtain ⟨T, hT, Λ', hΛ', hstop, -⟩ := hω
    exact stoppedConeFamily_spec ⟨T, hT, Λ', hΛ', hstop⟩
  have hY : AEMeasurable
      (fun ω => familyProcess (stoppedConeFamily (S.μ ω)).2 (stoppedConeFamily (S.μ ω)).1) S.P :=
    ((hfam γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hcone).1 (fun ω => (stoppedConeFamily (S.μ ω)).1)
      (fun ω => (stoppedConeFamily (S.μ ω)).2) hpr).snd
  obtain ⟨X, hXmeas, hXae⟩ := hY
  refine ⟨X, fun p => (measurable_pi_apply p).comp hXmeas, ?_⟩
  filter_upwards [hpr, hXae] with ω hprω hXω
  exact ⟨_, _, hprω.1, hprω.2.1, hprω.2.2, fun t x => Iff.of_eq (congrFun hXω (t, x)).symm⟩


end MatedCRT
