import MatedCRT.FirstPass.Derived.BrownianExitLawIdentification
import LatticeProb.Prob.BrownianCenteredExitEndpoint

set_option autoImplicit false
noncomputable section

open MeasureTheory Set HarmonicBalls BouRabeeGwynne LatticeProb
open scoped ENNReal NNReal

namespace MatedCRT

/-- Normalizing a planar Brownian exit position gives the exit law from the
normalized domain with the correspondingly normalized starting point. -/
theorem planarBrownianExitProbability_normalize (U : Set ℂ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (c z : ℂ) {r : ℝ} (hr : 0 < r) :
    let W := (fun w : ℂ => c + r • w) ⁻¹' U
    let hW : IsOpen W := hU.preimage (by fun_prop)
    ((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
        (fun w => r⁻¹ • (w - c)) =
      ((planarBrownianExitProbability W hW (r⁻¹ • (z - c)) : ProbabilityMeasure ℂ) :
        Measure ℂ) := by
  dsimp only
  let E := Complex.orthonormalBasisOneI.repr
  let W : Set ℂ := (fun w : ℂ => c + r • w) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hV : IsOpen (E '' U) := E.toHomeomorph.isOpenMap U hU
  have hVb : Bornology.IsBounded (E '' U) := E.isometry.lipschitzWith.isBounded_image hUb
  have hset : E '' W = (fun x => E c + r • x) ⁻¹' (E '' U) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨c + r • w, hw, by simp only [map_add, map_smul]⟩
    · rintro ⟨w, hw, heq⟩
      refine ⟨E.symm x, ?_, E.apply_symm_apply x⟩
      change c + r • E.symm x ∈ U
      have hEq : c + r • E.symm x = w := E.injective (by
        simpa only [map_add, map_smul, E.apply_symm_apply] using heq.symm)
      rw [hEq]
      exact hw
  let ρ := (planarBrownianMotion 0).map TargetLawTemplateEvent.complexPathToEuc
  have hρ : BouRabeeGwynne.IsStandardBrownianLaw ρ :=
    TargetLawTemplateEvent.isStandardBrownianLaw_map_complexPathToEuc
  have hn := brownian_exit_endpoint_law_normalize (d := 2) (by norm_num) hρ
    (E c) (E z) hr hV hVb
  have hstart : E (r⁻¹ • (z - c)) = r⁻¹ • (E z - E c) := by
    simp only [map_smul, map_sub]
  have hf : Measurable (fun w : ℂ => r⁻¹ • (w - c)) := by fun_prop
  have hg : Measurable (fun x : BouRabeeGwynne.Euc 2 => r⁻¹ • (x - E c)) := by fun_prop
  apply MeasurableEmbedding.map_injective E.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  change (((planarBrownianExitProbability U hU z : ProbabilityMeasure ℂ) : Measure ℂ).map
    (fun w => r⁻¹ • (w - c))).map E =
      ((planarBrownianExitProbability W hW (r⁻¹ • (z - c)) : ProbabilityMeasure ℂ) :
        Measure ℂ).map E
  rw [Measure.map_map E.continuous.measurable hf]
  have hcomp : E ∘ (fun w : ℂ => r⁻¹ • (w - c)) =
      (fun x : BouRabeeGwynne.Euc 2 => r⁻¹ • (x - E c)) ∘ E := by
    funext w
    simp only [Function.comp_apply, map_smul, map_sub]
  rw [hcomp, ← Measure.map_map hg E.continuous.measurable]
  rw [← BrownianExitLawIdentification.stoppedBrownianLaw_endPoint_eq U hU z ρ hρ]
  rw [hn, ← hset, ← hstart]
  exact BrownianExitLawIdentification.stoppedBrownianLaw_endPoint_eq W hW _ ρ hρ

end MatedCRT
end
