import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ExitTimeTail
import MatedCRT.Draft.Section2
import MatedCRT.External.SLE
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-! Scaling the second exit-time moment from Lemma 2.18. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The lower scaling bound on the median cancels the two inverse powers
of the mesh in the second-moment estimate. -/
theorem scaled_second_moment_coefficient_le {ε m C K : ℝ}
    (hε : 0 < ε) (hK : 0 < K)
    (hm : K⁻¹ * ε⁻¹ ≤ m) :
    m⁻¹ ^ 2 * (2 * C ^ 2 * ε ^ (-(2 : ℝ))) ≤ 2 * (C * K) ^ 2 := by
  have hmpos : 0 < m := (mul_pos (inv_pos.mpr hK) (inv_pos.mpr hε)).trans_le hm
  have hmult : ε⁻¹ ≤ K * m := by
    have h := mul_le_mul_of_nonneg_left hm hK.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] using h
  have hratio : m⁻¹ * ε⁻¹ ≤ K := by
    have h := (div_le_iff₀ hmpos).2 hmult
    simpa [div_eq_mul_inv, mul_comm] using h
  have hsq : (m⁻¹ * ε⁻¹) ^ 2 ≤ K ^ 2 :=
    (sq_le_sq₀ (by positivity) hK.le).2 hratio
  have hrpow : ε ^ (2 : ℝ) = ε ^ (2 : ℕ) := by
    exact Real.rpow_natCast ε 2
  rw [Real.rpow_neg hε.le, hrpow]
  calc
    m⁻¹ ^ 2 * (2 * C ^ 2 * (ε ^ 2)⁻¹) =
        2 * C ^ 2 * (m⁻¹ * ε⁻¹) ^ 2 := by rw [inv_pow]; ring
    _ ≤ 2 * (C * K) ^ 2 := by nlinarith [sq_nonneg C]

/-- Lemma 2.18 and the median scaling bound give a mesh-uniform second-moment
estimate for the normalized walk exit time. -/
theorem scaled_secondMoment_polyHighProb {𝒮 : SpaceFillingSLEModel}
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ B : ℝ, 0 < B ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → PolyHighProb S.P fun ε => {ω |
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D,
            ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
              ENNReal.ofReal B * (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ 2} := by
  obtain ⟨α, hα, h218α⟩ := h218 γ hγ hγ2
  obtain ⟨K, hK, hKscale⟩ := hscale γ hγ hγ2
  have hKpos : 0 < K := by linarith
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C, hC, h218C⟩ := h218α ρ hρ hρ1
  refine ⟨2 * (C * K) ^ 2, by positivity, ?_⟩
  intro Ω _ S hS
  obtain ⟨ε₀, hε₀, hscaleε⟩ := hKscale Ω S hS
  apply (h218C Ω S hS).mono_of_small hε₀
  intro ε hε hεlt ω hω D hD hDsub hμ a ha
  have hm := (hscaleε ε hε hεlt).1
  have hmpos : 0 < S.mε ε := (mul_pos (inv_pos.mpr hKpos) (inv_pos.mpr hε)).trans_le hm
  have hmoment := hω.1 D hD hDsub hμ a ha 2
  have hcoef : ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
      ENNReal.ofReal (2 * C ^ 2 * ε ^ (-(2 : ℝ))) ≤
      ENNReal.ofReal (2 * (C * K) ^ 2) := by
    change ENNReal.ofReal ((S.mε ε)⁻¹) ^ 2 *
      ENNReal.ofReal (2 * C ^ 2 * ε ^ (-(2 : ℝ))) ≤ _
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hmpos.le),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (scaled_second_moment_coefficient_le hε hKpos hm)
  have hmoment' : exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
      ENNReal.ofReal (2 * C ^ 2 * ε ^ (-(2 : ℝ))) *
        (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
          ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ 2 := by
    convert hmoment using 1; norm_num
  calc
    _ ≤ ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
        (ENNReal.ofReal (2 * C ^ 2 * ε ^ (-(2 : ℝ))) *
          (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
            ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ 2) := by gcongr
    _ ≤ _ := by rw [← mul_assoc]; gcongr

/-- The second-moment estimate controls the normalized exit-time tail on the
same polynomially high probability event. -/
theorem scaled_exitTime_tail_polyHighProb {𝒮 : SpaceFillingSLEModel}
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (T : ℝ≥0∞) (hT : T ≠ ⊤) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ B : ℝ, 0 < B ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → PolyHighProb S.P fun ε => {ω |
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D,
            T * (∫⁻ x in {x | T ≤
                ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
                  (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)},
              ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
                (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)
                ∂srwLaw (S.mult ε ω) a) ≤
              ENNReal.ofReal B * (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D,
                ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂S.μ ω) ^ 2} := by
  obtain ⟨α, hα, h⟩ := scaled_secondMoment_polyHighProb h218 hscale hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨B, hB, hP⟩ := h ρ hρ hρ1
  refine ⟨B, hB, ?_⟩
  intro Ω _ S hS
  apply (hP Ω S hS).mono
  intro ε ω hω D hD hDsub hμ a ha
  exact (scaled_exitTime_tail_le_secondMoment _ _ _ _ T hT).trans
    (hω D hD hDsub hμ a ha)

end MatedCRT
