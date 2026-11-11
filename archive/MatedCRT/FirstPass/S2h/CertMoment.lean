import MatedCRT.FirstPass.S2h.CertCharged
import MatedCRT.FirstPass.S2h.CutoffUnion
import MatedCRT.FirstPass.S2h.MeasurableIntegral

/-!
# Certificate moments: the pairing `w ↦ ∫ w Δφ` and the restricted moments

Two facts used by the code relation `CertRel` (clause C4 and the restricted moments):
* `continuous_laplacian_pairing`: for a test function `φ` on `B_{3/4}`, the map `w ↦ ∫ w Δφ` is continuous on the
  witness space `C(B̄_{3/4})` (the `L k` of `CertRel`);
* `sup_charged_moment_eq`: the supremum over finite charged families and cutoff levels of the restricted moments is the
  restricted integral over the union of the charged balls (CutoffUnion, `lintegral_restrict_iUnion_eq_iSup_cutoff`).
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The extension `extW` is `dist w w'`-close pointwise on `ℂ` (the witnesses differ only on `B̄_{3/4}`). -/
theorem abs_extW_sub_le (w w' : DiscW) (x : ℂ) : |extW w x - extW w' x| ≤ dist w w' := by
  by_cases hx : x ∈ closedBall (0 : ℂ) (3 / 4)
  · have h1 : extW w x = w ⟨x, hx⟩ := by simp [extW, hx]
    have h2 : extW w' x = w' ⟨x, hx⟩ := by simp [extW, hx]
    rw [h1, h2, ← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : closedBall (0 : ℂ) (3 / 4))
  · have h1 : extW w x = 0 := by simp [extW, hx]
    have h2 : extW w' x = 0 := by simp [extW, hx]
    rw [h1, h2, sub_self, abs_zero]
    exact dist_nonneg

/-- **Continuity of the Laplacian pairing.** For a test function `φ` on `B_{3/4}`, the map
`w ↦ ∫ w Δφ` (with `w` read through `extW`) is continuous on the witness space `C(B̄_{3/4}, ℝ)`. -/
theorem continuous_laplacian_pairing {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) (3 / 4)) φ) :
    Continuous fun w : DiscW => ∫ x, extW w x * Laplacian.laplacian φ x := by
  have hint : ∀ w : DiscW, Integrable fun x => extW w x * Laplacian.laplacian φ x := fun w =>
    integrable_mul_laplacian_of_contOn (extW_continuousOn w) hφ
  have hL1 : Integrable fun x => Laplacian.laplacian φ x := by
    simpa using integrable_mul_laplacian_of_contOn (w := fun _ => (1 : ℝ)) continuousOn_const hφ
  have hC : 0 ≤ ∫ x, ‖Laplacian.laplacian φ x‖ := integral_nonneg fun x => norm_nonneg _
  have key : ∀ w₁ w₂ : DiscW, dist (∫ x, extW w₁ x * Laplacian.laplacian φ x)
      (∫ x, extW w₂ x * Laplacian.laplacian φ x) ≤ dist w₁ w₂ * ∫ x, ‖Laplacian.laplacian φ x‖ := by
    intro w₁ w₂
    rw [Real.dist_eq, ← integral_sub (hint w₁) (hint w₂)]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hL1.norm.const_mul (dist w₁ w₂)) (ae_of_all _ fun x => ?_)).trans
      (le_of_eq (integral_const_mul _ _))
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_extW_sub_le w₁ w₂ x) (norm_nonneg _)
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε / ((∫ x, ‖Laplacian.laplacian φ x‖) + 1), ?_, fun w' hw' => ?_⟩
  · have : 0 < (∫ x, ‖Laplacian.laplacian φ x‖) + 1 := by linarith
    exact div_pos hε this
  · have hC1 : 0 < (∫ x, ‖Laplacian.laplacian φ x‖) + 1 := by linarith
    calc dist (∫ x, extW w' x * Laplacian.laplacian φ x) (∫ x, extW w x * Laplacian.laplacian φ x)
        ≤ dist w' w * ∫ x, ‖Laplacian.laplacian φ x‖ := key w' w
      _ ≤ dist w' w * ((∫ x, ‖Laplacian.laplacian φ x‖) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
      _ < ε := (lt_div_iff₀ hC1).1 hw'

open scoped Classical in
/-- **Restricted moments of a certificate.** For a locally finite measure `ν`, a nonnegative
continuous test function `D` with compact support, and a predicate `P` on the basis indices such that `U i ⊆ B_1` when
`P i`, the supremum over finite charged families `J` and cutoff levels `n` of the moments `∫ D · θ_{J,n} dν` (on the charged
indices, zero otherwise) is the integral of `D` over the union of the charged balls. -/
theorem sup_charged_moment_eq {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν] {D : ℂ → ℝ} (hD : Continuous D)
    (hDc : HasCompactSupport D) (hD0 : ∀ x, 0 ≤ D x) (U : ℕ → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (P : ℕ → Prop) (hP : ∀ i, P i → U i ⊆ ball (0 : ℂ) 1) :
    (⨆ (J : Finset ℕ) (n : ℕ), if (∀ i ∈ J, P i) then
        ENNReal.ofReal (∫ x, D x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν) else 0) =
      ∫⁻ x in (⋃ i, ⋃ (_ : P i), U i), ENNReal.ofReal (D x) ∂ν := by
  have hB_open : ∀ i, IsOpen (U i ∩ ball (0 : ℂ) 1) := fun i => (hU i).inter isOpen_ball
  have hB_sub : ∀ i, U i ∩ ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) 1 := fun i => inter_subset_right
  have hS : (⋃ i ∈ {i | P i}, U i ∩ ball (0 : ℂ) 1) = ⋃ i, ⋃ (_ : P i), U i := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨i, hi, hx, _⟩
      exact ⟨i, hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, hi, hx, hP i hi hx⟩
  have hint : ∀ J : Finset ℕ, ∀ n : ℕ,
      Integrable (fun x => D x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x) ν := by
    intro J n
    refine Continuous.integrable_of_hasCompactSupport (hD.mul (continuous_cutoffBall _ _)) ?_
    exact hDc.mul_right
  have hterm : ∀ J : Finset ℕ, ∀ n : ℕ,
      ∫⁻ x, ENNReal.ofReal (cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x) * ENNReal.ofReal (D x) ∂ν =
        ENNReal.ofReal (∫ x, D x * cutoffBall (⋃ i ∈ J, U i ∩ ball (0 : ℂ) 1) n x ∂ν) := by
    intro J n
    rw [ofReal_integral_eq_lintegral_ofReal (hint J n)
      (ae_of_all _ fun x => mul_nonneg (hD0 x) (cutoffBall_nonneg _ _ _))]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (cutoffBall_nonneg _ _ _), mul_comm]
  rw [← hS, lintegral_restrict_iUnion_eq_iSup_cutoff (fun i => U i ∩ ball (0 : ℂ) 1) hB_open hB_sub
    {i | P i} (f := fun x => ENNReal.ofReal (D x)) (ENNReal.measurable_ofReal.comp hD.measurable)]
  simp only [hterm]
  apply le_antisymm
  · refine iSup_le fun J => iSup_le fun n => ?_
    split_ifs with h
    · exact le_iSup_of_le ⟨J, fun i hi => h i hi⟩ (le_iSup_of_le n le_rfl)
    · exact zero_le
  · refine iSup_le fun ⟨J, hJ⟩ => iSup_le fun n => ?_
    have hJ' : ∀ i ∈ J, P i := fun i hi => hJ (Finset.mem_coe.2 hi)
    refine le_iSup_of_le J (le_iSup_of_le n ?_)
    simp only [eq_true hJ', ↓reduceIte, le_refl]

end MatedCRT
