import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationCellTail
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ExitTimeTail

/-! Second-moment control of the discrete Green occupation error. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- A finite normalized second moment implies a finite unnormalized moment
when the normalization is strictly positive. -/
theorem exitTimeMoment_ne_top_of_scaled_bound (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (a : ℤ) (c : ℝ≥0) (hc : 0 < c) (C : ℝ≥0∞) (hC : C < ⊤)
    (hbound : (c : ℝ≥0∞) ^ 2 * exitTimeMoment m A a 2 ≤ C) :
    exitTimeMoment m A a 2 ≠ ⊤ := by
  intro htop
  have hcn : (c : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
  rw [htop, ENNReal.mul_top hcn] at hbound
  exact (not_le_of_gt hC) hbound

/-- On a ball, the second moment controls the normalized Green occupation
truncation error for every positive truncation time. -/
theorem normalized_cell_green_error_mul_le_secondMoment
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω)
    (z y : ℂ) (r : ℝ) (f : Ω → ℂ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ w ∈ ball z r, |f ω w| ≤ M) (hε : 0 < ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hmoment : exitTimeMoment (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) 2 ≠ ⊤)
    (hscale : 0 < S.mε ε) (T : ℝ) :
    ENNReal.ofReal T * ENNReal.ofReal |(S.mε ε)⁻¹ *
      (∑' b : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) b * f ω (vertexPoint ε (S.η ω) b)) -
        truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω| ≤
      ENNReal.ofReal M * (((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
        exitTimeMoment (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) 2) := by
  have htail := normalized_cell_green_occupation_tail_le_of_secondMoment S ε ω z y r f M
    hM hf hε hη hp hmoment hscale T
  have hsecond := scaled_exitTime_tail_le_secondMoment (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y)
    (Real.toNNReal (S.mε ε)⁻¹) (ENNReal.ofReal T) ENNReal.ofReal_ne_top
  let tail : ℝ≥0∞ := ∫⁻ x in {x | ENNReal.ofReal T ≤
      ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)},
      ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
  change _ ≤ ENNReal.ofReal M * tail at htail
  change ENNReal.ofReal T * tail ≤ _ at hsecond
  calc
    _ ≤ ENNReal.ofReal T * (ENNReal.ofReal M * tail) := by gcongr
    _ = ENNReal.ofReal M * (ENNReal.ofReal T * tail) := by ac_rfl
    _ ≤ _ := by gcongr

end MatedCRT
