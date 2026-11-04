import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationIntegrable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Truncation

/-! The discrete Green occupation error on a ball. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- A Green sum indexed by a finite vertex set is its finite-set sum. -/
theorem green_occupation_tsum_eq_finset (m : ℤ → ℤ → ℕ) (A C : Set ℤ)
    (hC : C.Finite) (a : ℤ) (g : ℤ → ℝ) :
    (∑' b : C, greenFn m A a b * g b) =
      ∑ b ∈ hC.toFinset, greenFn m A a b * g b := by
  classical
  rw [tsum_subtype C (fun b => greenFn m A a b * g b),
    tsum_eq_sum (s := hC.toFinset) ?_]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Set.indicator_of_mem (hC.mem_toFinset.1 hb)]
  · intro b hb
    exact Set.indicator_of_notMem (fun h => hb (hC.mem_toFinset.2 h)) _

/-- For a finite set of cells meeting a ball, the rescaled Green occupation
error is bounded by the normalized walk exit-time tail. -/
theorem normalized_cell_green_occupation_tail_le {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) (z y : ℂ) (r : ℝ)
    (f : Ω → ℂ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ w ∈ ball z r, |f ω w| ≤ M) (hε : 0 < ε)
    (hη : Continuous (S.η ω))
    (hC : (cellVertices ε (S.η ω) (ball z r)).Finite)
    (hmean : expectedExitTime (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) ≠ ⊤)
    (hscale : 0 < S.mε ε) (T : ℝ) :
    ENNReal.ofReal |(S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
      greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) b * f ω (vertexPoint ε (S.η ω) b)) -
      truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω| ≤
      ENNReal.ofReal M * ∫⁻ x in {x | ENNReal.ofReal T ≤ ENNReal.ofReal (S.mε ε)⁻¹ *
        (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)},
        ENNReal.ofReal (S.mε ε)⁻¹ *
          (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
  classical
  rw [green_occupation_tsum_eq_finset (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) (ball z r))
    (cellVertices ε (S.η ω) (ball z r)) hC
    (vertexOf ε (S.η ω) y) (fun b => f ω (vertexPoint ε (S.η ω) b))]
  unfold truncatedDiscreteOccupation
  apply normalized_green_occupation_tail_le (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) (ball z r)) hC.toFinset ?_
    (vertexOf ε (S.η ω) y) (fun b => f ω (vertexPoint ε (S.η ω) b))
    M hM ?_ hmean (S.mε ε) T hscale
  · intro b hb
    exact hC.mem_toFinset.2 hb.1
  · intro b hb
    exact hf _ (vertexPoint_mem_ball_of_mem_interior hε hη hb)

/-- Integer-valued exit times are bounded by their squares, including at
infinity; hence a finite second moment implies finite expected exit time. -/
theorem expectedExitTime_le_secondMoment (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) :
    expectedExitTime m A a ≤ exitTimeMoment m A a 2 := by
  apply lintegral_mono
  intro x
  cases hτ : vExitTime A x with
  | top => simp [hτ]
  | coe n =>
    cases n with
    | zero => simp [hτ]
    | succ k =>
      have hone : (1 : ℝ≥0∞) ≤ ((k + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.succ_pos k
      simpa [hτ] using (le_self_pow₀ hone (by norm_num : (2 : ℕ) ≠ 0))

/-- For a continuous proper curve, finite second exit-time moment gives the
normalized Green occupation tail estimate on the ball. -/
theorem normalized_cell_green_occupation_tail_le_of_secondMoment
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω)
    (z y : ℂ) (r : ℝ) (f : Ω → ℂ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ w ∈ ball z r, |f ω w| ≤ M) (hε : 0 < ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hmoment : exitTimeMoment (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) 2 ≠ ⊤)
    (hscale : 0 < S.mε ε) (T : ℝ) :
    ENNReal.ofReal |(S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
      greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) b * f ω (vertexPoint ε (S.η ω) b)) -
      truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω| ≤
      ENNReal.ofReal M * ∫⁻ x in {x | ENNReal.ofReal T ≤
        ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
        (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)},
        ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (vExitTime (interiorCellVertices ε (S.η ω) (ball z r)) x : ℝ≥0∞)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
  have hmean : expectedExitTime (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) ≠ ⊤ :=
    ne_of_lt ((expectedExitTime_le_secondMoment _ _ _).trans_lt (lt_top_iff_ne_top.2 hmoment))
  exact normalized_cell_green_occupation_tail_le S ε ω z y r f M hM hf hε hη
    (Tightness.cellVertices_finite hη hp hε isBounded_ball) hmean hscale T

end MatedCRT
