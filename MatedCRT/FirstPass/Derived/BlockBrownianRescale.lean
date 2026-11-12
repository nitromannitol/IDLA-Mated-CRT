import MatedCRT.FirstPass.Derived.BlockRunningMinCellsRescale
import MatedCRT.FirstPass.Derived.BlockCellMinInjective

/-!
# Brownian rescaling of the block paths of a correlated Brownian motion

Berestycki–Gwynne (2020), Appendix A, proof of Lemma A.9. For a block `[a + 1, a + N]` of cells of
size `ε` and a coordinate `X = L` or `X = R` of a correlated two-sided Brownian motion, the forward
block path `u ↦ ε^{-1/2} (X (ε a + ε u) - X (ε a))` and the backward block path
`u ↦ ε^{-1/2} (X (ε (a + N) - ε u) - X (ε (a + N)))` are standard Brownian motions on `ℝ≥0`, with
measurable values and continuous paths. The running-minimum cells of the block (of `X`, resp. of its
time reversal on the block) are counted by the unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a
running-minimum time of the forward (resp. backward) block path.

## Main results

* `isBrownianReal_blockForwardPath`, `isBrownianReal_blockBackwardPath`: Brownian scaling;
* `measurable_blockForwardPath`, `continuous_blockForwardPath` and their backward analogues;
* `card_blockRunningMinCells_eq_card_forwardHits`,
  `card_blockRunningMinCells_blockReversal_eq_card_backwardHits`: the counts.
-/

open MeasureTheory ProbabilityTheory Finset MatedCRTHarmonic.MatedCRT

open scoped NNReal

namespace MatedCRT

/-- The forward block path `u ↦ ε^{-1/2} (X_i (s + ε u) - X_i (s))` of the coordinate `i` started at
time `s`. -/
noncomputable def blockForwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) : ℝ≥0 → Path2 → ℝ :=
  fun t ω => (√(ε : ℝ))⁻¹ * shiftedCoordinate i s (ε * t) ω

/-- The backward block path `u ↦ ε^{-1/2} (X_i (s - ε u) - X_i (s))` of the coordinate `i` started
at time `s`. -/
noncomputable def blockBackwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) : ℝ≥0 → Path2 → ℝ :=
  fun t ω => (√(ε : ℝ))⁻¹ * backwardCoordinate i s (ε * t) ω

theorem blockForwardPath_apply (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (t : ℝ≥0) (ω : Path2) :
    blockForwardPath i ε s t ω =
      (√(ε : ℝ))⁻¹ * (lrCoord i (s + (ε : ℝ) * t) ω - lrCoord i s ω) := by
  simp only [blockForwardPath, shiftedCoordinate, NNReal.coe_mul]

theorem blockBackwardPath_apply (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (t : ℝ≥0) (ω : Path2) :
    blockBackwardPath i ε s t ω =
      (√(ε : ℝ))⁻¹ * (lrCoord i (s - (ε : ℝ) * t) ω - lrCoord i s ω) := by
  simp only [blockBackwardPath, backwardCoordinate, NNReal.coe_mul]

/-- Brownian scaling: the forward block path of a correlated Brownian motion is a standard Brownian
motion. -/
theorem isBrownianReal_blockForwardPath {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {ε : ℝ≥0} (hε : ε ≠ 0) (s : ℝ) :
    IsBrownianReal (blockForwardPath i ε s) μ :=
  (shiftedCoordinate_isBrownianReal hμ i s).smul hε

/-- Brownian scaling: the backward block path of a correlated Brownian motion is a standard
Brownian motion. -/
theorem isBrownianReal_blockBackwardPath {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {ε : ℝ≥0} (hε : ε ≠ 0) (s : ℝ) :
    IsBrownianReal (blockBackwardPath i ε s) μ :=
  (backwardCoordinate_isBrownianReal hμ i s).smul hε

theorem measurable_blockForwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (t : ℝ≥0) :
    Measurable (blockForwardPath i ε s t) := by
  show Measurable fun ω => blockForwardPath i ε s t ω
  simp_rw [blockForwardPath_apply]
  exact ((measurable_lrCoord i _).sub (measurable_lrCoord i s)).const_mul _

theorem measurable_blockBackwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (t : ℝ≥0) :
    Measurable (blockBackwardPath i ε s t) := by
  show Measurable fun ω => blockBackwardPath i ε s t ω
  simp_rw [blockBackwardPath_apply]
  exact ((measurable_lrCoord i _).sub (measurable_lrCoord i s)).const_mul _

theorem continuous_blockForwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (ω : Path2) :
    Continuous fun t => blockForwardPath i ε s t ω := by
  simp_rw [blockForwardPath_apply]
  exact continuous_const.mul (((continuous_lrCoord i ω).comp (continuous_const.add
    (continuous_const.mul NNReal.continuous_coe))).sub continuous_const)

theorem continuous_blockBackwardPath (i : Fin 2) (ε : ℝ≥0) (s : ℝ) (ω : Path2) :
    Continuous fun t => blockBackwardPath i ε s t ω := by
  simp_rw [blockBackwardPath_apply]
  exact continuous_const.mul (((continuous_lrCoord i ω).comp (continuous_const.sub
    (continuous_const.mul NNReal.continuous_coe))).sub continuous_const)

open Classical in
/-- The running-minimum cells of the block `[a + 1, a + N]` of the coordinate `X_i` are counted by
the unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a running-minimum time of the forward block
path started at `ε a`. -/
theorem card_blockRunningMinCells_eq_card_forwardHits (i : Fin 2) {ε : ℝ≥0} (hε : 0 < ε)
    (a : ℤ) (N : ℕ) (ω : Path2) :
    #(blockRunningMinCells (ε : ℝ) (fun t => lrCoord i t ω) (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧
        ∀ s ≤ t, blockForwardPath i ε ((ε : ℝ) * a) t ω ≤
          blockForwardPath i ε ((ε : ℝ) * a) s ω) := by
  have hc : 0 < (√(ε : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (NNReal.coe_pos.2 hε))
  refine card_blockRunningMinCells_eq_card_filter (NNReal.coe_pos.2 hε) _ _ a N fun u v => ?_
  rw [blockForwardPath_apply, blockForwardPath_apply, mul_le_mul_iff_right₀ hc,
    sub_le_sub_iff_right]

open Classical in
/-- The running-minimum cells of the time reversal of the coordinate `X_i` on the block
`[a + 1, a + N]` are counted by the unit intervals `[j - 1, j]`, `1 ≤ j ≤ N`, containing a
running-minimum time of the backward block path started at `ε (a + N)`. -/
theorem card_blockRunningMinCells_blockReversal_eq_card_backwardHits (i : Fin 2) {ε : ℝ≥0}
    (hε : 0 < ε) (a : ℤ) (N : ℕ) (ω : Path2) :
    #(blockRunningMinCells (ε : ℝ) (blockReversal (ε : ℝ) (fun t => lrCoord i t ω) (a + 1) (a + N))
        (a + 1) (a + N)) =
      #((Icc 1 N).filter fun j => ∃ t : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) ≤ t ∧ t ≤ j ∧
        ∀ s ≤ t, blockBackwardPath i ε ((ε : ℝ) * ((a + N : ℤ) : ℝ)) t ω ≤
          blockBackwardPath i ε ((ε : ℝ) * ((a + N : ℤ) : ℝ)) s ω) := by
  have hc : 0 < (√(ε : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (NNReal.coe_pos.2 hε))
  refine card_blockRunningMinCells_blockReversal_eq_card_filter (NNReal.coe_pos.2 hε) _ _ a N
    fun u v => ?_
  rw [blockBackwardPath_apply, blockBackwardPath_apply, mul_le_mul_iff_right₀ hc,
    sub_le_sub_iff_right]

end MatedCRT
