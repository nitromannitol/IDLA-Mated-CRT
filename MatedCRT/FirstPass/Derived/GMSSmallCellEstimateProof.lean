import MatedCRT.FirstPass.Derived.GMS21ZeroConeQuenchedPolygonal
import LatticeProb.Prob.GMSRealMeshDiameter

/-!
# The small-cell estimate of Gwynne–Miller–Sheffield on closed balls

This file proves `GMSSmallCellEstimate` (`GMS21ZeroConeQuenchedPolygonal.lean`): for every probability law on the
GMS space of cell configurations satisfying the hypotheses of Theorem 1.16 of Gwynne–Miller–Sheffield
(arXiv:1807.07515: mass transport, ergodicity modulo scaling, the finite expectation (1.5) and connectedness along
horizontal and vertical lines), almost surely the maximal diameter of the cells meeting the closed ball `B̄_R(0)` is
`o(R)` as `R → ∞` (arXiv:1807.07515, Lemmas 2.8-2.9).

We follow the written answer `notes/fp-gaps/CODEX-MQ-sbl-36.md`, "Transfer to the coded estimate" (lines 23-33): the
law is transported to the coded environments of the reflected invariance principle by the Borel slot map
`GMS.codeMap`, the mass transport and the finite rooted-energy moment pass to the coded law, the coded large-cell
theorem `ReflectedGMS.Spatial.ae_maxDiamHittingBall_finite_and_sublinear` applies there, and its conull event is
pulled back through the cell bijection. This chain is `LatticeProb.GMSRealMeshDiameter.ae_scaled_cell_diam_lt`
(Lattice-Probability), whose conclusion is the uniform smallness of the cells of the configuration rescaled by every
small mesh `ε`, at the points of a fixed ball. At the mesh `ε = R⁻¹` and the unit ball it is the closed-ball estimate.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter

noncomputable section

namespace MatedCRT.GMS310Transfer

/-- **The small-cell estimate of Gwynne–Miller–Sheffield** (arXiv:1807.07515, Lemmas 2.8-2.9; written answer
`notes/fp-gaps/CODEX-MQ-sbl-36.md`): for every probability law on the GMS space with mass transport, ergodicity modulo
scaling, finite expectation and connectedness along lines, almost surely, for every `r > 0`, for all large `R`, every
cell meeting `B̄_R(0)` has diameter at most `r R`. A cell meeting `B̄_R(0)` at `x` contains `ε⁻¹ z` for `ε = R⁻¹` and
`z = R⁻¹ x` in the unit ball, so the rescaled-cell estimate `ae_scaled_cell_diam_lt` at the unit ball bounds
`R⁻¹ diam K` by `r` as soon as `R⁻¹` is below its threshold. -/
theorem gmsSmallCellEstimate : GMSSmallCellEstimate := by
  intro μ _ hMT _ hFE hL
  filter_upwards [LatticeProb.GMSRealMeshDiameter.ae_scaled_cell_diam_lt hL hMT hFE] with H hH
  intro r hr
  obtain ⟨ε₀, hε₀, hb⟩ := hH 1 r hr
  refine ⟨2 / ε₀, div_pos two_pos hε₀, fun R hR K hK => ?_⟩
  obtain ⟨x, hxK, hxR⟩ := hK
  have hRpos : 0 < R := (div_pos two_pos hε₀).trans_le hR
  have hRinv : 0 < R⁻¹ := inv_pos.2 hRpos
  have hεR : R⁻¹ < ε₀ := by
    have h1 : 2 ≤ R * ε₀ := (div_le_iff₀ hε₀).1 hR
    have h2 : R⁻¹ * 2 ≤ R⁻¹ * (R * ε₀) := mul_le_mul_of_nonneg_left h1 hRinv.le
    rw [← mul_assoc, inv_mul_cancel₀ hRpos.ne', one_mul] at h2
    linarith
  have h : R⁻¹ * Metric.diam ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) < r := by
    refine hb R⁻¹ hRinv hεR (R⁻¹ • x) ?_ K.1 K.2 ?_
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hRinv]
      have hx' := mem_closedBall_zero_iff.1 hxR
      calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx' hRinv.le
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    · rw [inv_inv, smul_smul, mul_inv_cancel₀ hRpos.ne', one_smul]
      exact hxK
  have h3 := mul_lt_mul_of_pos_left h hRpos
  rw [← mul_assoc, mul_inv_cancel₀ hRpos.ne', one_mul] at h3
  linarith

end MatedCRT.GMS310Transfer
