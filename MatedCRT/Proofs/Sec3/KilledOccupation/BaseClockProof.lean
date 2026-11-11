import Mathlib
import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.LBM
import HarmonicBalls.Defs.LQG
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClock
import MatedCRT.Proofs.Sec3.KilledOccupation.Potential

/-!
# The base occupation identity from its literature inputs (Appendix B, step S1: lem:occ-base)

Source: `paper/appendix-occupation-C16.tex`, Lemma lem:occ-base (lines 140-151, eq:occ-base) and its proof
(lines 152-240). The conclusion is `BaseOccupationIdentity` (`BaseClock.lean`).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

/-- Lebesgue measure on the time line `ℝ≥0` of the clocks: the image of Lebesgue measure on `[0, ∞)` under
`Real.toNNReal`. (Mathlib has no `MeasureSpace ℝ≥0`.) -/
noncomputable def lebNN : Measure ℝ≥0 := (volume.restrict (Ici (0 : ℝ))).map Real.toNNReal

/-- Integrals over `Icc 0 s` for `lebNN` are the real integrals over `Ioc 0 s`. -/
theorem lintegral_Icc_lebNN {s : ℝ≥0} {F : ℝ≥0 → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ u in Icc (0 : ℝ≥0) s, F u ∂lebNN = ∫⁻ t in Ioc (0 : ℝ) (s : ℝ), F t.toNNReal := by
  have hset : (Real.toNNReal ⁻¹' Icc (0 : ℝ≥0) s) ∩ Ici (0 : ℝ) = Icc (0 : ℝ) s := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Icc, mem_Ici, zero_le', true_and]
    constructor
    · rintro ⟨h, h0⟩
      exact ⟨h0, Real.toNNReal_le_iff_le_coe.mp h.2⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨Real.toNNReal_nonneg, Real.toNNReal_le_iff_le_coe.mpr h⟩, h0⟩
  rw [lebNN, Measure.restrict_map Real.measurable_toNNReal measurableSet_Icc,
    lintegral_map hF Real.measurable_toNNReal, Measure.restrict_restrict
      (Real.measurable_toNNReal measurableSet_Icc), hset,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

end MatedCRT.KilledOccupation
