import MatedCRT.FirstPass.Derived.MatingConePairDimension
import MatedCRT.FirstPass.Derived.MatingTriplePointsAssembly
import LatticeProb.Prob.CorrelatedBMSubcriticalDirectPair

/-! # Dimension of cone triple points -/

set_option autoImplicit false

open MeasureTheory
open MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace MatedCRT

/-- The cone triple point dimension bound follows from the direct-pair bound. -/
theorem ghmConeDimInput_derived : GHMConeDimInput := by
  intro γ hγ hγ2 μ hμ
  have hγ0 : 0 < γ := lt_trans (Real.sqrt_pos.2 (by norm_num)) hγ
  have hsq : 2 ≤ γ ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsq0 : 0 < γ ^ 2 := by positivity
  have hd : 0 ≤ 1 - 2 / γ ^ 2 := by
    have hdiv : 2 / γ ^ 2 ≤ 1 := (div_le_one hsq0).2 hsq
    linarith
  let d : ℝ≥0 := ⟨1 - 2 / γ ^ 2, hd⟩
  have hpair := LatticeProb.CorrelatedBM.ae_dimH_direct_excursion_pairs_le_subcritical
    hγ0 hγ2 hμ d (by rfl)
  filter_upwards [hpair] with ω hω
  apply dimH_coneTriplePoints_le_of_pairs ω
  change dimH (coneTriplePairs ω) ≤ ENNReal.ofReal (d : ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact hω

end MatedCRT
