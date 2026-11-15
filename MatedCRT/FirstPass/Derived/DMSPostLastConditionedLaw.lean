import MatedCRT.FirstPass.Derived.DMSPostLastCanonicalLaw
import MatedCRT.FirstPass.Derived.ConeBMConditionedExists
import LatticeProb.Prob.IndependentGoodBrownian
import LatticeProb.Prob.WilliamsUndriftedWeakLimit

/-! # The conditioned Brownian post-last-zero law -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace MatedCRT.Proposed

/-- The post-last-zero construction has the weak-limit conditioned law. -/
theorem dms14Remark44PostLastZeroLaw : DMS14Remark44PostLastZeroLaw := by
  intro γ hγ0 hγ2 Ω mΩ P hP B F hB hF hpath
  let d := MatedCRTHarmonic.MatedCRT.lqgQ γ - γ
  have hd : 0 < d := lqgQ_sub_pos_of_lt_two hγ0 hγ2
  obtain ⟨ν, hν⟩ := MatedCRT.ConeBMConditioned.exists_isBMConditionedPositive hd
  obtain ⟨Ω', mΩ', Q, b, b', hb, hb', hind⟩ :=
    LatticeProb.exists_independent_goodBrownian
  let : MeasurableSpace Ω' := mΩ'
  have hbBrownian : IsBrownianReal b Q := ⟨hb.pre, Filter.Eventually.of_forall hb.cont⟩
  have hb'Brownian : IsBrownianReal b' Q := ⟨hb'.pre, Filter.Eventually.of_forall hb'.cont⟩
  let : IsProbabilityMeasure ν := hν.1
  have hνlim := (MatedCRT.isBMConditionedPositive_pathMap hbBrownian hb.meas hb.cont hν).2
  have hνeq := LatticeProb.weakLimit_eq_undrifted_williamsPostLastPath_law
    hb hb' hd hind ν hνlim
  have haux : Q.map (fun ω => LatticeProb.driftMap (-d)
      (LatticeProb.williamsPostLastPath hb' 1 d ω)) =
      (MarkovProcess.brownianMotion 0).map (postLastPathMap d) := by
    apply map_dmsPostLastZeroPath_eq_canonical hb'Brownian d
    exact Filter.Eventually.of_forall fun ω t => (dmsPostLastZeroPath_eq_williams hb' d ω t).symm
  have htarget := map_dmsPostLastZeroPath_eq_canonical hB d hpath
  have heq : P.map F = ν := htarget.trans (haux.symm.trans hνeq.symm)
  simpa only [heq] using hν

end MatedCRT.Proposed
