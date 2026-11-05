import MatedCRT.Steps.Sec2.VolumeGrowthHalf
import MatedCRT.Proofs.Sec2.VolumeGrowthHalf.WholePlane
import MatedCRT.Proofs.Sec2.VolumeGrowthHalf.Domination
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail

/-!
# The lower half of Lemma 2.7 from Bonanno's GMS19 Lemma 2.8

`volumeGrowthLowerStmt_of_coneAreaDominates`: the lower volume bound of Lemma 2.7 (lemma:volume-growth, line 658),
`δ^{β⁻} ≤ μ_h(B_δ(z))` for all `z ∈ B_{1-δ}` with polynomially high probability, for every `β⁻ > (2+γ)²/2`, from
* Leonardo Bonanno's GMS19 Lemma 2.8 (`MatedCRTHarmonic.GMSLemma27.lemma28_wholePlane_strict`, adapted to `B_{1-δ}`
  in `MatedCRT/Proofs/Sec2/VolumeGrowthHalf/WholePlane.lean`) and his proof of the GMC lower tail GHM15 Lemma 3.12
  (`MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds`; adapted from Leonardo Bonanno's lean-formalizations,
  https://github.com/leobon12/lean-formalizations, as ported to Lattice-Probability);
* the step `ConeAreaDominatesWholePlaneGFFStep` (the cone's LQG measure dominates a whole-plane GFF's on `B_1`).

Exponents. With `β⁻ = 2 + γ²/2 + p`, `β⁻ > (2+γ)²/2` is `p > 2γ` (Bonanno's range for GMS19 (2.10)); the
probability of failure is `O(δ^e)` for every `e < p²/(2γ²) − 2`, and `p > 2γ` makes `p²/(2γ²) − 2 > 0`, so
`e = (p²/(2γ²) − 2)/2 > 0` gives polynomially high probability. The paper's `B_{1-δ}` replaces Bonanno's fixed
`B_ρ`, `ρ < 1` (same union bound, see `WholePlane.lean`); "`≤`" in the event of Bonanno's strict form gives our
non-strict `δ^{β⁻} ≤ μ_h(B_δ(z))`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 2.7, lower half**, from the cone domination step and Bonanno's GMS19 Lemma 2.8 and GHM15 Lemma 3.12. -/
theorem volumeGrowthLowerStmt_of_coneAreaDominates (hdom : ConeAreaDominatesWholePlaneGFFStep) :
    VolumeGrowthLowerStmt := by
  intro γ hγ hγ2 βm hβm Ω _ P hC hcirc μ hcone
  have hP : IsProbabilityMeasure P := hcone.1
  obtain ⟨H, μ', hH, hμ', hle⟩ := hdom γ hγ hγ2 Ω P hC hcirc μ hcone
  have hsq : (2 + γ) ^ 2 / 2 = 2 + 2 * γ + γ ^ 2 / 2 := by ring
  set p : ℝ := βm - (2 + γ ^ 2 / 2) with hp
  have hp2 : 2 * γ < p := by rw [hp]; linarith
  have hp0 : 0 < p := by linarith
  have hk : 2 < p ^ 2 / (2 * γ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.2 hp2) (by linarith : 0 < p + 2 * γ)]
  set e : ℝ := (p ^ 2 / (2 * γ ^ 2) - 2) / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have he' : e < p ^ 2 / (2 * γ ^ 2) - 2 := by rw [he]; linarith
  obtain ⟨C, hC⟩ := measure_ball_le_unitBall_of_dominates
    (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hγ hH hμ' hle hp0 he'
  have hβ : 2 + γ ^ 2 / 2 + p = βm := by rw [hp]; ring
  refine ⟨e, he0, C, 1, one_pos, fun δ hδ0 hδ1 => le_trans (measure_mono ?_) (hC δ ⟨hδ0, hδ1⟩)⟩
  intro ω hω
  simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨z, hz, hlt⟩ := hω
  refine ⟨z, hz, ?_⟩
  rw [hβ]
  exact hlt.le

/-- **Lemma 2.7, lower half**, from the coupling of the quantum cone with a whole-plane GFF on `B_1`
(`ConeWholePlaneCouplingStep`); the comparison `μ_{h̃ - γ log |·|} ≥ μ_{h̃}` on `B_1` is proved
(`coneAreaDominatesWholePlaneGFFStep_of_coupling`). -/
theorem volumeGrowthLowerStmt_of_coupling (h : ConeWholePlaneCouplingStep) : VolumeGrowthLowerStmt :=
  volumeGrowthLowerStmt_of_coneAreaDominates (coneAreaDominatesWholePlaneGFFStep_of_coupling h)

end MatedCRT
