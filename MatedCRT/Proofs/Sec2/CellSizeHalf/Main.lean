import MatedCRT.Steps.Sec2.CellSizeHalf
import MatedCRT.Proofs.Sec2.CellSizeHalf.CellModel
import MatedCRT.Proofs.Sec2.VolumeGrowthHalf.Domination
import MatedCRT.Proofs.Infra.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma27
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail

/-!
# The upper half of Lemma 2.8 from Bonanno's GMS19 Lemma 2.7

`cellSizeUpperStmt_of_coneAreaDominates`: the upper cell-diameter bound of Lemma 2.8 (lemma:cell-size-estimate,
line 669), `diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}` for every cell meeting `B_ρ`, with polynomially high probability, from
* Leonardo Bonanno's GMS19 Lemma 2.7 for all segments (`MatedCRTHarmonic.GMSLemma27.lemma27_segments`; adapted from
  Leonardo Bonanno's lean-formalizations, https://github.com/leobon12/lean-formalizations, as ported to
  Lattice-Probability), for the cell model of the environment (`MatedCRTEnv.toCellModel`);
* its inputs: `SegmentsContainBalls` (GHM15 Proposition 3.4 + Remark 3.9, from the mating-of-trees coupling of
  `MatedCRTEnv.IsValid`: `segmentsContainBalls_toCellModel`), `GMCLowerTail γ` (GHM15 Lemma 3.12, proved by Bonanno:
  `MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds`) and `AreaDominatesWholePlaneGFF` (from the step
  `ConeAreaDominatesWholePlaneGFFStep` for the cone field of the environment).

Exponents. Bonanno's Lemma 2.7 holds for every `q ∈ (0, 2/(2+γ)²)` with failure probability `O(ε^α)` for every
`α < α(q, γ) = (q/(2γ²))(1/q − 2 − γ²/2)² − 2q`, and `α(q, γ) > 0` (`lemma27Exponent_pos`). Our exponent is
`q = 2/(2+γ)² − ζ`; it can be `≤ 0` (`ζ ∈ (0, 1)` while `2/(2+γ)² < 1/2`), in which case we apply Bonanno's lemma at
`q₀ = 1/(2+γ)²` and use `ε^{q₀} ≤ 1 ≤ ε^q`; in general `q₀ = max(q, 1/(2+γ)²) ∈ (0, 2/(2+γ)²)` and
`ε^{q₀} ≤ ε^q` for `ε < 1`. Bonanno's cells `η([ε(x−1), εx])` are ours.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 2.8, upper half**, from the cone domination step and Bonanno's GMS19 Lemma 2.7. -/
theorem cellSizeUpperStmt_of_coneAreaDominates (hdom : ConeAreaDominatesWholePlaneGFFStep)
    (𝒮 : SpaceFillingSLEModel) : CellSizeUpperStmt 𝒮 := by
  intro γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
  obtain ⟨H, μ', hH, hμ', hle⟩ := hdom γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hS.isConeField
  have hdomM : MatedCRTHarmonic.GMSLemma27.AreaDominatesWholePlaneGFF (S.toCellModel hS) :=
    ⟨H, μ', hH, hμ', hle⟩
  have hsq : 0 < (2 + γ) ^ 2 := by positivity
  set q : ℝ := 2 / (2 + γ) ^ 2 - ζ with hq
  set q₀ : ℝ := max q (1 / (2 + γ) ^ 2) with hq₀
  have hq₀0 : 0 < q₀ := lt_max_of_lt_right (by positivity)
  have hq₀' : q₀ < 2 / (2 + γ) ^ 2 :=
    max_lt (by rw [hq]; linarith) ((div_lt_div_iff_of_pos_right hsq).mpr (by norm_num))
  have hα := MatedCRTHarmonic.GMSLemma27.lemma27Exponent_pos hγ hq₀0 hq₀'
  obtain ⟨C, hC⟩ := MatedCRTHarmonic.GMSLemma27.lemma27_segments (S.toCellModel hS)
    (segmentsContainBalls_toCellModel hS) (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hdomM hγ
    hq₀0 hq₀' hρ hρ1 (half_lt_self hα)
  refine ⟨MatedCRTHarmonic.GMSLemma27.lemma27Exponent q₀ γ / 2, half_pos hα, C, 1, one_pos,
    fun ε hε0 hε1 => le_trans (measure_mono ?_) (hC ε ⟨hε0, hε1⟩)⟩
  refine compl_subset_compl.mpr fun ω hω k hk => ?_
  have h1 : diam (cell ε (S.η ω) k) ≤ ε ^ q₀ := hω _ _ (le_of_eq (by ring)) hk
  exact h1.trans (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (le_max_left _ _))

/-- **Lemma 2.8, upper half**, from the coupling of the quantum cone with a whole-plane GFF on `B_1`
(`ConeWholePlaneCouplingStep`; the comparison of the LQG measures on `B_1` is proved). -/
theorem cellSizeUpperStmt_of_coupling (h : ConeWholePlaneCouplingStep) (𝒮 : SpaceFillingSLEModel) :
    CellSizeUpperStmt 𝒮 :=
  cellSizeUpperStmt_of_coneAreaDominates (coneAreaDominatesWholePlaneGFFStep_of_coupling h) 𝒮

end MatedCRT
