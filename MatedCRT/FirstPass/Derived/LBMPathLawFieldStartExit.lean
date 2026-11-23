import MatedCRT.FirstPass.Derived.LQGMeasureNeZeroWiring
import MatedCRT.FirstPass.Derived.LBMPathLawFieldDefines
import MatedCRT.FirstPass.Derived.RandomWalkToLBMIdentificationAssembly
import MatedCRT.FirstPass.Derived.LQGDataSpace

/-!
# The rescaled Liouville Brownian motion starts at its starting point and leaves every ball

For `0 < γ < 2`, a valid mated-CRT environment `S` and a measurable version `H` of its field, almost surely, for
every starting point `z`, almost every path under the rescaled Liouville Brownian law `lbmPathLawField γ
(pairJ ⊤ (H ω)) z` starts at `z` and leaves every ball `B(0, R)`, `R ∈ ℕ`
(`ae_forall_ae_lbmPathLawField_start_exit`). The law is the image of planar Brownian motion from `z` under the
time-changed path `u ↦ b (F_ω(b)⁻¹ (m u))` (`MatedCRTEnv.IsValid.ae_lbmLawFieldSelection_eq`); the clock is a
time-change clock (continuous, strictly increasing, from `0`, unbounded), and planar Brownian motion starts at `z`
and leaves every ball.

On a weak limit `ν''` of the joint laws of the field coordinates, a coordinate `E`, the curve and a sequence of
path-law families, the same holds at the random starting point `η(u)` read off the curve, for `ν''`-almost every
sample (`ae_lbmPathLawField_curvePoint_start_exit`): the marginal of `ν''` on the first three coordinates is the
law of (field coordinates, `E`, curve) (`map_fst_eq_map_of_tendsto_integral`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData)

namespace MatedCRT

/-- The set of paths which start at `z` and leave every ball `B(0, R)`, `R ∈ ℕ`, is Borel. -/
theorem measurableSet_start_exit (z : ℂ) :
    MeasurableSet {f : ContinuousPath ℂ | f 0 = z ∧
      ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) f ≠ ⊤} := by
  have h1 : MeasurableSet {f : ContinuousPath ℂ | f 0 = z} :=
    (continuous_eval_const (0 : ℝ≥0)).measurable (measurableSet_singleton z)
  have h2 : MeasurableSet (⋂ R : ℕ, {f : ContinuousPath ℂ |
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) f ≠ ⊤}) :=
    MeasurableSet.iInter fun R =>
      ((ContinuousPath.measurable_exitTime _ Metric.isOpen_ball) (measurableSet_singleton ⊤)).compl
  convert h1.inter h2 using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]

/-- **The rescaled Liouville Brownian motion starts at its starting point and leaves every ball, quenched, for all
starting points.** -/
theorem ae_forall_ae_lbmPathLawField_start_exit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ z : ℂ,
      ∀ᵐ f ∂(lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : Measure (ContinuousPath ℂ)),
        f 0 = z ∧ ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) f ≠ ⊤ := by
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (FirstPass.Derived.lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS)
  have hm : S.m₀ = lbmExitMedian γ := by
    rw [hS.m₀_eq_lawFieldExitMedian hH (measurable_lbmLawFieldSelection_coordCircleGood γ)
      (hΛ.mono fun ω h => h 0), hS.map_pairJ_eq_quantumConeCoordLaw hH hrep, lbmExitMedian]
  set c : ℝ≥0 := (lbmExitMedian γ).toNNReal with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ← hm]
    exact (Real.toNNReal_pos.2 hm0).ne'
  have hmeas : Measurable (LatticeProb.timeScalePath (E := ℂ) c) :=
    (LatticeProb.continuous_timeScalePath _).measurable
  filter_upwards [hΛ, hS.isLQGClock] with ω hω hclock
  intro z
  obtain ⟨hg, hK⟩ := hω z
  have h1 : ((lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      (((lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω)) z :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))).map
        (LatticeProb.timeScalePath c) := by
    rw [lbmPathLawField, rescaledLBMLawField_apply]
    exact ProbabilityMeasure.toMeasure_map _
  have hP : ((lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      (planarBrownianMotion z).map (fun b => LatticeProb.timeScalePath c (lbmContinuousPath (S.clock ω) b)) := by
    rw [h1, hK]
    exact AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hg
  rw [hP]
  refine (ae_map_iff (hmeas.comp_aemeasurable hg) (measurableSet_start_exit z)).2 ?_
  filter_upwards [(hclock z).2, ae_planarBrownianMotion_eval_zero z,
    ae_all_iff.2 fun R : ℕ => ae_planarBrownianMotion_exit_any_ball_lt_top z 0 R] with b hb hb0 hexit
  simp only [Function.comp_apply]
  rw [lbmContinuousPath_of_isTimeChangeClock hb]
  refine ⟨?_, fun R => ?_⟩
  · show b (_root_.HarmonicBalls.clockInverse (S.clock ω b) (c * 0)) = z
    rw [mul_zero, FirstPass.Derived.clockInverse_zero_of_isTimeChangeClock hb, hb0]
  · obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_lt_top_iff (Metric.ball (0 : ℂ) R) b).mp (hexit R)
    let q : ℝ≥0 := Real.toNNReal (S.clock ω b s)
    have hexit' : LatticeProb.timeScalePath c
        ⟨liouvilleBrownianPath (S.clock ω) b, continuous_liouvilleBrownianPath hb⟩ (q / c) ∉
          Metric.ball (0 : ℂ) R := by
      show b (_root_.HarmonicBalls.clockInverse (S.clock ω b) (c * (q / c))) ∉ Metric.ball (0 : ℂ) R
      rw [mul_div_cancel₀ q hc, clockInverse_clockValue hb.map_zero hb.strictMono s]
      exact hs
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top
      (ContinuousPath.exitTime_le_of_notMem _ _ (q / c) hexit')

/-- **At the point `η(u)` of the curve, on the joint limit.** Let `ν''` be a weak limit of the joint laws of the
field coordinates, a measurable coordinate `E`, the curve `η'` and a sequence of path-law families `Z n`. Then for
`ν''`-almost every sample, almost every path under the rescaled Liouville Brownian law of the field from `η(u)`
starts at `η(u)` and leaves every ball `B(0, R)`, `R ∈ ℕ`. -/
theorem ae_lbmPathLawField_curvePoint_start_exit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure ((((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily)}
    [IsProbabilityMeasure ν'']
    (hconv : ∀ f : ((((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)) × PathLawFamily) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν''))) (u : ℝ) :
    ∀ᵐ q ∂ν'', ∀ᵐ f ∂(lbmPathLawField γ q.1.1.1 (q.1.2 u) : Measure (ContinuousPath ℂ)),
      f 0 = q.1.2 u ∧ ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) f ≠ ⊤ := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  have hκP : Measurable fun x : Data => (lbmPathLawField γ x.1.1 (x.2 u) : ProbabilityMeasure (ContinuousPath ℂ)) :=
    continuous_eval.measurable.comp (((measurable_lbmPathLawField γ).comp (measurable_fst.comp measurable_fst)).prodMk
      ((continuous_eval_const u).measurable.comp measurable_snd))
  let κ : Kernel Data (ContinuousPath ℂ) :=
    ⟨fun x => (lbmPathLawField γ x.1.1 (x.2 u) : Measure (ContinuousPath ℂ)), measurable_subtype_coe.comp hκP⟩
  have : IsMarkovKernel κ := ⟨fun x => by
    show IsProbabilityMeasure (lbmPathLawField γ x.1.1 (x.2 u) : Measure (ContinuousPath ℂ))
    infer_instance⟩
  have hT : MeasurableSet {p : Data × ContinuousPath ℂ | ¬ (p.2 0 = p.1.2 u ∧
      ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) p.2 ≠ ⊤)} := by
    have h1 : MeasurableSet {p : Data × ContinuousPath ℂ | p.2 0 = p.1.2 u} :=
      measurableSet_eq_fun ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_snd)
        ((continuous_eval_const u).measurable.comp (measurable_snd.comp measurable_fst))
    have h2 : MeasurableSet (⋂ R : ℕ, {p : Data × ContinuousPath ℂ |
        ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) p.2 ≠ ⊤}) :=
      MeasurableSet.iInter fun R => (((ContinuousPath.measurable_exitTime _ Metric.isOpen_ball).comp
        measurable_snd) (measurableSet_singleton ⊤)).compl
    convert (h1.inter h2).compl using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter]
  have hQ : MeasurableSet {x : Data | κ x (Prod.mk x ⁻¹' {p : Data × ContinuousPath ℂ | ¬ (p.2 0 = p.1.2 u ∧
      ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) p.2 ≠ ⊤)}) = 0} :=
    (Kernel.measurable_kernel_prodMk_left hT) (measurableSet_singleton 0)
  have hsrc : ∀ᵐ x ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)),
      κ x (Prod.mk x ⁻¹' {p : Data × ContinuousPath ℂ | ¬ (p.2 0 = p.1.2 u ∧
        ∀ R : ℕ, ContinuousPath.exitTime (Metric.ball (0 : ℂ) R) p.2 ≠ ⊤)}) = 0 := by
    refine (ae_map_iff hD.aemeasurable hQ).2 ?_
    filter_upwards [ae_forall_ae_lbmPathLawField_start_exit hγ hγ2 hS hH hrep] with ω hω
    exact ae_iff.1 (hω (η' ω u))
  rw [← hmarg] at hsrc
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hsrc] with q hq
  exact ae_iff.2 hq

end MatedCRT
