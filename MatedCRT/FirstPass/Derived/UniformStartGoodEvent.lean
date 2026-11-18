import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.FirstPass.Derived.StopAtExitWalkBound
import MatedCRT.FirstPass.Derived.ExitTimeCdfConvergence
import MatedCRT.FirstPass.S6j.LitUniformStartInvariance

/-!
# A measurable good event for the uniform-start invariance principle

For a valid environment `S` of the mated-CRT map, a measurable version `η'` of the curve and a sequence `d`
in the separable curve space `BouRabeeGwynne.CurveSpace 2`, the event `goodM S η' d ε R ρ s` collects the
environments for which, from every vertex `x` with `η'(εx) ∈ closedBall 0 ρ`, the interpolated walk exits
`ball 0 R` almost surely and the quenched law of the stopped-curve class landing in each finite union of
the open balls `Metric.eball (d i) (1/(j+1) + s)` is at most the planar Brownian law of the enlarged union
plus `s`.  The event is measurable (`measurableSet_goodM`) because it only involves countably many
measurable functions of the environment; it is the measurable sandwich between the non-measurable
uniform-start events of the invariance principle.
-/

open MeasureTheory ProbabilityTheory Metric Set MarkovProcess HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.UniformStartGood

variable {Ω : Type} [MeasurableSpace Ω]

/-- The finite unions of open balls `B(d i, 1/(j+1) + s)`, `(i, j) ∈ F`, in the curve space. -/
noncomputable def testBall (d : ℕ → BouRabeeGwynne.CurveSpace 2) (s : ℝ) (F : Finset (ℕ × ℕ)) :
    Set (BouRabeeGwynne.CurveSpace 2) :=
  ⋃ p ∈ F, Metric.eball (d p.1) (ENNReal.ofReal (1 / ((p.2 : ℝ) + 1) + s))

theorem isOpen_testBall (d : ℕ → BouRabeeGwynne.CurveSpace 2) (s : ℝ) (F : Finset (ℕ × ℕ)) :
    IsOpen (testBall d s F) :=
  isOpen_biUnion fun _ _ => Metric.isOpen_eball

/-- The measurable good event of the uniform-start invariance principle. -/
def goodM (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (d : ℕ → BouRabeeGwynne.CurveSpace 2)
    (ε R ρ s : ℝ) : Set Ω :=
  {ω | ∀ x : ℤ, η' ω (ε * x) ∈ closedBall (0 : ℂ) ρ →
    srwLaw (S.mult ε ω) x {ξ | pathExitTime (ball (0 : ℂ) R)
        ⇑(interpPathCM (fun k : ℤ => η' ω (ε * k)) zero_le_one ξ) = ⊤} = 0 ∧
    ∀ F : Finset (ℕ × ℕ),
      srwLaw (S.mult ε ω) x {ξ | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R)
          (interpPathCM (fun k : ℤ => η' ω (ε * k)) zero_le_one ξ) ∈ testBall d 0 F} ≤
        planarBrownianMotion (η' ω (ε * x))
          {b | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R) b ∈ testBall d s F} +
        ENNReal.ofReal s}

/-- The quenched law of an event for the interpolated walk is measurable in the environment. -/
theorem measurable_srwLaw_interpPath {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {v : Ω → ℤ → ℂ} (hv : Measurable v) (ε : ℝ) (x : ℤ)
    {E : Set (ContinuousPath ℂ)} (hE : MeasurableSet E) :
    Measurable fun ω => srwLaw (S.mult ε ω) x (interpPathCM (v ω) zero_le_one ⁻¹' E) := by
  have h := (Measure.measurable_coe hE).comp
    (measurable_subtype_coe.comp (measurable_walkPathLaw hS hv zero_le_one ε x))
  convert h using 1
  funext ω
  exact (Measure.map_apply (measurable_interpPathCM (v ω) zero_le_one) hE).symm

/-- The event `goodM` is measurable. -/
theorem measurableSet_goodM {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη : Measurable η')
    (d : ℕ → BouRabeeGwynne.CurveSpace 2) (ε R ρ s : ℝ) :
    MeasurableSet (goodM S η' d ε R ρ s) := by
  have hev : ∀ t : ℝ, Measurable fun ω => η' ω t := fun t =>
    (continuous_eval_const t).measurable.comp hη
  have hv : Measurable fun (ω : Ω) (k : ℤ) => η' ω (ε * k) :=
    measurable_pi_iff.2 fun k => hev _
  have hE1 : MeasurableSet {p : ContinuousPath ℂ | pathExitTime (ball (0 : ℂ) R) ⇑p = ⊤} :=
    (ExitTimeCdf.measurable_pathExitTime isOpen_ball) (measurableSet_singleton ⊤)
  have hE2 : ∀ (s : ℝ) (F : Finset (ℕ × ℕ)), MeasurableSet
      {b : ContinuousPath ℂ | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R) b ∈
        testBall d s F} := fun s F =>
    (StopAtExitLevyProkhorov.measurable_stoppedExitCurve _ isOpen_ball) (isOpen_testBall d s F).measurableSet
  unfold goodM
  simp only [ofPred_forall]
  refine MeasurableSet.iInter fun x => ?_
  have hant : MeasurableSet {ω | η' ω (ε * x) ∈ closedBall (0 : ℂ) ρ} :=
    (hev _) isClosed_closedBall.measurableSet
  have h1 := measurable_srwLaw_interpPath hS hv ε x hE1
  have hA := h1 (measurableSet_singleton 0)
  have hB : ∀ F : Finset (ℕ × ℕ), MeasurableSet
      {ω | srwLaw (S.mult ε ω) x {ξ | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R)
          (interpPathCM (fun k : ℤ => η' ω (ε * k)) zero_le_one ξ) ∈ testBall d 0 F} ≤
        planarBrownianMotion (η' ω (ε * x))
          {b | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R) b ∈ testBall d s F} +
        ENNReal.ofReal s} := fun F => by
    have h2 := measurable_srwLaw_interpPath hS hv ε x (hE2 0 F)
    have h3 : Measurable fun ω => planarBrownianMotion (η' ω (ε * x))
        {b | StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) R) b ∈ testBall d s F} :=
      (Kernel.measurable_coe _ (hE2 s F)).comp (hev _)
    exact measurableSet_le h2 (h3.add measurable_const)
  refine (hant.compl.union (hA.inter (MeasurableSet.iInter hB))).congr ?_
  ext ω
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  exact imp_iff_not_or.symm

end MatedCRT.UniformStartGood
