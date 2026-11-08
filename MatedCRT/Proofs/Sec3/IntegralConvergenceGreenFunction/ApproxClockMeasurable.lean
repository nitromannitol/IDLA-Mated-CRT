import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffMeasurable

/-!
# Lemma 3.4 (item 4): joint measurability of the approximate Liouville clock

For a field `H` of circle averages that is jointly measurable in the environment and the spatial point, the approximate
clock `((ω, b), t) ↦ ∫_0^t ε^{γ²/2} exp(γ H ω (b s)) ds` is jointly measurable in the environment, the continuous path
and the time. The argument: the evaluation `(b, s) ↦ b s` of continuous paths is jointly continuous; the integrand is
then jointly measurable in the parameter and the integration variable; the integral over `(0, t]` is a parametric
integral of a jointly measurable integrand, hence measurable in the parameter (Fubini–Tonelli for strongly measurable
integrands).

Terminology: approximate Liouville clock of the LQG measure (Duplantier–Sheffield; Garban–Rhodes–Vargas, Section 2).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology MarkovProcess
open scoped NNReal

/-- The evaluation `(b, s) ↦ b s` of continuous paths is jointly measurable. -/
theorem measurable_path_eval_pair :
    Measurable fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2 :=
  (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable

/-- **Joint measurability of the approximate clock.** If the field `H` is jointly measurable in `(ω, z)`, the
approximate clock integrals `∫_0^t ε^{γ²/2} exp(γ H ω (b s)) ds` are jointly measurable in `((ω, b), t)`. -/
theorem measurable_clockIntegral {Ω : Type*} [MeasurableSpace Ω] (γ ε : ℝ) (H : Ω → ℂ → ℝ)
    (hH : Measurable fun p : Ω × ℂ => H p.1 p.2) :
    Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
      ∫ s in (0 : ℝ)..(q.2 : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 s.toNNReal)) := by
  -- the path evaluated at the (rounded) integration variable
  have hpath : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ => x.1.1.2 x.2.toNNReal :=
    measurable_path_eval_pair.comp
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_real_toNNReal.comp measurable_snd))
  have hH' : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      H x.1.1.1 (x.1.1.2 x.2.toNNReal) :=
    hH.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hpath)
  have hg : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * H x.1.1.1 (x.1.1.2 x.2.toNNReal)) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hH'))
  -- the integrand restricted to `(0, t]`, as a function of the parameter and the variable
  have hset : MeasurableSet {x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ | x.2 ∈ Ioc (0 : ℝ) (x.1.2 : ℝ)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (NNReal.continuous_coe.measurable.comp (measurable_snd.comp measurable_fst)))
  have hf : Measurable fun x : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      if x.2 ∈ Ioc (0 : ℝ) (x.1.2 : ℝ) then
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * H x.1.1.1 (x.1.1.2 x.2.toNNReal)) else 0 :=
    Measurable.ite hset hg measurable_const
  -- the parametric integral of the indicator integrand
  have hint : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ≥0 =>
      ∫ s : ℝ, (if s ∈ Ioc (0 : ℝ) (q.2 : ℝ) then
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 s.toNNReal)) else 0) := by
    exact (hf.stronglyMeasurable.integral_prod_right').measurable
  have hpt : ∀ q : (Ω × ContinuousPath ℂ) × ℝ≥0,
      ∫ s in (0 : ℝ)..(q.2 : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 s.toNNReal)) =
        ∫ s : ℝ, (if s ∈ Ioc (0 : ℝ) (q.2 : ℝ) then
          ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1.1 (q.1.2 s.toNNReal)) else 0) := by
    intro q
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg q.2),
      ← integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (q.2 : ℝ)))]
    congr 1
    funext s
    simp [Set.indicator_apply]
  have heq := funext hpt
  exact (congrArg (fun f : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ => Measurable f) heq).mpr hint

end MatedCRT
