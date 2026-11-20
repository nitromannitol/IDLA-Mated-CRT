import MatedCRT.FirstPass.Derived.OccupationBallLawL2Bound
import LatticeProb.Prob.VitaliSquareBounded

/-!
# Convergence of the mean occupation integrals under the path law averaged over a disc

Let `ballLaw R = ∫_{B(0, R)} planarLaw z dz`.  If the approximating clocks converge to a clock `G`
under every `planarLaw z`, and the dyadic approximants of the Liouville measure satisfy a ball-mass
bound on `B(0, n + 1)`, then for `f` continuous with `0 ≤ f ≤ K`, vanishing off `B̄(0, n)`, the mean
occupation integrals `∫ X_k d(ballLaw R)` converge to `∫ Φ d(ballLaw R)` for a measurable version
`Φ` of the occupation integral of `G`: Vitali's convergence theorem with the uniform second moment
bound `exists_lintegral_sq_windowOcc_ballLaw_le`.
-/

open MeasureTheory MarkovProcess Set Filter Topology Metric
open HarmonicBalls (lqgClockApprox IsLQGClock planarBrownianMotion)
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Convergence of the mean occupation integrals under the disc law.**  The occupation integrals
`X_k = ∫ f d(occupation measure of the k-th approximating clock)` are `ballLaw R`-uniformly square
integrable, converge in `ballLaw R`-measure to a measurable version `Φ` of the occupation integral of
the limiting clock, hence `∫ X_k d(ballLaw R) → ∫ Φ d(ballLaw R)` and `Φ` is `ballLaw R`-integrable. -/
theorem exists_measurable_tendsto_integral_ballLaw_lqgClock {γ : ℝ} {hE : ℝ → ℂ → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hE (HarmonicBalls.dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hE z F)
    {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hG : IsPCAF planarLaw G)
    (hGF : ∀ z, ∀ᵐ b ∂planarLaw z, ∀ t, (G t b : ℝ) = F b t)
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ hE (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Continuous f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) (R : ℝ) :
    ∃ Φ : ContinuousPath ℂ → ℝ, Measurable Φ ∧
      (∀ z, (fun b => ∫ x, f x ∂occupationMeasure (fun t => G t b) b) =ᵐ[planarLaw z] Φ) ∧
      Integrable Φ (ballLaw R) ∧
      Tendsto (fun k : ℕ => ∫ b, ∫ x, f x ∂occupationMeasure
          (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b ∂ballLaw R) atTop
        (𝓝 (∫ b, Φ b ∂ballLaw R)) := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfK x).1
  obtain ⟨Φ, hΦ, hver, hconv⟩ :=
    exists_measurable_tendstoInMeasure_ballLaw_lqgClock hcont hF hG hGF hf hf0 R
  obtain ⟨B, hB⟩ := exists_lintegral_sq_windowOcc_ballLaw_le (h := hE)
    (fun k => (hcont k).measurable) hβ hC0 hball hf.measurable hfK hfn R
  have e : ∀ (k : ℕ) (b : ContinuousPath ℂ), ∫ x, f x ∂occupationMeasure
      (fun t => lqgClockApproxNN γ hE (HarmonicBalls.dyadicScale k) t b) b =
      (windowOcc (weightedApproxDensity γ hE f k) b).toReal := fun k b =>
    integral_occupationMeasure_lqgClockApproxNN (HarmonicBalls.dyadicScale_pos k).le (hcont k) b
      hf hf0
  have hXm : ∀ k : ℕ, Measurable fun b : ContinuousPath ℂ =>
      (windowOcc (weightedApproxDensity γ hE f k) b).toReal := fun k =>
    (measurable_windowOcc (measurable_weightedApproxDensity (γ := γ) (h := hE) (k := k)
      hf.measurable ((hcont k).measurable))).ennreal_toReal
  have hconv' : TendstoInMeasure (ballLaw R)
      (fun k b => (windowOcc (weightedApproxDensity γ hE f k) b).toReal) atTop Φ := by
    simpa only [e] using hconv
  obtain ⟨hint, htend⟩ := LatticeProb.tendsto_integral_of_tendstoInMeasure_of_lintegral_sq_le
    (μ := ballLaw R) (f := fun k b => (windowOcc (weightedApproxDensity γ hE f k) b).toReal)
    (g := Φ) (K := B) (fun k => (hXm k).aestronglyMeasurable) hB hconv'
  refine ⟨Φ, hΦ, hver, hint, ?_⟩
  simpa only [e] using htend

end MatedCRT.FirstPass.Derived
