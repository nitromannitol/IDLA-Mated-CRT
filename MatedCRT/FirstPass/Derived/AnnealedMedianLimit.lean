import MatedCRT.FirstPass.Derived.AnnealedLawWeakConvergence
import MatedCRT.FirstPass.Derived.ExitTimeMedianConvergence

/-!
# The exit-time median of the origin mixture of a weak limit of the annealed walk laws

Let `ε_n → 0` and let `ν` be a joint weak limit of the environment data and of the interpolated quenched laws of the
rescaled random walk on the mated-CRT map, as in `tendsto_annealedPathLaw_probabilityMeasure`.  The annealed laws
`annealedPathLaw S η' ε_n a_n` of the rescaled walks from the vertex `a^{ε_n}_0` of the cell containing the origin then
converge weakly to the origin mixture `originPathLaw ν`.

The lower median of the exit time from `B_{1/2}` of the annealed rescaled walk is `m^interp_ε / m_ε`
(`medianOf_exitCdf_annealedPathLaw`), which tends to `1` as soon as `m_{ε_n} → ∞` (`tendsto_mεInterp_div_mε`).  On the
other hand, if `originPathLaw ν`-almost every path exits `B_{1/2}` regularly and the exit-time distribution function of
`originPathLaw ν` is strictly above `1/2` to the right of its lower median, the lower medians converge to the lower
median of the exit time of the limit (`ExitTimeCdf.tendsto_medianOf_exitCdf`).  Uniqueness of limits gives that the
exit time of the origin mixture from `B_{1/2}` has lower median `1`.
-/

open MeasureTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open MatedCRT.TruncatedLaws (RegularExit)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The exit-time median of the origin mixture of the limit law is one.**  Under the hypotheses of
`tendsto_annealedPathLaw_probabilityMeasure`, if `originPathLaw ν`-almost every path exits `B_{1/2}` regularly, the
exit-time distribution function of `originPathLaw ν` from `B_{1/2}` is strictly above `1/2` to the right of its lower
median, and `m_{ε_n} → ∞`, then the lower median of the exit time of `originPathLaw ν` from `B_{1/2}` equals `1`. -/
theorem medianOf_exitCdf_originPathLaw_eq_one
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {a : ℕ → Ω → ℤ} (ha : ∀ n, Measurable (a n))
    (hav : ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, interpWalkLaw S η' (e n) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hreg : ∀ᵐ g : ContinuousPath ℂ ∂(originPathLaw ν), RegularExit (Metric.ball (0 : ℂ) (1 / 2)) ⇑g)
    (hstrict : ∀ s, medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)) < s →
      (1 / 2 : ℝ≥0∞) < exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν) s)
    (hmε : Tendsto (fun n => S.mε (e n)) atTop atTop) :
    medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)) = 1 := by
  have hlim := tendsto_annealedPathLaw_probabilityMeasure hS hη' hae he0 he hmod ha hav hD hconv
  have h1 := ExitTimeCdf.tendsto_medianOf_exitCdf hlim Metric.isOpen_ball hreg hstrict
  have h2 : Tendsto
      (fun n => medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (annealedPathLaw S η' (e n) (a n))))
      atTop (𝓝 1) := by
    have h3 := (S.tendsto_mεInterp_div_mε (l := map e atTop) (tendsto_map'_iff.2 hmε)).comp
      (tendsto_map : Tendsto e atTop (map e atTop))
    refine h3.congr' ?_
    filter_upwards [hmε.eventually_gt_atTop 0] with n hn
    exact (medianOf_exitCdf_annealedPathLaw hS hη' hae (ha n) (hav n) hn).symm
  exact tendsto_nhds_unique h1 h2

end MatedCRT.FirstPass.Derived
