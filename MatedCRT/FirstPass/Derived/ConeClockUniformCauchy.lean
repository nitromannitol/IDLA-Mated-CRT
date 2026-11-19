import MatedCRT.FirstPass.Derived.ConeClockWeightConvergence
import LatticeProb.Analysis.UniformCauchyWeightedPrimitives

/-!
# The cone clock is locally uniformly Cauchy where the whole-plane clock is

The circle averages of the reference cone field are those of a whole-plane field `hcirc` plus the
radial correction `-γ log max(|·|, ε) + ⨍ coneRefField` (`coneRefCircle_eq_add`), so the approximating
cone clock at scale `ε` is the whole-plane clock density integrated against the cone weight
(`lqgClockApprox_coneRefCircle`). Along a path that stays in a closed ball `closedBall a r` with
`r < |a|` on `[0, h]`, the weights converge uniformly on `[0, h]` to a continuous limit
(`tendstoUniformlyOn_coneClockWeight_path`), and the uniformly Cauchy property of weighted primitives
(`LatticeProb.uniformCauchySeqOn_intervalIntegral_mul`) transfers the local uniform Cauchy property
of the dyadic whole-plane clocks to the dyadic cone clocks.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter HarmonicBalls MarkovProcess
open scoped NNReal Topology

/-- **Pathwise transfer.** Let the circle averages `hcirc` be jointly continuous at positive radii and
let `b` stay in `closedBall a r` on `[0, h]` with `r < |a|`. If the dyadic approximations of the
whole-plane LQG clock along `b` are uniformly Cauchy on `[0, h]`, so are those of the cone clock with
circle averages `coneRefCircle γ hcirc w`. -/
theorem uniformCauchySeqOn_coneRefCircle_clock (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    {a : ℂ} {r : ℝ} (hr : r < ‖a‖) {h : ℝ≥0} {b : ContinuousPath ℂ}
    (hb : ∀ t ∈ Icc (0 : ℝ≥0) h, b t ∈ Metric.closedBall a r)
    (hU : UniformCauchySeqOn
      (fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t) atTop (Icc 0 h)) :
    UniformCauchySeqOn
      (fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t)
      atTop (Icc 0 h) := by
  have hε : ∀ k, 0 < HarmonicBalls.dyadicScale k := HarmonicBalls.dyadicScale_pos
  have hεt : Tendsto HarmonicBalls.dyadicScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc0 : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hF : Continuous (coneRefField hcirc w) := continuous_coneRefField hc0 w
  have hδ : 0 < ‖a‖ - r := sub_pos.2 hr
  set f : ℕ → ℝ → ℝ := fun k s => HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * hcirc (HarmonicBalls.dyadicScale k) (b s.toNNReal)) with hfdef
  set v : ℕ → ℝ → ℝ := fun k s =>
    Real.exp (γ * (-γ * Real.log (max ‖b s.toNNReal‖ (HarmonicBalls.dyadicScale k)) +
      Real.circleAverage (coneRefField hcirc w) (b s.toNNReal) (HarmonicBalls.dyadicScale k)))
    with hvdef
  have hA : UniformCauchySeqOn (fun k (x : ℝ) => ∫ s in (0 : ℝ)..x, f k s) atTop
      (Icc 0 (h : ℝ)) :=
    (uniformCauchySeqOn_nnreal_Icc_iff (G := fun k (x : ℝ) => ∫ s in (0 : ℝ)..x, f k s)).1 hU
  have hmain : UniformCauchySeqOn (fun k (x : ℝ) => ∫ s in (0 : ℝ)..x, f k s * v k s) atTop
      (Icc 0 (h : ℝ)) :=
    LatticeProb.uniformCauchySeqOn_intervalIntegral_mul
      (fun k _ => lqgClockDensity_nonneg γ hcirc (hε k) _)
      (fun k => continuous_lqgClockDensity_path γ hc (hε k) b) hA
      (fun k => (continuous_coneClockWeight_path hF γ b (hε k) hδ).1)
      (continuous_coneClockWeight_path hF γ b (hε 0) hδ).2
      (tendstoUniformlyOn_coneClockWeight_path hF γ hr hb hεt)
  have h2 := (uniformCauchySeqOn_nnreal_Icc_iff
    (G := fun k (x : ℝ) => ∫ s in (0 : ℝ)..x, f k s * v k s)).2 hmain
  convert h2 using 1
  funext k t
  exact lqgClockApprox_coneRefCircle γ hcirc w (hε k) b t

/-- **Transfer of the local uniform Cauchy property.** For any start law `μ` and path laws `Q`, if
from `μ`-almost every start the dyadic whole-plane clocks are `Q y`-almost surely uniformly Cauchy on
`[0, h]` whenever the path stays in `closedBall a r` (`r < |a|`) on `[0, h]`, then the same holds for
the dyadic cone clocks with circle averages `coneRefCircle γ hcirc w`. -/
theorem coneRefCircle_localUniformCauchy (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ)
    {μ : Measure ℂ} {Q : ℂ → Measure (ContinuousPath ℂ)}
    (H : ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ → ∀ᵐ y ∂μ, ∀ᵐ b ∂(Q y),
      (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ hcirc (HarmonicBalls.dyadicScale k) b t) atTop (Icc 0 h)) :
    ∀ (h : ℝ≥0) (a : ℂ) (r : ℝ), r < ‖a‖ → ∀ᵐ y ∂μ, ∀ᵐ b ∂(Q y),
      (∀ t ∈ Icc 0 h, b t ∈ Metric.closedBall a r) →
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (coneRefCircle γ hcirc w) (HarmonicBalls.dyadicScale k) b t)
        atTop (Icc 0 h) := by
  intro h a r hr
  filter_upwards [H h a r hr] with y hy
  filter_upwards [hy] with b hb hbin
  exact uniformCauchySeqOn_coneRefCircle_clock γ hc w hr hbin (hb hbin)

end MatedCRT.FirstPass.Derived
