import LatticeProb.Analysis.StieltjesInverseTransform
import MatedCRT.FirstPass.Derived.RevuzLintegral
import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.Derived.RevuzFormula

/-!
# Integrals against a good clock as integrals in the time-changed variable

Let `a : ℝ≥0 → ℝ≥0` be a continuous, strictly increasing and unbounded clock. Its Lebesgue–Stieltjes measure is
the image of Lebesgue measure under the right inverse `r ↦ inf {s | r < a s}`, so for every measurable `F ≥ 0`,
`∫_{(x, y]} F da = ∫_{(a x, a y]} F (inf {s | r < a s}) dr`
(`setLIntegral_stieltjesOfNNReal_Ioc_eq_clockInverse`).

For a positive continuous additive functional `A` of planar Brownian motion with a good clock, this applies along
almost every path to `a = A · ω`, whose right inverse is the time change `τ_r = clockInverse A r`. Hence, almost
surely, the integral of `g (B_s)` against `dA_s` over `(0, t]` is the integral of `g (B_{τ_r})` over
`r ∈ (0, A_t]` (`ae_setLIntegral_regularize_Ioc_eq_clockInverse`), and the occupation measure entering the Revuz
measure is the time-changed occupation measure on `(0, A_1]`
(`ae_lintegral_occupationMeasure_eq_clockInverse`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Change of variables for the Stieltjes measure of a good clock.** For a continuous, strictly increasing and
unbounded `a : ℝ≥0 → ℝ≥0` and measurable `F ≥ 0`,
`∫_{(x, y]} F da = ∫_{(a x⁺, a y⁺]} F (inf {s | r⁺ < a s}) dr`. -/
theorem setLIntegral_stieltjesOfNNReal_Ioc_eq_clockInverse {a : ℝ≥0 → ℝ≥0} (hc : Continuous a)
    (hs : StrictMono a) (hu : Tendsto a atTop atTop) {x y : ℝ} {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s in Ioc x y, F s ∂(stieltjesOfNNReal a).measure =
      ∫⁻ r in Ioc (a x.toNNReal : ℝ) (a y.toNNReal), F ((sInf {s | r.toNNReal < a s} : ℝ≥0) : ℝ) := by
  have hf := stieltjesOfNNReal_apply_of_continuous hs.monotone hc
  rw [LatticeProb.lintegral_stieltjes_Ioc_eq_lintegral_clockInverse hc hs hu _ hf hF, hf, hf]

/-- Along a path where the clock `A · ω` is continuous, strictly increasing and unbounded, the integral against
`dA_s` over `(x, y]` is the integral over `r ∈ (A_x, A_y]` at the time change `τ_r = clockInverse A r`. -/
theorem setLIntegral_stieltjes_clock_Ioc_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (hc : Continuous fun t => A t ω) (hs : StrictMono fun t => A t ω)
    (hu : Tendsto (fun t => A t ω) atTop atTop) {x y : ℝ} {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s in Ioc x y, F s ∂(stieltjesOfNNReal fun t => A t ω).measure =
      ∫⁻ r in Ioc (A x.toNNReal ω : ℝ) (A y.toNNReal ω), F (clockInverse A r.toNNReal ω : ℝ) :=
  setLIntegral_stieltjesOfNNReal_Ioc_eq_clockInverse hc hs hu hF

/-- **The integral against a good clock in the time-changed variable.** For a positive continuous additive
functional `A` of planar Brownian motion with a good clock, every start `z`, time `t` and measurable `g ≥ 0`,
almost surely `∫_{(0, t]} g (B_s) dA_s = ∫_{(0, A_t]} g (B_{τ_r}) dr`, where the left side is computed on the
rational-time regularization of `A`. -/
theorem ae_setLIntegral_regularize_Ioc_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∀ᵐ ω ∂planarLaw z,
      ∫⁻ s in Ioc (0 : ℝ) t, g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => regularize A u ω).measure =
        ∫⁻ r in Ioc (0 : ℝ) (A t ω), g (ω (clockInverse A r.toNNReal ω)) := by
  filter_upwards [hA.path z, hG z] with ω hp hg'
  obtain ⟨h0, hc, hm⟩ := hp
  have hreg : (fun u => regularize A u ω) = fun u => A u ω :=
    funext (regularize_eq_of_continuous_monotone hc hm)
  have hF : Measurable fun s : ℝ => g (ω s.toNNReal) :=
    hg.comp (ω.continuous.comp continuous_real_toNNReal).measurable
  rw [hreg, setLIntegral_stieltjes_clock_Ioc_eq_clockInverse hc hg'.1 hg'.2 hF]
  simp [h0]

/-- **The occupation measure of a good clock in the time-changed variable.** For a positive continuous additive
functional `A` of planar Brownian motion with a good clock, every start `z` and measurable `g ≥ 0`, almost surely
the occupation measure entering the Revuz measure integrates `g` to `∫_{(0, A_1]} g (B_{τ_r}) dr`. -/
theorem ae_lintegral_occupationMeasure_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∀ᵐ ω ∂planarLaw z,
      ∫⁻ y, g y ∂occupationMeasure (fun u => regularize A u ω) ω =
        ∫⁻ r in Ioc (0 : ℝ) (A 1 ω), g (ω (clockInverse A r.toNNReal ω)) := by
  filter_upwards [ae_setLIntegral_regularize_Ioc_eq_clockInverse hA hG z 1 hg] with ω hω
  rw [lintegral_occupationMeasure _ ω hg]
  simpa using hω

end MatedCRT
