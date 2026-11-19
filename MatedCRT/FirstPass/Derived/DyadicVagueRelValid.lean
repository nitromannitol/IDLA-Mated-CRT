import MatedCRT.FirstPass.Derived.DyadicVagueRelMeasurable
import MatedCRT.FirstPass.Derived.ConeAreaScaling

/-!
# The dyadic vague-limit relation holds almost surely in a valid environment

In a valid mated-CRT environment `S`, let `H` be a version of the whole-plane field (its pairings agree almost
surely with those of `S.hC`). The circle averages of the coordinates `pairJ ⊤ (H ω)` agree with `S.hcirc ω` at
every positive radius, and the γ-LQG measure `S.μ ω` is the dyadic vague limit of `ε^{γ²/2} e^{γ h_ε(z)} dz`
(the case `R = b = 1` of the area scaling of the quantum cone). Hence, almost surely, `S.μ ω` is the dyadic LQG
limit of the circle averages of the coordinates, and the dyadic vague-limit relation `IsDyadicVagueLimitAlong`
holds along every family of continuous compactly supported test functions, both for `S.μ ω` and for the measure
`(E ω).toMeasure` of LQG data `E` encoding `S.μ ω` almost surely.

## Main statements
* `MatedCRT.MatedCRTEnv.IsValid.ae_isLQGLimit_coordCircleAverage`
* `MatedCRT.MatedCRTEnv.IsValid.ae_isDyadicVagueLimitAlong`
* `MatedCRT.MatedCRTEnv.IsValid.ae_isDyadicVagueLimitAlong_toMeasure`
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

section ValidEnvironment

variable {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ}

/-- In a valid environment, for any version `H` of the field, almost surely the γ-LQG measure `S.μ ω` is the dyadic
LQG limit of the circle averages of the field coordinates `pairJ ⊤ (H ω)`. -/
theorem MatedCRTEnv.IsValid.ae_isLQGLimit_coordCircleAverage (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {H : Ω → LQGMetric.DistC} (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, HarmonicBalls.IsLQGLimit γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) (S.μ ω) := by
  filter_upwards [hS.ae_forall_isLQGLimit_rescaledCircle hγ0 hγ2, hS.ae_coordCircleAverage_eq hH]
    with ω hω hωeq
  have h1 := hω 1 1 one_pos one_pos
  have hc : rescaledCircle γ (S.hcirc ω) 1 1 = S.hcirc ω := by
    funext r z
    simp only [rescaledCircle, one_mul, Complex.ofReal_one, Real.log_one, mul_zero, add_zero, sub_zero]
  have hm : rescaledMeasure (S.μ ω) 1 1 = S.μ ω := by
    simp only [rescaledMeasure, inv_one, ENNReal.ofReal_one, one_smul, Complex.ofReal_one, one_mul,
      Measure.map_id']
  rw [hc, hm] at h1
  refine ⟨h1.isLocallyFiniteMeasure, fun g hg hgc => ?_⟩
  have hk : ∀ k : ℕ,
      HarmonicBalls.lqgApprox γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) (HarmonicBalls.dyadicScale k) =
        HarmonicBalls.lqgApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) := fun k => by
    unfold HarmonicBalls.lqgApprox
    congr 1
    funext z
    rw [hωeq _ (HarmonicBalls.dyadicScale_pos k) z]
  simp only [hk]
  exact h1.tendsto_integral g hg hgc

/-- In a valid environment, for any version `H` of the field and any family of continuous compactly supported test
functions, almost surely the dyadic approximations of the γ-LQG measure of the circle averages of the field
coordinates converge to `S.μ ω` along every test function. -/
theorem MatedCRTEnv.IsValid.ae_isDyadicVagueLimitAlong (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {H : Ω → LQGMetric.DistC} (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {ι : Type*} (f : ι → ℂ → ℝ) (hfc : ∀ i, Continuous (f i)) (hfs : ∀ i, HasCompactSupport (f i)) :
    ∀ᵐ ω ∂S.P, FirstPass.Derived.IsDyadicVagueLimitAlong γ f (LQGMetric.pairJ ⊤ (H ω)) (S.μ ω) := by
  filter_upwards [hS.ae_isLQGLimit_coordCircleAverage hγ0 hγ2 hH] with ω hω i
  exact hω.tendsto_integral (f i) (hfc i) (hfs i)

/-- In a valid environment, for any version `H` of the field, any LQG data `E` encoding `S.μ ω` almost surely, and
any family of continuous compactly supported test functions, almost surely the dyadic vague-limit relation holds
both for `(E ω).toMeasure` and for `S.μ ω`, and `S.μ ω` is locally finite. -/
theorem MatedCRTEnv.IsValid.ae_isDyadicVagueLimitAlong_toMeasure (hS : S.IsValid 𝒮 γ) (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {H : Ω → LQGMetric.DistC} (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → FirstPass.Derived.LQGData}
    (hE : ∀ᵐ ω ∂S.P, FirstPass.Derived.LQGData.toMeasure (E ω) = S.μ ω)
    {ι : Type*} (f : ι → ℂ → ℝ) (hfc : ∀ i, Continuous (f i)) (hfs : ∀ i, HasCompactSupport (f i)) :
    ∀ᵐ ω ∂S.P,
      FirstPass.Derived.IsDyadicVagueLimitAlong γ f (LQGMetric.pairJ ⊤ (H ω))
          (FirstPass.Derived.LQGData.toMeasure (E ω)) ∧
        FirstPass.Derived.IsDyadicVagueLimitAlong γ f (LQGMetric.pairJ ⊤ (H ω)) (S.μ ω) ∧
          IsLocallyFiniteMeasure (S.μ ω) := by
  filter_upwards [hS.ae_isLQGLimit_coordCircleAverage hγ0 hγ2 hH, hE] with ω hω hEω
  have hrel : FirstPass.Derived.IsDyadicVagueLimitAlong γ f (LQGMetric.pairJ ⊤ (H ω)) (S.μ ω) :=
    fun i => hω.tendsto_integral (f i) (hfc i) (hfs i)
  refine ⟨?_, hrel, hω.isLocallyFiniteMeasure⟩
  rw [hEω]
  exact hrel

end ValidEnvironment

end MatedCRT
