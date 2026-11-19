import MatedCRT.FirstPass.Derived.ExitTailLimit
import MatedCRT.FirstPass.Derived.NoFlatOfTendstoLaw
import MatedCRT.FirstPass.Derived.MepsSpeedLower

/-!
# A subsequential limit of the interpolated walk laws exits every ball in finite time

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Lemma 7.4: finite exit of the limit.

If the laws of the interpolated quenched walk laws `P̃^{ε_n}(ω)` converge weakly to `ν₂`, then `ν₂`-almost
every `P` satisfies, for every `z` and every radius `r > 0`, that `P(z)` gives mass zero to the paths whose exit
time from `B(0, r)` is infinite.  This is `ExitTailLimit.ae_apply_stayForever_eq_zero_of_tendsto_law` for the
radii `r = n + 1`, with all premises supplied from the uniform-start principle and the reference environments of
the model exactly as in `ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw`.

* `ae_forall_pathExitTime_ne_top_of_tendsto_law_interpWalkLaw`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.ExitTailLimit

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **A subsequential limit of the interpolated walk laws exits every ball in finite time** (BG20, Lemma 7.4),
from the uniform-start invariance principle. -/
theorem ae_forall_pathExitTime_ne_top_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {ν₂ : Measure PathLawFamily}
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) :
    ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : ContinuousPath ℂ | pathExitTime (ball (0 : ℂ) r) f = ⊤} = 0 := by
  have h213 := greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := exitTimeUpperBoundStmt_of_greenKernelUpper
    (greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have h217 : BoundedExitTimeRVStmt := firstPass_2_17 volumeGrowthStmt_holds
  have hc0 := MepsSpeedLower.exists_le_mul_mε_of_uniformStart h213 h214 hN4 hγ hγ2 S hS
  have hall : ∀ᵐ P ∂ν₂, ∀ n : ℕ, ∀ z : ℂ,
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        (stayForever ((n : ℝ) + 1)) = 0 :=
    ae_all_iff.2 fun n => ae_apply_stayForever_eq_zero_of_tendsto_law hEnvS h214 h217 hγ hγ2 hS hη' hae hc0
      hε0 hε hlaw (by positivity)
  filter_upwards [hall] with P hP z r hr
  obtain ⟨n, hn⟩ := exists_nat_ge r
  refine measure_mono_null ?_ (hP n z)
  intro f hf t
  have hf' : pathExitTime (ball (0 : ℂ) r) f = ⊤ := hf
  have hmem : f t ∈ ball (0 : ℂ) r :=
    MatedCRT.TruncatedLaws.mem_of_lt_pathExitTime (by rw [hf']; exact ENNReal.coe_lt_top)
  exact ball_subset_ball (by linarith) hmem

end MatedCRT.FirstPass.Derived
