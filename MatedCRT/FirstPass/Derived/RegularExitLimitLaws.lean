import MatedCRT.FirstPass.Derived.ClassLawLimitIdentification
import MatedCRT.FirstPass.Derived.ExitTailAllRadiiLimit
import MatedCRT.FirstPass.Derived.ExitClassLowering
import MatedCRT.FirstPass.Derived.RegularExitMixture
import MatedCRT.FirstPass.Derived.MepsTendstoAtTop

/-!
# The stopped class law of a subsequential limit is Brownian at every radius, from countably many starting points

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Lemma 7.4.

Let `ν₂` be a subsequential weak limit of the laws of the interpolated quenched walk laws `P̃^{ε_n}(ω)` and let
`D ⊆ ℂ` be countable.  For `ν₂`-almost every `P`, for every `z ∈ D` and every radius `r > ‖z‖`, the law under `P z`
of the curve class stopped at the exit from `B(0, r)` is the planar Brownian law from `z`.

For a fixed `z` and Lebesgue-almost every `r`, the stopped curve class is `P z`-almost surely continuous
(the limit exits every ball in finite time, `ae_forall_pathExitTime_ne_top_of_tendsto_law_interpWalkLaw`, and
almost every radius is a regular exit radius, `ae_ae_ae_regularExit_ball`), so the class law of the limit is
identified at one such radius `R k ≥ ‖z‖ + k` for each `k`, by `ae_stoppedExitCurve_map_eq_of_ae_continuousAt`.
The law without intervals of constancy
(`ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw`) lets `map_stoppedExitCurve_eq_of_le`
lower the radius from `R k` to any `r ≤ R k`.

* `ae_forall_mem_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The stopped class law of a subsequential limit of interpolated walk laws is Brownian at every radius, for
countably many starting points** (BG20, proof of Lemma 7.4). -/
theorem ae_forall_mem_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (hEnvS : ConeEnvironmentScalingStep 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {ν₂ : Measure PathLawFamily} [IsProbabilityMeasure ν₂]
    (hlaw : ∀ f : PathLawFamily →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂)))
    {D : Set ℂ} (hD : D.Countable) :
    ∀ᵐ P ∂ν₂, ∀ z ∈ D, ∀ r : ℝ, ‖z‖ < r →
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) := by
  have h213 := greenKernelLowerBoundStmt_of_reference_of_forall_gamma hν hν href hU
  have h214 := exitTimeUpperBoundStmt_of_greenKernelUpper
    (greenKernelUpperBoundStmt_of_reference_of_forall_gamma hν href hU)
  have hmε : ∀ᶠ n in atTop, 0 < S.mε (ε n) :=
    (tendsto_mε_atTop_of_uniformStart h213 h214 hN4 hγ hγ2 hS hε0 hε).eventually_gt_atTop 0
  have hflat := ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU
    hγ hγ2 hS hη' hae hε0 hε hlaw
  have hfin := ae_forall_pathExitTime_ne_top_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU
    hγ hγ2 hS hη' hae hε0 hε hlaw
  rw [ae_ball_iff hD]
  intro z _
  have hκ : Measurable fun P : PathLawFamily =>
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) := by
    have h1 : Measurable fun P : PathLawFamily => (P z : ProbabilityMeasure (ContinuousPath ℂ)) :=
      (continuous_eval_const z).measurable
    exact measurable_subtype_coe.comp h1
  have hreg := RegularRadius.ae_ae_ae_regularExit_ball ν₂ _ hκ (fun P => inferInstance)
  have hex : ∀ k : ℕ, ∃ r : ℝ, ‖z‖ + k < r ∧ ∀ᵐ P ∂ν₂,
      ∀ᵐ X : ContinuousPath ℂ ∂((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)),
        MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) r) ⇑X := fun k => by
    by_contra h
    have hsub : Ioi (‖z‖ + k) ⊆ {r : ℝ | ¬ ∀ᵐ P ∂ν₂,
        ∀ᵐ X : ContinuousPath ℂ ∂((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)),
          MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) r) ⇑X} :=
      fun r hr hq => h ⟨r, hr, hq⟩
    have h0 : volume (Ioi (‖z‖ + k)) = 0 := measure_mono_null hsub (ae_iff.1 hreg)
    simp at h0
  choose R hRz hRreg using hex
  have hk : ∀ k : ℕ, ∀ᵐ P ∂ν₂,
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (R k))) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) (R k))) := fun k => by
    have hzr : ‖z‖ < R k := lt_of_le_of_lt (by simp) (hRz k)
    refine ClassLawLimit.ae_stoppedExitCurve_map_eq_of_ae_continuousAt hγ hγ2 hN4 hS hη' hae hε0 hε hmε hlaw
      hzr ?_
    filter_upwards [hfin, hRreg k] with P h1 h2
    have h1' := (measure_eq_zero_iff_ae_notMem.1 (h1 z (R k) (lt_of_le_of_lt (norm_nonneg z) hzr)))
    filter_upwards [h2, h1'] with X hX hX'
    exact MatedCRT.StopAtExitCmp.continuousAt_stoppedExitCurve_of_regularExit isOpen_ball hX' hX
  filter_upwards [ae_all_iff.2 hk, hflat] with P hPk hPf r hr
  obtain ⟨k, hk'⟩ := exists_nat_ge r
  have hrR : r ≤ R k := by
    have := hRz k
    have h0 := norm_nonneg z
    linarith
  exact ExitClassLowering.map_stoppedExitCurve_eq_of_le hrR (lt_of_le_of_lt (by simp) (hRz k)) (hPf z) (hPk k)

end MatedCRT.FirstPass.Derived
