import MatedCRT.FirstPass.Derived.RegularExitLimitLaws
import MatedCRT.FirstPass.Derived.BrownianClassLawContinuity

/-!
# The stopped class law of a subsequential limit is Brownian at every starting point and every radius

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), proof of Lemma 7.4.

A continuous family `z ↦ P z` of laws of continuous planar paths such that, for a dense set `D` of starting points,
`P w` stopped at the exit from `B(0, r)` has the planar Brownian class law for `w ∈ D` and `r > ‖w‖`, and such that
`P w` gives mass zero to the paths that exit no ball in finite time and to the paths with an interval of constancy,
has the planar Brownian class law at every starting point `z` and every radius `r > ‖z‖`.  One chooses a radius `r' ≥ r`
at which `P z` almost surely exits regularly; at `r'` the stopped curve class is `P z`-almost surely continuous, so
the Lévy–Prokhorov distance of the class law of `P w` from that of Brownian motion from `z` is continuous in `w` at
`z`, while for `w ∈ D` it equals that of Brownian motion from `w`, which tends to zero; finally the radius is lowered
from `r'` to `r`.

* `map_stoppedExitCurve_eq_of_dense`: the deterministic statement;
* `ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw`: for `ν₂`-almost every `P`, for every `z` and
  every `r > ‖z‖`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT MatedCRT.StopAtExitLevyProkhorov

namespace MatedCRT.ClassLawLimit

/-- For every s-finite law of paths and every `a` there is a radius `r' > a` at which the law exits regularly. -/
theorem exists_regularRadius_gt (μ : Measure (ContinuousPath ℂ)) [SFinite μ] (a : ℝ) :
    ∃ r' : ℝ, a < r' ∧ ∀ᵐ X : ContinuousPath ℂ ∂μ,
      MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) r') ⇑X := by
  by_contra h
  have hsub : Ioi a ⊆ {r : ℝ | ¬ ∀ᵐ X : ContinuousPath ℂ ∂μ,
      MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) r) ⇑X} := fun r hr hq => h ⟨r, hr, hq⟩
  have h0 : volume (Ioi a) = 0 :=
    measure_mono_null hsub (ae_iff.1 (RegularRadius.ae_ae_regularExit_ball μ))
  simp at h0

/-- **The stopped class law is Brownian at every starting point and radius, from a dense set of starting
points.** -/
theorem map_stoppedExitCurve_eq_of_dense {P : C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} {D : Set ℂ}
    (hD : Dense D)
    (hDeq : ∀ w ∈ D, ∀ r : ℝ, ‖w‖ < r →
      ((P w : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion w).map (stoppedExitCurve (ball (0 : ℂ) r)))
    (hfin : ∀ w : ℂ, ∀ r : ℝ, 0 < r →
      ((P w : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : ContinuousPath ℂ | pathExitTime (ball (0 : ℂ) r) f = ⊤} = 0)
    (hflat : ∀ w : ℂ,
      ((P w : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))
        {f : ContinuousPath ℂ | ∃ s t : ℝ≥0, s < t ∧ ∀ u, s ≤ u → u ≤ t → f u = f s} = 0)
    {z : ℂ} {r : ℝ} (hzr : ‖z‖ < r) :
    ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
        (stoppedExitCurve (ball (0 : ℂ) r)) =
      (planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) r)) := by
  obtain ⟨r', hr'r, hreg⟩ := exists_regularRadius_gt
    ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) r
  have hzr' : ‖z‖ < r' := hzr.trans hr'r
  have hr'pos : 0 < r' := lt_of_le_of_lt (norm_nonneg z) hzr'
  refine ExitClassLowering.map_stoppedExitCurve_eq_of_le hr'r.le hzr' (hflat z) ?_
  have hmeas := measurable_stoppedExitCurve (ball (0 : ℂ) r') isOpen_ball
  let ν₀ : ProbabilityMeasure (BouRabeeGwynne.CurveSpace 2) :=
    ⟨(planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) r')),
      inferInstance⟩
  have hc : ∀ᵐ a ∂((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)),
      ContinuousAt (stoppedExitCurve (ball (0 : ℂ) r')) a := by
    filter_upwards [hreg, measure_eq_zero_iff_ae_notMem.1 (hfin z r' hr'pos)] with X hX hX'
    exact MatedCRT.StopAtExitCmp.continuousAt_stoppedExitCurve_of_regularExit isOpen_ball hX' hX
  have hF : ContinuousAt (fun w : ℂ => levyProkhorovDist
      (((P w : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
        (stoppedExitCurve (ball (0 : ℂ) r'))) (ν₀ : Measure (BouRabeeGwynne.CurveSpace 2))) z :=
    (continuousAt_levyProkhorovDist_map hmeas ν₀ (P z) hc).comp P.continuous.continuousAt
  have hG := BrownianClassLawContinuity.tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve
    (mem_ball_zero_iff.2 hzr')
  have : (𝓝[D] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hD z)
  have hev : (fun w : ℂ => levyProkhorovDist
      (((P w : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
        (stoppedExitCurve (ball (0 : ℂ) r'))) (ν₀ : Measure (BouRabeeGwynne.CurveSpace 2))) =ᶠ[𝓝[D] z]
      fun w : ℂ => levyProkhorovDist ((planarBrownianMotion w).map (stoppedExitCurve (ball (0 : ℂ) r')))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) r'))) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds
      (mem_ball_zero_iff.2 hzr'))] with w hwD hw
    simp only [hDeq w hwD r' (mem_ball_zero_iff.1 hw)]
    rfl
  have h0 := tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
    ((hG.mono_left nhdsWithin_le_nhds).congr' hev.symm)
  have hd : dist (LevyProkhorov.ofMeasure
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)).map (stoppedExitCurve (ball (0 : ℂ) r'))))
      (LevyProkhorov.ofMeasure ν₀) = 0 := h0
  have h2' := dist_eq_zero.1 hd
  have h2 : (P z : ProbabilityMeasure (ContinuousPath ℂ)).map (stoppedExitCurve (ball (0 : ℂ) r')) = ν₀ := by
    simpa using congrArg LevyProkhorov.toMeasure h2'
  exact congrArg (fun m : ProbabilityMeasure (BouRabeeGwynne.CurveSpace 2) => (m : Measure (BouRabeeGwynne.CurveSpace 2))) h2

end MatedCRT.ClassLawLimit

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The stopped class law of a subsequential limit of interpolated walk laws is Brownian at every starting
point and every radius** (BG20, Lemma 7.4). For `ν₂`-almost every `P`, for every `z` and every `r > ‖z‖`, the law
under `P z` of the curve class stopped at the exit from `B(0, r)` is the planar Brownian law from `z`. -/
theorem ae_forall_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw {𝒮 : SpaceFillingSLEModel}
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
      Tendsto (fun n => ∫ ω, f (interpWalkLaw S η' (ε n) ω) ∂S.P) atTop (𝓝 (∫ P, f P ∂ν₂))) :
    ∀ᵐ P ∂ν₂, ∀ z : ℂ, ∀ r : ℝ, ‖z‖ < r →
      ((P z : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) =
        (planarBrownianMotion z).map
          (MatedCRT.StopAtExitLevyProkhorov.stoppedExitCurve (ball (0 : ℂ) r)) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have h1 := ae_forall_mem_map_stoppedExitCurve_eq_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU hγ hγ2
    hS hη' hae hε0 hε hlaw hDc
  have h2 := ae_forall_pathExitTime_ne_top_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU hγ hγ2
    hS hη' hae hε0 hε hlaw
  have h3 := ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw hEnvS hN4 hν href hU
    hγ hγ2 hS hη' hae hε0 hε hlaw
  filter_upwards [h1, h2, h3] with P hP1 hP2 hP3 z r hzr
  exact ClassLawLimit.map_stoppedExitCurve_eq_of_dense hDd hP1 (fun w r hr => hP2 w r hr) hP3 hzr

end MatedCRT.FirstPass.Derived
