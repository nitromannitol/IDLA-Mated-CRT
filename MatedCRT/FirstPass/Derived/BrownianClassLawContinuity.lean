import MatedCRT.FirstPass.Derived.WalkClassLevyProkhorovOfGood
import MatedCRT.FirstPass.Derived.StopAtExitLocalUniform
import MatedCRT.FirstPass.Derived.BrownianRegularExitBall
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM

/-!
# Continuity of the stopped Brownian class law in the starting point

For a radius `R` and a starting point `z` in the open disc `ball 0 R`, the law of the class of the Brownian
path from `w`, stopped at the exit of `ball 0 R` (the curve modulo time parametrization), converges in the
Lévy–Prokhorov distance to the one from `z` as `w → z`
(`tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve`).  The proof is a coupling: the path from
`w` is the translate by `w` of the path from `0`; the translates converge locally uniformly, the class map is
continuous at the paths that exit regularly (`continuousAt_stoppedExitCurve_of_regularExit`), and almost every
Brownian path from `z` exits `ball 0 R` regularly (`ae_regularExit_ball_planarBrownian`).  The general step is
that almost sure convergence of measurable maps into a separable metric space gives convergence of the laws in the
Lévy–Prokhorov distance (`tendsto_levyProkhorovDist_map_of_ae_tendsto`).
-/

namespace MatedCRT.BrownianClassLawContinuity

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls
open scoped NNReal ENNReal

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
  [BorelSpace E] [TopologicalSpace.SeparableSpace E] {ι : Type*}

/-- Almost sure convergence of measurable maps implies convergence of their laws in the Lévy–Prokhorov
distance, on a separable metric space. -/
theorem tendsto_levyProkhorovDist_map_of_ae_tendsto {μ : Measure Ω} [IsProbabilityMeasure μ] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → Ω → E} {g : Ω → E} (hf : ∀ i, Measurable (f i))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω))) (hg : Measurable g) :
    Tendsto (fun i => levyProkhorovDist (μ.map (f i)) (μ.map g)) l (𝓝 0) := by
  have key : Tendsto (fun i => (μ.map (f i)).toProbabilityMeasure) l
      (𝓝 (μ.map g).toProbabilityMeasure) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro h
    change Tendsto (fun i => ∫ x, h x ∂(μ.map (f i))) l (𝓝 (∫ x, h x ∂(μ.map g)))
    have e1 : ∀ i, ∫ x, h x ∂(μ.map (f i)) = ∫ ω, h (f i ω) ∂μ := fun i =>
      integral_map (hf i).aemeasurable h.continuous.aestronglyMeasurable
    have e2 : ∫ x, h x ∂(μ.map g) = ∫ ω, h (g ω) ∂μ :=
      integral_map hg.aemeasurable h.continuous.aestronglyMeasurable
    simp only [e1, e2]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖h‖) ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun i => (h.continuous.measurable.comp (hf i)).aestronglyMeasurable
    · exact Eventually.of_forall fun i => ae_of_all _ fun ω => h.norm_coe_le_norm _
    · filter_upwards [hlim] with ω hω using (h.continuous.tendsto _).comp hω
  have h2 := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto
    (μ.map g).toProbabilityMeasure).comp key
  rw [tendsto_iff_dist_tendsto_zero] at h2
  exact h2

end Generic

section Brownian

open MatedCRT.StopAtExitLevyProkhorov MatedCRT.StopAtExitCmp

/-- For fixed `b`, the translate `b + w` depends continuously on `w`, for the topology of locally uniform
convergence. -/
theorem continuous_translatePath_apply (b : ContinuousPath ℂ) :
    Continuous (fun w : ℂ => translatePath w b) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  simp only [translatePath_apply]
  exact (b.continuous.comp continuous_snd).add continuous_fst

/-- **Continuity of the stopped Brownian class law in the starting point.**  For `z` in the open disc
`ball 0 R`, the Lévy–Prokhorov distance, on the space of curves modulo time parametrization, between the class law
of planar Brownian motion from `w` stopped at the exit of `ball 0 R` and the one from `z` tends to `0` as
`w → z`. -/
theorem tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve {R : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    Tendsto (fun w : ℂ => levyProkhorovDist ((planarBrownianMotion w).map (stoppedExitCurve (ball 0 R)))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball 0 R)))) (𝓝 z) (𝓝 0) := by
  have hcls : Measurable (stoppedExitCurve (ball (0 : ℂ) R)) :=
    measurable_stoppedExitCurve _ isOpen_ball
  have hmap : ∀ w : ℂ, (planarBrownianMotion w).map (stoppedExitCurve (ball (0 : ℂ) R)) =
      (planarBrownianMotion 0).map (fun b => stoppedExitCurve (ball (0 : ℂ) R) (translatePath w b)) := by
    intro w
    rw [← map_translatePath_planarBrownianMotion w, Measure.map_map hcls (translatePath w).measurable]
    rfl
  have hae : ∀ᵐ b ∂(planarBrownianMotion 0),
      pathExitTime (ball (0 : ℂ) R) ⇑(translatePath z b) ≠ ⊤ ∧
        MatedCRT.TruncatedLaws.RegularExit (ball (0 : ℂ) R) ⇑(translatePath z b) := by
    have h := ae_regularExit_ball_planarBrownian hz
    rw [← map_translatePath_planarBrownianMotion z] at h
    exact ae_of_ae_map (translatePath z).measurable.aemeasurable h
  have hlim : ∀ᵐ b ∂(planarBrownianMotion 0), Tendsto
      (fun w : ℂ => stoppedExitCurve (ball (0 : ℂ) R) (translatePath w b)) (𝓝 z)
      (𝓝 (stoppedExitCurve (ball (0 : ℂ) R) (translatePath z b))) := by
    filter_upwards [hae] with b hb
    exact (continuousAt_stoppedExitCurve_of_regularExit isOpen_ball hb.1 hb.2).tendsto.comp
      ((continuous_translatePath_apply b).tendsto z)
  have key := tendsto_levyProkhorovDist_map_of_ae_tendsto (μ := planarBrownianMotion 0) (l := 𝓝 z)
    (f := fun (w : ℂ) (b : ContinuousPath ℂ) => stoppedExitCurve (ball (0 : ℂ) R) (translatePath w b))
    (g := fun b => stoppedExitCurve (ball (0 : ℂ) R) (translatePath z b))
    (fun w => hcls.comp (translatePath w).measurable) hlim (hcls.comp (translatePath z).measurable)
  simpa only [hmap] using key

/-- The `ε`-`δ` form of `tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve`. -/
theorem exists_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve_lt {R : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ w : ℂ, dist w z < δ →
      levyProkhorovDist ((planarBrownianMotion w).map (stoppedExitCurve (ball 0 R)))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball 0 R))) < κ := by
  have h := Metric.tendsto_nhds.1
    (tendsto_levyProkhorovDist_planarBrownianMotion_stoppedExitCurve hz) κ hκ
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have := H hw
  rw [Real.dist_eq, sub_zero] at this
  exact (abs_lt.1 this).2

end Brownian

end MatedCRT.BrownianClassLawContinuity
