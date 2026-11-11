import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalConeIdentification
import MatedCRT.Proofs.Sec1.EnvironmentScaling.GaussianBandProof

/-!
# Canonical Brownian path assembly

Composition of the completed Brownian exports (`GaussianBandProof.lean`, in particular
`ae_tendsto_div_real_of_isBrownianReal`) with the measurable post-last-zero constructor of
`CanonicalConeIdentification.lean` (`exists_measurable_referenceConeConditionedPath`, line 977).
That constructor took the real-time sublinear growth as the premise `hsub`. Here `hsub` is derived:
for a Brownian motion `B` in the sense of Mathlib (`ProbabilityTheory.IsBrownianReal B P`) with
measurable coordinates `B t`, the measurable continuous-path version of the reference cone process
`referenceConeConditionedPath γ (B · ω)` needs no `hsub` premise and no `GaussianBandStep` premise.

The sublinear growth (the Gaussian tail
bound and the reflection bound for the maximum, followed by Borel-Cantelli) is the argument discharged in
`GaussianBandProof.lean`. The conditioned-law identification written there (the entrance and transition
densities of the conditioned drifted Brownian motion, `env-steps.tex:217-242`, citing DMS Remark 4.4,
pp. 74-75) is not formalized here. It enters only as the explicit hypothesis
`MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw` in the law-identity corollaries. Nothing in this file
identifies that hypothesis with a literal theorem of Duplantier-Miller-Sheffield.

Premises that remain, all displayed in the statements below: `[IsProbabilityMeasure P]`;
`hB : ProbabilityTheory.IsBrownianReal B P`, which carries the almost sure continuity `hB.cont`;
the coordinate measurability `hBm : ∀ t, Measurable (B t)`, which the a.e. measurability of the
HasLaw API does not provide; the positive drift `0 < lqgQ γ - γ` (for the law corollaries, the range
`0 < γ < 2` through `lqgQ_sub_pos_of_lt_two`); and, for the law corollaries only, `hR`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MatedCRT.Sec1

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Measurable continuous-path version of a Brownian motion.** If `B` is a Brownian motion on a
probability space `(Ω, P)` with measurable coordinates, there is a measurable map
`Y : Ω → ContinuousPath ℝ` whose path is almost surely the path of `B`. The full-measure event is
`∀ᵐ ω ∂P, ∀ t, Y ω t = B t ω`. The version is `exists_measurable_continuousPath_version` applied to
the coordinate family: it is the zero path on a measurable null set containing the discontinuous paths,
and each evaluation `ω ↦ Y ω t` is measurable because the coordinates are. The continuity is `hB.cont`. -/
theorem exists_measurable_continuousPath_version_of_isBrownianReal
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∃ Y : Ω → MarkovProcess.ContinuousPath ℝ, Measurable Y ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y ω t = B t ω := by
  have hZB : Measurable (fun ω (t : ℝ≥0) => B t ω) := measurable_pi_iff.mpr fun t => hBm t
  obtain ⟨Y, hY, hYB⟩ := exists_measurable_continuousPath_version (fun ω t => B t ω) hZB hB.cont
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYB] with ω hω t
  exact congrFun hω t

/-- **Measurable reference-cone path, with no supplied sublinear growth.** For a Brownian motion `B`
with measurable coordinates and positive drift `d = lqgQ γ - γ > 0`, there is a measurable
continuous-path version `F` of the reference cone conditioned path `referenceConeConditionedPath γ`,
with full-measure event `∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (B · ω) t`. The real-time
sublinear growth `B t / t → 0` is not assumed: it is `ae_tendsto_div_real_of_isBrownianReal`, the
discharged Gaussian band of `GaussianBandProof.lean`. -/
theorem exists_measurable_referenceConeConditionedPath_of_isBrownianReal
    {γ : ℝ} (hd : 0 < MatedCRTHarmonic.MatedCRT.lqgQ γ - γ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t :=
  exists_measurable_referenceConeConditionedPath hd B hBm hB.cont
    (ae_tendsto_div_real_of_isBrownianReal hB hBm)

/-- **Law identity for the reference cone path, with the Remark 4.4 input retained.** For
`0 < γ < 2` (so the drift `lqgQ γ - γ` is positive) and a Brownian motion `B` with measurable
coordinates, there is a measurable continuous-path version `F` of `referenceConeConditionedPath γ`
whose law is the conditioned positive law `IsBMConditionedPositive (lqgQ γ - γ)`. The law identity is
the explicit hypothesis `hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw`. It is not discharged
here and is not identified with DMS Remark 4.4 as a literal theorem. The sublinear growth is
discharged. -/
theorem exists_referenceConeConditionedPath_law_of_isBrownianReal
    (hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) :=
  exists_referenceConeConditionedPath_law_of_remark44 hR hγ0 hγ2 B hB hBm
    (ae_tendsto_div_real_of_isBrownianReal hB hBm)

/-- **Weak-limit identification of the reference cone path, with the Remark 4.4 input retained.**
Given `hR` as in `exists_referenceConeConditionedPath_law_of_isBrownianReal`, every conditioned
positive law `ν` of drift `lqgQ γ - γ` is the law of a measurable continuous-path version of the
reference cone path built from `B`. Uniqueness of the conditioned positive law is
`isBMConditionedPositive_unique` (Field.lean). The sublinear growth is discharged. -/
theorem exists_referenceConeConditionedPath_map_eq_of_isBrownianReal
    (hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {ν : Measure (MarkovProcess.ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) ν) :
    ∃ F : Ω → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      P.map F = ν :=
  exists_referenceConeConditionedPath_map_eq_of_remark44 hR hγ0 hγ2 B hB hBm
    (ae_tendsto_div_real_of_isBrownianReal hB hBm) hν

end MatedCRT.Sec1
