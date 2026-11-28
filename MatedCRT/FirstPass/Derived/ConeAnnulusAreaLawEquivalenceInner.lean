import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceSteps
import LatticeProb.Prob.LawAEContinuousDense
import LatticeProb.Gauss.GaussianProcessLawExt
import LatticeProb.Prob.CameronMartinEquivalence

/-!
# The inner radial path of a quantum cone: measurability and absolute continuity of its law

Two steps of the comparison of the laws of the area measures of the two quantum cones on a bounded annulus
(`ConeAnnulusAreaLawEquivalenceSteps.lean`).

* `MatedCRT.brownianPathAEMeasurable`: the path `ω ↦ (t ↦ B_t(ω))` of a Brownian motion is almost everywhere
  measurable for the product σ-algebra of `ℝ≥0 → ℝ`. The coordinates are almost everywhere measurable and the
  paths are almost surely continuous on the separable space `ℝ≥0`, so the path agrees almost surely with a
  limit along a countable dense set of times of measurable versions of the coordinates
  (`LatticeProb.aemeasurable_of_ae_continuous`).
* `MatedCRT.coneInnerPathLaw`: for `T ≥ 0` the law of `t ↦ B_t + α₁ min(t, T)` is absolutely continuous with
  respect to the law of `t ↦ B₀_t + α₂ min(t, T)`. The laws of the paths of two Brownian motions agree
  (a Gaussian law is determined by its mean and covariance, `LatticeProb.gaussianProcess_map_eq_of_mean_cov`),
  and `(α₁ - α₂) min(t, T) = cov[(α₁ - α₂) B_T, B_t]` is the Cameron–Martin direction of the finitely supported
  coefficient vector `(α₁ - α₂) δ_T`, whose shift is equivalent to the law of the process
  (`LatticeProb.gaussian_map_shift_absolutelyContinuous`; Cameron–Martin theorem, Bogachev, *Gaussian
  Measures*, Ch. 2).

The inner radial part of the cone is Definition 4.10 of Duplantier–Miller–Sheffield (arXiv:1409.7055).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT

/-- **Brownian paths are almost everywhere measurable.** -/
theorem brownianPathAEMeasurable : BrownianPathAEMeasurable := by
  intro Ω _ P _ B hB
  exact LatticeProb.aemeasurable_of_ae_continuous (X := fun ω t => B t ω) hB.cont
    fun t => hB.toIsPreBrownianReal.aemeasurable t

/-- The map `b ↦ coneInnerPath α T b` on paths is measurable for the product σ-algebra. -/
theorem measurable_coneInnerPath (α T : ℝ) : Measurable (coneInnerPath α T) :=
  measurable_pi_iff.2 fun t => (measurable_pi_apply t).add_const _

/-- The Cameron–Martin direction of `c δ_s` for a pre-Brownian motion is `t ↦ c min(t, s)`. -/
theorem covShift_single_brownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (c : ℝ) (s t : ℝ≥0) :
    QuantumZipper.CameronMartin.covShift B P (Finsupp.single s c) t = c * min (t : ℝ) (s : ℝ) := by
  by_cases hc : c = 0
  · simp [hc, QuantumZipper.CameronMartin.covShift]
  · simp only [QuantumZipper.CameronMartin.covShift, Finsupp.support_single _ hc,
      Finset.sum_singleton, Finsupp.single_eq_same, QuantumZipper.CameronMartin.covK,
      hB.covariance_eval]
    norm_cast

/-- **The inner radial paths (Cameron–Martin).** For `T ≥ 0` and Brownian motions `B, B₀`, the path
`t ↦ B_t + α₁ min(t, T)` is almost everywhere measurable and its law is absolutely continuous with respect to the
law of `t ↦ B₀_t + α₂ min(t, T)`. -/
theorem coneInnerPathLaw : ConeInnerPathLaw := by
  intro α₁ α₂ T hT Ω _ P _ B B₀ hB hB₀
  have hpath : ∀ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C P → AEMeasurable (fun ω t => C t ω) P :=
    fun C hC => brownianPathAEMeasurable P C hC
  have hprob : IsProbabilityMeasure P := inferInstance
  let B' : ℝ≥0 → Ω → ℝ := fun t => (hB.toIsPreBrownianReal.aemeasurable t).mk (B t)
  have hB'm : ∀ t, Measurable (B' t) := fun t => (hB.toIsPreBrownianReal.aemeasurable t).measurable_mk
  have hB' : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => (hB.toIsPreBrownianReal.aemeasurable t).ae_eq_mk
  have hB'path : Measurable (fun ω t => B' t ω) := measurable_pi_iff.2 hB'm
  have hL : ∀ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C P →
      P.map (fun ω t => C t ω) = P.map (fun ω t => B' t ω) := fun C hC =>
    LatticeProb.gaussianProcess_map_eq_of_mean_cov hC.toIsPreBrownianReal.isGaussianProcess
      hB'.isGaussianProcess
      (fun t => (hC.toIsPreBrownianReal.integral_eval t).trans (hB'.integral_eval t).symm)
      (fun s t => (hC.toIsPreBrownianReal.covariance_eval s t).trans (hB'.covariance_eval s t).symm)
      (hpath C hC) hB'path.aemeasurable
  have key : ∀ (C : ℝ≥0 → Ω → ℝ), IsBrownianReal C P → ∀ α : ℝ,
      P.map (fun ω => coneInnerPath α T (fun t => C t ω)) =
        (P.map (fun ω t => B' t ω)).map (coneInnerPath α T) := by
    intro C hC α
    rw [← hL C hC]
    exact ((AEMeasurable.map_map_of_aemeasurable (measurable_coneInnerPath α T).aemeasurable
      (hpath C hC))).symm
  refine ⟨(measurable_coneInnerPath α₁ T).comp_aemeasurable (hpath B hB), ?_⟩
  rw [key B hB, key B₀ hB₀]
  set L := P.map (fun ω t => B' t ω) with hLdef
  let σ : ℝ≥0 →₀ ℝ := Finsupp.single T.toNNReal (α₁ - α₂)
  have hcm := (LatticeProb.gaussian_map_shift_absolutelyContinuous (X := B')
    hB'.isGaussianProcess hB'm (fun t => hB'.integral_eval t) σ).1
  let h : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := fun b t => b t + (α₁ - α₂) * min (t : ℝ) T
  have hh : Measurable h := measurable_pi_iff.2 fun t => (measurable_pi_apply t).add_const _
  have hshift : (fun ω j => B' j ω + QuantumZipper.CameronMartin.covShift B' P σ j) =
      h ∘ fun ω t => B' t ω := by
    funext ω j
    simp only [σ, covShift_single_brownian hB', Function.comp_apply, h, Real.coe_toNNReal T hT]
  rw [hshift, ← Measure.map_map hh hB'path] at hcm
  have hcomp : coneInnerPath α₁ T = coneInnerPath α₂ T ∘ h := by
    funext b t
    simp only [coneInnerPath, h, Function.comp_apply]
    ring
  rw [hcomp, ← Measure.map_map (measurable_coneInnerPath α₂ T) hh]
  exact LatticeProb.map_absolutelyContinuous_of_absolutelyContinuous hcm (measurable_coneInnerPath α₂ T)

end MatedCRT
