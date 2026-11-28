import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeat
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The canonical planar Brownian motion is a planar Brownian motion

`planarBrownianMotion 0` is the law on `ContinuousPath ℂ` of standard planar Brownian motion started
at `0`; it is the image of the product `brownianMotion 0 ⊗ brownianMotion 0` of two real Brownian
laws under `complexPathOfReIm` (`planarBrownianMotion_map_reImPath`).  This file shows that the
canonical process `(t, ω) ↦ ω t` is a planar Brownian motion in the sense of
`LQGMetric.KilledHeat.IsPlanarBM`: the real and imaginary parts are Brownian motions
(`isBrownianReal_comp_hasLaw`), independent of each other, hence jointly Gaussian
(`IndepFun.hasGaussianLaw`), centred, with covariance `min` within a coordinate and `0` across.

## Main results

* `isPlanarBM_canonical`: `IsPlanarBM (fun t ω => ω t) (planarBrownianMotion 0)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal

namespace MatedCRT.PeanosphereTriplePoints

/-- The real part of the canonical process is a Brownian motion under `planarBrownianMotion 0`. -/
lemma isBrownianReal_canonical_re :
    ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => (ω t).re) (planarBrownianMotion 0) := by
  have h := PlanarBrownianSpace.isBrownianReal_comp_hasLaw
    (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub ((0 : ℂ).re)) (PlanarBrownianSpace.hasLaw_re 0)
  simpa [reImPath_fst_apply] using h

/-- The imaginary part of the canonical process is a Brownian motion under
`planarBrownianMotion 0`. -/
lemma isBrownianReal_canonical_im :
    ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => (ω t).im) (planarBrownianMotion 0) := by
  have h := PlanarBrownianSpace.isBrownianReal_comp_hasLaw
    (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub ((0 : ℂ).im)) (PlanarBrownianSpace.hasLaw_im 0)
  simpa [reImPath_snd_apply] using h

/-- Under `planarBrownianMotion 0` the real and imaginary parts of the path are independent. -/
lemma indepFun_canonical_re_im :
    IndepFun (fun b : ContinuousPath ℂ => (reImPath b).1) (fun b => (reImPath b).2)
      (planarBrownianMotion 0) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (PlanarBrownianSpace.hasLaw_re 0).aemeasurable
    (PlanarBrownianSpace.hasLaw_im 0).aemeasurable, (PlanarBrownianSpace.hasLaw_re 0).map_eq,
    (PlanarBrownianSpace.hasLaw_im 0).map_eq]
  exact planarBrownianMotion_map_reImPath 0

/-- The real part at time `s` and the imaginary part at time `r` are independent. -/
lemma indepFun_canonical_eval (s r : ℝ≥0) :
    IndepFun (fun ω : ContinuousPath ℂ => (ω s).re) (fun ω : ContinuousPath ℂ => (ω r).im)
      (planarBrownianMotion 0) := by
  have h := indepFun_canonical_re_im.comp (PlanarBrownianSpace.measurable_eval_path (α := ℝ) s)
    (PlanarBrownianSpace.measurable_eval_path (α := ℝ) r)
  simpa [Function.comp_def, reImPath_fst_apply, reImPath_snd_apply] using h

/-- The real parts of the path at the times of `J`, as a vector. -/
private def reVec (J : Finset ℝ≥0) (ω : ContinuousPath ℂ) : J → ℝ := fun j => (ω j).re

/-- The imaginary parts of the path at the times of `J`, as a vector. -/
private def imVec (J : Finset ℝ≥0) (ω : ContinuousPath ℂ) : J → ℝ := fun j => (ω j).im

/-- `reVec` is the coordinate vector of the real-part path. -/
private lemma reVec_eq (J : Finset ℝ≥0) :
    reVec J = (fun (p : ContinuousPath ℝ) (j : J) => p j) ∘ fun b => (reImPath b).1 := by
  funext ω j
  simp [reVec, reImPath_fst_apply]

/-- `imVec` is the coordinate vector of the imaginary-part path. -/
private lemma imVec_eq (J : Finset ℝ≥0) :
    imVec J = (fun (p : ContinuousPath ℝ) (j : J) => p j) ∘ fun b => (reImPath b).2 := by
  funext ω j
  simp [imVec, reImPath_snd_apply]

/-- Evaluating a path at finitely many times is measurable. -/
private lemma measurable_vec (J : Finset ℝ≥0) :
    Measurable fun (p : ContinuousPath ℝ) (j : J) => p j :=
  measurable_pi_iff.2 fun j => PlanarBrownianSpace.measurable_eval_path (α := ℝ) j

/-- The two coordinates of the canonical process form a Gaussian process indexed by
`Bool × ℝ≥0`. -/
lemma isGaussianProcess_canonical :
    IsGaussianProcess (LQGMetric.KilledHeat.coordProc
      (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t)) (planarBrownianMotion 0) where
  hasGaussianLaw I := by
    classical
    let J : Finset ℝ≥0 := I.image Prod.snd
    have hre : HasGaussianLaw (reVec J) (planarBrownianMotion 0) :=
      isBrownianReal_canonical_re.isGaussianProcess.hasGaussianLaw J
    have him : HasGaussianLaw (imVec J) (planarBrownianMotion 0) :=
      isBrownianReal_canonical_im.isGaussianProcess.hasGaussianLaw J
    have hind : IndepFun (reVec J) (imVec J) (planarBrownianMotion 0) := by
      rw [reVec_eq, imVec_eq]
      exact indepFun_canonical_re_im.comp (measurable_vec J) (measurable_vec J)
    have hG := IndepFun.hasGaussianLaw hre him hind
    let L : ((J → ℝ) × (J → ℝ)) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun i =>
      if i.1.1 = true then
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ)
          ⟨i.1.2, Finset.mem_image_of_mem _ i.2⟩).comp (ContinuousLinearMap.snd ℝ (J → ℝ) (J → ℝ))
      else
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ)
          ⟨i.1.2, Finset.mem_image_of_mem _ i.2⟩).comp (ContinuousLinearMap.fst ℝ (J → ℝ) (J → ℝ))
    have hfun : (fun ω : ContinuousPath ℂ => I.restrict
        (fun p => LQGMetric.KilledHeat.coordProc (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t) p ω)) =
        fun ω => L (reVec J ω, imVec J ω) := by
      funext ω i
      rcases i with ⟨⟨b, t⟩, _⟩
      cases b <;> simp [L, LQGMetric.KilledHeat.coordProc, reVec, imVec, Finset.restrict]
    rw [hfun]
    exact hG.map_fun L

/-- The `false` coordinate of the canonical process is the real part. -/
lemma coordProc_canonical_false (t : ℝ≥0) :
    LQGMetric.KilledHeat.coordProc (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t) (false, t) =
      fun ω => (ω t).re := by
  funext ω; simp [LQGMetric.KilledHeat.coordProc]

/-- The `true` coordinate of the canonical process is the imaginary part. -/
lemma coordProc_canonical_true (t : ℝ≥0) :
    LQGMetric.KilledHeat.coordProc (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t) (true, t) =
      fun ω => (ω t).im := by
  funext ω; simp [LQGMetric.KilledHeat.coordProc]

/-- **The canonical process under `planarBrownianMotion 0` is a planar Brownian motion.** -/
theorem isPlanarBM_canonical :
    LQGMetric.KilledHeat.IsPlanarBM (fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t)
      (planarBrownianMotion 0) where
  cont := Filter.Eventually.of_forall fun ω => ω.continuous
  gauss := isGaussianProcess_canonical
  mean := by
    rintro ⟨b, t⟩
    cases b
    · rw [coordProc_canonical_false]
      exact isBrownianReal_canonical_re.integral_eval t
    · rw [coordProc_canonical_true]
      exact isBrownianReal_canonical_im.integral_eval t
  cov := by
    rintro ⟨b, s⟩ ⟨b', r⟩
    cases b <;> cases b'
    · rw [coordProc_canonical_false, coordProc_canonical_false]
      simpa [NNReal.coe_min] using isBrownianReal_canonical_re.covariance_eval s r
    · rw [coordProc_canonical_false, coordProc_canonical_true]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (indepFun_canonical_eval s r).covariance_eq_zero
        (isBrownianReal_canonical_re.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
        (isBrownianReal_canonical_im.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
    · rw [coordProc_canonical_true, coordProc_canonical_false]
      simp only [Bool.true_eq_false, ↓reduceIte]
      exact (indepFun_canonical_eval r s).symm.covariance_eq_zero
        (isBrownianReal_canonical_im.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
        (isBrownianReal_canonical_re.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
    · rw [coordProc_canonical_true, coordProc_canonical_true]
      simpa [NNReal.coe_min] using isBrownianReal_canonical_im.covariance_eval s r

end MatedCRT.PeanosphereTriplePoints
