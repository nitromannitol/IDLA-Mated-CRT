import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Gauss.UncorrelatedIndependence

/-!
# Rotation invariance of planar Brownian motion

Let `μ` be the law of a two-sided standard planar Brownian motion, that is a law on
`Path2 = C(ℝ, ℝ × ℝ)` satisfying `IsCorrelatedBM2 (√2) μ`: its two coordinates are independent
centred Gaussian processes with covariance `twoSidedMin s t` (since `lrCov √2 0 1 = -cos (π / 2) = 0`).
Rotating the path pointwise by a fixed angle `φ` preserves this law.

## Main statements

* `MatedCRT.PlanarBMConePoints.rotatePath`: the pointwise rotation of a planar path by `φ`.
* `MatedCRT.PlanarBMConePoints.continuous_rotatePath`: the rotation is continuous on `Path2`.
* `MatedCRT.PlanarBMConePoints.isCorrelatedBM2_map_rotatePath`: the image of a standard planar
  Brownian law under `rotatePath φ` is again a standard planar Brownian law.

Each coordinate of the rotated path is a linear combination of the two original coordinates at the
same time, so the image process is a centred Gaussian process; its covariance is preserved because
`cos φ ^ 2 + sin φ ^ 2 = 1`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MatedCRT.PlanarBMConePoints

open MatedCRTHarmonic.MatedCRT

/-- The path rotated pointwise by the angle `φ` (clockwise), `ω t ↦ (cos φ x + sin φ y, -sin φ x + cos φ y)`. -/
def rotatePath (φ : ℝ) : Path2 → Path2 := fun ω =>
  ⟨fun t => (Real.cos φ * (ω t).1 + Real.sin φ * (ω t).2, -Real.sin φ * (ω t).1 + Real.cos φ * (ω t).2),
    by fun_prop⟩

/-- The rotation of paths is continuous for the compact-open topology on `Path2`. -/
theorem continuous_rotatePath (φ : ℝ) : Continuous (rotatePath φ) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun p : Path2 × ℝ =>
    ((Real.cos φ * (p.1 p.2).1 + Real.sin φ * (p.1 p.2).2,
      -Real.sin φ * (p.1 p.2).1 + Real.cos φ * (p.1 p.2).2) : ℝ × ℝ)
  fun_prop

/-- The coefficients of the two coordinates of the rotated path in terms of the original ones. -/
private def rotCoef (φ : ℝ) (i : Fin 2) : ℝ × ℝ :=
  if i = 0 then (Real.cos φ, Real.sin φ) else (-Real.sin φ, Real.cos φ)

private lemma lrCoord_rotatePath (φ : ℝ) (i : Fin 2) (t : ℝ) (ω : Path2) :
    lrCoord i t (rotatePath φ ω) =
      (rotCoef φ i).1 * lrCoord 0 t ω + (rotCoef φ i).2 * lrCoord 1 t ω := by
  fin_cases i <;> rfl

private lemma measurable_lrCoord_rotation (i : Fin 2) (t : ℝ) :
    Measurable (fun ω : Path2 => lrCoord i t ω) := by
  unfold lrCoord
  split_ifs
  · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval t)

private lemma covariance_lin_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y X' Y' : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : MemLp X' 2 P) (hY' : MemLp Y' 2 P) (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * X' ω + d * Y' ω; P] =
      a * c * cov[X, X'; P] + a * d * cov[X, Y'; P] + b * c * cov[Y, X'; P] +
        b * d * cov[Y, Y'; P] := by
  have h1 : (fun ω => a * X ω + b * Y ω) = (fun ω => a * X ω) + fun ω => b * Y ω := rfl
  have h2 : (fun ω => c * X' ω + d * Y' ω) = (fun ω => c * X' ω) + fun ω => d * Y' ω := rfl
  rw [h1, h2, covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hX'.const_mul c).add (hY'.const_mul d)),
    covariance_add_right (hX.const_mul a) (hX'.const_mul c) (hY'.const_mul d),
    covariance_add_right (hY.const_mul b) (hX'.const_mul c) (hY'.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

private lemma rotCoef_gram (φ : ℝ) (i j : Fin 2) :
    (rotCoef φ i).1 * (rotCoef φ j).1 + (rotCoef φ i).2 * (rotCoef φ j).2 =
      lrCov (Real.sqrt 2) i j := by
  have hcos : Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4) = 0 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show Real.pi * 2 / 4 = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
  have h := Real.cos_sq_add_sin_sq φ
  fin_cases i <;> fin_cases j
  · show Real.cos φ * Real.cos φ + Real.sin φ * Real.sin φ = 1
    nlinarith
  · show Real.cos φ * -Real.sin φ + Real.sin φ * Real.cos φ = -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4)
    rw [hcos]
    ring
  · show -Real.sin φ * Real.cos φ + Real.cos φ * Real.sin φ = -Real.cos (Real.pi * Real.sqrt 2 ^ 2 / 4)
    rw [hcos]
    ring
  · show -Real.sin φ * -Real.sin φ + Real.cos φ * Real.cos φ = 1
    nlinarith

/-- **Rotation invariance of planar Brownian motion.** The image of the law of a two-sided standard
planar Brownian motion (`IsCorrelatedBM2 (√2) μ`) under the pointwise rotation `rotatePath φ` is the
law of a two-sided standard planar Brownian motion. -/
theorem isCorrelatedBM2_map_rotatePath {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) (φ : ℝ) :
    IsCorrelatedBM2 (Real.sqrt 2) (μ.map (rotatePath φ)) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hΦ : Measurable (rotatePath φ) := (continuous_rotatePath φ).measurable
  have hm := measurable_lrCoord_rotation
  have hL2 : ∀ i t, MemLp (lrCoord i t) 2 μ := fun i t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (i, t)).memLp_two
  have hmem : ∀ p : Fin 2 × ℝ, (fun ω => lrCoord p.1 p.2 (rotatePath φ ω)) ∈
      Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) := by
    intro p
    have hfun : (fun ω => lrCoord p.1 p.2 (rotatePath φ ω)) =
        (rotCoef φ p.1).1 • lrCoord 0 p.2 + (rotCoef φ p.1).2 • lrCoord 1 p.2 := by
      funext ω
      simp only [lrCoord_rotatePath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ((0 : Fin 2), p.2))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ((1 : Fin 2), p.2))))
  have hG : IsGaussianProcess
      (fun (p : Fin 2 × ℝ) (ω : Path2) => lrCoord p.1 p.2 (rotatePath φ ω)) μ :=
    LatticeProb.GaussIndep.isGaussianProcess_of_mem_span hμ.isGaussianProcess hmem
  have hgm : ∀ I : Finset (Fin 2 × ℝ),
      Measurable fun ω : Path2 => I.restrict (fun p : Fin 2 × ℝ => lrCoord p.1 p.2 ω) :=
    fun I => measurable_pi_iff.2 fun j => hm j.1.1 j.1.2
  refine
    { isProbabilityMeasure := (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 ‹_›
      isGaussianProcess := ⟨fun I => ⟨(hgm I).aemeasurable, ?_⟩⟩
      integral_eq_zero := fun i t => ?_
      covariance_eq := fun i j s t => ?_ }
  · rw [Measure.map_map (hgm I) hΦ]
    exact (hG.hasGaussianLaw I).isGaussian_map
  · rw [integral_map hΦ.aemeasurable (hm i t).aestronglyMeasurable]
    simp only [lrCoord_rotatePath]
    rw [integral_add (((hL2 0 t).integrable (by norm_num)).const_mul _)
      (((hL2 1 t).integrable (by norm_num)).const_mul _), integral_const_mul, integral_const_mul,
      hμ.integral_eq_zero, hμ.integral_eq_zero]
    ring
  · rw [covariance_map_fun (hm i s).aestronglyMeasurable (hm j t).aestronglyMeasurable
      hΦ.aemeasurable]
    simp only [lrCoord_rotatePath]
    rw [covariance_lin_comb (hL2 0 s) (hL2 1 s) (hL2 0 t) (hL2 1 t)]
    simp only [hμ.covariance_eq]
    rw [← rotCoef_gram φ i j]
    have h00 : lrCov (Real.sqrt 2) 0 0 = 1 := rfl
    have h11 : lrCov (Real.sqrt 2) 1 1 = 1 := rfl
    have h01 : lrCov (Real.sqrt 2) 0 1 = 0 := by
      rw [← rotCoef_gram 0 0 1]
      simp [rotCoef]
    have h10 : lrCov (Real.sqrt 2) 1 0 = 0 := by
      rw [← rotCoef_gram 0 1 0]
      simp [rotCoef]
    rw [h00, h11, h01, h10]
    ring

end MatedCRT.PlanarBMConePoints
