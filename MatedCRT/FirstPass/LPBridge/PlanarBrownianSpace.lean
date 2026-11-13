import Mathlib
import LatticeProb.Prob.BrownianExit
import HarmonicBalls.Defs.Brownian
import MarkovProcess.Examples.BrownianMotion

/-!
# Planar Brownian motion at half speed is a Brownian motion on `ℝ²` with generator `Δ / 4`

`planarBrownianMotion z` is standard planar Brownian motion started from `z` (generator `Δ / 2`):
its real and imaginary parts are independent standard real Brownian motions. Run at half speed and
recentred at `z`, and written in the orthonormal basis `1, i` of `ℂ`, it is a Brownian motion on
`EuclideanSpace ℝ (Fin 2)` started at `0` in the sense of Lattice-Probability's
`LatticeProb.IsBrownianSpace 2 0`: each coordinate multiplied by `√2` is a standard real Brownian
motion (Mathlib's `ProbabilityTheory.IsBrownianReal`), and the two coordinate processes are
independent.

The coordinate map `toEuclid` is a linear isometry, so norms of the half-speed path are norms of
the planar path (`norm_halfSpeedPath`), and the displacement times of the two paths agree after
the time change `t ↦ t / 2`.

## Main statements
* `isBrownianReal_brownianMotion_sub`: MarkovProcess's real Brownian motion started from `x`,
  recentred at `x`, is a Brownian motion in Mathlib's sense.
* `isBrownianReal_comp_hasLaw`: Brownian motion is transported along a map with the right law.
* `isBrownianSpace_halfSpeedPath`: the bridge `planarBrownianMotion z ↦ IsBrownianSpace 2 0`.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls
open scoped NNReal

namespace MatedCRT.PlanarBrownianSpace

/-- The coordinates of `w ∈ ℂ` in the orthonormal basis `1, i` of `ℂ` over `ℝ`. -/
noncomputable abbrev toEuclid : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- Planar path recentred at `z` and run at half speed, in the coordinates `toEuclid`:
`t ↦ toEuclid (b (t / 2) - z)`. -/
noncomputable def halfSpeedPath (z : ℂ) (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) :
    EuclideanSpace ℝ (Fin 2) :=
  toEuclid (b (2⁻¹ * t) - z)

lemma halfSpeedPath_zero (z : ℂ) (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) :
    halfSpeedPath z t b 0 = (b (2⁻¹ * t)).re - z.re := by
  simp [halfSpeedPath, toEuclid, Complex.orthonormalBasisOneI_repr_apply]

lemma halfSpeedPath_one (z : ℂ) (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) :
    halfSpeedPath z t b 1 = (b (2⁻¹ * t)).im - z.im := by
  simp [halfSpeedPath, toEuclid, Complex.orthonormalBasisOneI_repr_apply]

/-- The half-speed path has the norms of the planar path. -/
lemma norm_halfSpeedPath (z : ℂ) (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) :
    ‖halfSpeedPath z t b‖ = ‖b (2⁻¹ * t) - z‖ :=
  toEuclid.norm_map _

/-- MarkovProcess's real Brownian motion started from `x`, recentred at `x`, is a Brownian motion
in Mathlib's sense: Gaussian marginals and independent increments give the finite-dimensional
laws (`HasIndepIncrements.isPreBrownianReal_of_hasLaw`). -/
lemma isBrownianReal_brownianMotion_sub (x : ℝ) :
    ProbabilityTheory.IsBrownianReal
      (fun (t : ℝ≥0) (ω : MarkovProcess.ContinuousPath ℝ) => ω t - x)
      (MarkovProcess.brownianMotion x) :=
  ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw
      (MarkovProcess.isBrownianReal_brownianMotion x).hasLaw_eval
      (MarkovProcess.isBrownianReal_brownianMotion x).hasIndepIncrements,
    (MarkovProcess.isBrownianReal_brownianMotion x).cont⟩

/-- A Brownian motion `X` under `Q`, read through a map `Y` whose law under `P` is `Q`, is a
Brownian motion under `P`. -/
lemma isBrownianReal_comp_hasLaw {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : ℝ≥0 → Ω' → ℝ}
    (hX : ProbabilityTheory.IsBrownianReal X Q) {Y : Ω → Ω'} (hY : HasLaw Y Q P) :
    ProbabilityTheory.IsBrownianReal (fun t ω => X t (Y ω)) P where
  hasLaw I := (hX.hasLaw I).comp hY
  cont := by
    have h := hX.cont
    rw [← hY.map_eq] at h
    exact ae_of_ae_map hY.aemeasurable h

/-- Two independent random variables indexed by `Fin 2` are mutually independent. (The same
argument as the generic lemma `iIndepFun_fin_two` of the reflected-walk development.) -/
private lemma iIndepFun_fin_two' {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin 2 → Ω → β} (hX : ∀ i, Measurable (X i))
    (h : IndepFun (X 0) (X 1) P) : iIndepFun X P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hX, Measure.infinitePi_eq_pi]
  apply (MeasurableEquiv.piFinTwo fun _ : Fin 2 => β).map_measurableEquiv_injective
  rw [(measurePreserving_piFinTwo fun i => P.map (X i)).map_eq,
    Measure.map_map (MeasurableEquiv.measurable _) (measurable_pi_iff.2 hX)]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hX 0).aemeasurable (hX 1).aemeasurable).1 h

lemma measurable_eval_path {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (t : ℝ≥0) : Measurable fun b : MarkovProcess.ContinuousPath α => b t :=
  (continuous_eval_const t).measurable

/-- The real part of planar Brownian motion started from `z` has the law of real Brownian motion
started from `Re z`. -/
lemma hasLaw_re (z : ℂ) :
    HasLaw (fun b : MarkovProcess.ContinuousPath ℂ => (reImPath b).1)
      (MarkovProcess.brownianMotion z.re) (planarBrownianMotion z) :=
  ⟨(measurable_fst.comp measurable_reImPath).aemeasurable, planarBrownianMotion_map_re z⟩

/-- The imaginary part of planar Brownian motion started from `z` has the law of real Brownian
motion started from `Im z`. -/
lemma hasLaw_im (z : ℂ) :
    HasLaw (fun b : MarkovProcess.ContinuousPath ℂ => (reImPath b).2)
      (MarkovProcess.brownianMotion z.im) (planarBrownianMotion z) :=
  ⟨(measurable_snd.comp measurable_reImPath).aemeasurable, planarBrownianMotion_map_im z⟩

/-- `√(2⁻¹)⁻¹ = √2`, the factor produced by Brownian scaling with `c = 1/2`. -/
lemma inv_sqrt_half : (√((2⁻¹ : ℝ≥0) : ℝ))⁻¹ = Real.sqrt ((2 : ℕ) : ℝ) := by
  rw [NNReal.coe_inv, Real.sqrt_inv, inv_inv]
  norm_num

/-- **Planar Brownian motion as `IsBrownianSpace 2 0`.** Under `planarBrownianMotion z`, the
process `t ↦ toEuclid (b (t / 2) - z)` is a Brownian motion on `EuclideanSpace ℝ (Fin 2)` started
at `0` with generator `Δ / 4`: it starts at `0`, each coordinate times `√2` is a standard real
Brownian motion, and the two coordinates are independent. -/
theorem isBrownianSpace_halfSpeedPath (z : ℂ) :
    LatticeProb.IsBrownianSpace 2 0 (halfSpeedPath z) (planarBrownianMotion z) where
  start := by
    have hre := (((MarkovProcess.isBrownianReal_brownianMotion z.re).hasLaw_eval 0).comp
      (hasLaw_re z))
    have him := (((MarkovProcess.isBrownianReal_brownianMotion z.im).hasLaw_eval 0).comp
      (hasLaw_im z))
    rw [gaussianReal_zero_var] at hre him
    filter_upwards [hre.ae_eq_of_dirac, him.ae_eq_of_dirac] with b h1 h2
    simp only [Function.comp_apply, reImPath_fst_apply, reImPath_snd_apply, sub_eq_zero] at h1 h2
    have hb : b 0 = z := Complex.ext h1 h2
    simp [halfSpeedPath, hb]
  coord i := by
    fin_cases i
    · have h := (isBrownianReal_comp_hasLaw (isBrownianReal_brownianMotion_sub z.re)
        (hasLaw_re z)).smul (c := 2⁻¹) (by norm_num)
      have heq : (fun (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) =>
          Real.sqrt ((2 : ℕ) : ℝ) *
            (halfSpeedPath z t b 0 - (0 : EuclideanSpace ℝ (Fin 2)) 0)) =
          fun t b => (√((2⁻¹ : ℝ≥0) : ℝ))⁻¹ * ((reImPath b).1 (2⁻¹ * t) - z.re) := by
        funext t b
        rw [inv_sqrt_half, halfSpeedPath_zero, reImPath_fst_apply]
        simp
      simpa only [Fin.zero_eta, heq] using h
    · have h := (isBrownianReal_comp_hasLaw (isBrownianReal_brownianMotion_sub z.im)
        (hasLaw_im z)).smul (c := 2⁻¹) (by norm_num)
      have heq : (fun (t : ℝ≥0) (b : MarkovProcess.ContinuousPath ℂ) =>
          Real.sqrt ((2 : ℕ) : ℝ) *
            (halfSpeedPath z t b 1 - (0 : EuclideanSpace ℝ (Fin 2)) 1)) =
          fun t b => (√((2⁻¹ : ℝ≥0) : ℝ))⁻¹ * ((reImPath b).2 (2⁻¹ * t) - z.im) := by
        funext t b
        rw [inv_sqrt_half, halfSpeedPath_one, reImPath_snd_apply]
        simp
      simpa only [Fin.mk_one, heq] using h
  indep := by
    have hφ : ∀ x : ℝ, Measurable fun (p : MarkovProcess.ContinuousPath ℝ) (t : ℝ≥0) =>
        p (2⁻¹ * t) - x := fun x =>
      measurable_pi_iff.mpr fun t => (measurable_eval_path (2⁻¹ * t)).sub_const x
    have hRI : IndepFun (fun b : MarkovProcess.ContinuousPath ℂ => (reImPath b).1)
        (fun b => (reImPath b).2) (planarBrownianMotion z) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map (hasLaw_re z).aemeasurable
        (hasLaw_im z).aemeasurable, (hasLaw_re z).map_eq, (hasLaw_im z).map_eq]
      exact planarBrownianMotion_map_reImPath z
    have h01 := hRI.comp (hφ z.re) (hφ z.im)
    have hfun : ∀ i : Fin 2, (fun (b : MarkovProcess.ContinuousPath ℂ) (t : ℝ≥0) =>
        halfSpeedPath z t b i) =
        if i = 0 then (fun p (t : ℝ≥0) => p (2⁻¹ * t) - z.re) ∘ fun b => (reImPath b).1
        else (fun p (t : ℝ≥0) => p (2⁻¹ * t) - z.im) ∘ fun b => (reImPath b).2 := by
      intro i
      fin_cases i
      · funext b t
        simp [halfSpeedPath_zero]
      · funext b t
        simp [halfSpeedPath_one]
    have hm : ∀ i : Fin 2, Measurable fun (b : MarkovProcess.ContinuousPath ℂ) (t : ℝ≥0) =>
        halfSpeedPath z t b i := by
      intro i
      rw [hfun i]
      split_ifs
      · exact (hφ z.re).comp (measurable_fst.comp measurable_reImPath)
      · exact (hφ z.im).comp (measurable_snd.comp measurable_reImPath)
    refine iIndepFun_fin_two' hm ?_
    rw [hfun 0, hfun 1]
    simpa using h01

end MatedCRT.PlanarBrownianSpace
