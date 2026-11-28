import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import MatedCRT.FirstPass.Derived.BrownianTubeChain
import MatedCRT.FirstPass.Derived.CanonicalBrownianPathLaw
import LatticeProb.Prob.CauchyPointPolar
import LatticeProb.Prob.CorrelatedBMStart
import LatticeProb.Prob.CorrelatedBMPlanarHeatBridge

/-!
# Tube positivity for the uncorrelated Brownian pair

For the law `μ` of the pair `(L, R)` of two independent two-sided standard Brownian motions
(`IsCorrelatedBM2 (√2) μ`), the forward planar path `s ↦ (L s - L 0) + i (R s - R 0)` is a
`ContinuousPath ℂ`, and its law is `planarBrownianMotion 0`.

* `fwdPlanarPath`: the forward planar path of an element of `Path2`.
* `measurable_fwdPlanarPath`: it is measurable.
* `map_fwdPlanarPath_eq`: for `IsCorrelatedBM2 (√2) μ`, `μ.map fwdPlanarPath = planarBrownianMotion 0`.
  The forward coordinates are independent standard Brownian motions (`iIndepFun_halfPathMap`), each of
  the canonical path law (`map_pathMap_eq_brownianMotion_zero`), and `planarBrownianMotion 0` is the
  image of the product of two such laws under `complexPathOfReIm`.
* `planarTubePositive`: `PlanarTubePositive`. The event contains the preimage under `fwdPlanarPath` of
  a tube around a straight path, whose `planarBrownianMotion 0`-measure is positive by the one-step
  window chain `ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain` and
  `tubeChain_inter_subset_tube`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open scoped NNReal ENNReal
open HarmonicBalls LatticeProb LatticeProb.CorrelatedBM

namespace MatedCRT.PeanosphereTriplePoints

/-! ### The forward planar path and its law -/

/-- The forward planar path of `p : Path2` started at `0`: `s ↦ (p s - p 0).1 + i (p s - p 0).2` for
`s ≥ 0`. -/
noncomputable def fwdPlanarPath (p : Path2) : ContinuousPath ℂ :=
  ⟨fun s : ℝ≥0 => (((p s).1 - (p 0).1 : ℝ) : ℂ) + (((p s).2 - (p 0).2 : ℝ) : ℂ) * Complex.I, by
    have hp : Continuous fun s : ℝ≥0 => p (s : ℝ) := p.continuous.comp NNReal.continuous_coe
    have h1 : Continuous fun s : ℝ≥0 => (p (s : ℝ)).1 := continuous_fst.comp hp
    have h2 : Continuous fun s : ℝ≥0 => (p (s : ℝ)).2 := continuous_snd.comp hp
    fun_prop⟩

/-- The forward planar path map `Path2 → ContinuousPath ℂ` is measurable. -/
theorem measurable_fwdPlanarPath : Measurable fwdPlanarPath := by
  rw [ContinuousMapBorel.ContinuousMap.measurable_iff_eval]
  intro t
  have h1 : Measurable fun p : Path2 => (p (t : ℝ)).1 :=
    measurable_fst.comp (ContinuousMapBorel.ContinuousMap.measurable_eval (t : ℝ))
  have h2 : Measurable fun p : Path2 => (p (t : ℝ)).2 :=
    measurable_snd.comp (ContinuousMapBorel.ContinuousMap.measurable_eval (t : ℝ))
  have h3 : Measurable fun p : Path2 => (p 0).1 :=
    measurable_fst.comp (ContinuousMapBorel.ContinuousMap.measurable_eval (0 : ℝ))
  have h4 : Measurable fun p : Path2 => (p 0).2 :=
    measurable_snd.comp (ContinuousMapBorel.ContinuousMap.measurable_eval (0 : ℝ))
  exact (Complex.measurable_ofReal.comp (h1.sub h3)).add
    ((Complex.measurable_ofReal.comp (h2.sub h4)).mul_const _)

/-- **The path law of a planar Brownian motion.** A planar process `W` that is a standard planar Brownian
motion started at `0` in the sense of `IsPlanarBM` (a centred Gaussian process with independent coordinates of
covariance `min s t`), with measurable values and continuous paths, has the law `planarBrownianMotion 0` on
`ContinuousPath ℂ`. The real and imaginary parts are standard Brownian motions, independent because
jointly Gaussian and uncorrelated, and `planarBrownianMotion 0` is the image of the product of two copies of
`brownianMotion 0` under `complexPathOfReIm`. -/
theorem map_planarPath_eq_of_isPlanarBM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℂ} (hW : LQGMetric.KilledHeat.IsPlanarBM W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous fun t => W t ω) :
    P.map (fun ω => (⟨fun t => W t ω, hc ω⟩ : ContinuousPath ℂ)) = planarBrownianMotion 0 := by
  have := hW.gauss.isProbabilityMeasure
  let Y : Bool → ℝ≥0 → Ω → ℝ := fun b t => LQGMetric.KilledHeat.coordProc W (b, t)
  have hYm : ∀ b t, Measurable (Y b t) := by
    intro b t
    cases b
    · exact Complex.measurable_re.comp (hm t)
    · exact Complex.measurable_im.comp (hm t)
  have hYc : ∀ b ω, Continuous fun t => Y b t ω := by
    intro b ω
    cases b
    · exact Complex.continuous_re.comp (hc ω)
    · exact Complex.continuous_im.comp (hc ω)
  have hYB : ∀ b, ProbabilityTheory.IsBrownianReal (Y b) P := by
    intro b
    have hg : IsGaussianProcess (Y b) P := hW.gauss.comp_right (fun t : ℝ≥0 => (b, t))
    have hpre : ProbabilityTheory.IsPreBrownianReal (Y b) P := by
      refine hg.isPreBrownianReal_of_covariance (fun t => hW.mean (b, t)) ?_
      intro s t hst
      show cov[LQGMetric.KilledHeat.coordProc W (b, s), LQGMetric.KilledHeat.coordProc W (b, t); P] = s
      rw [hW.cov]
      simp [min_eq_left hst]
    exact ⟨hpre, ae_of_all _ (hYc b)⟩
  have hind : iIndepFun (fun b (ω : Ω) (t : ℝ≥0) => Y b t ω) P := by
    refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero (S := fun _ => ℝ≥0)
      (X := fun b t => Y b t)
      (hW.gauss.comp_right (fun p : (_ : Bool) × ℝ≥0 => (p.1, p.2)))
      (fun b t => (hYm b t).aemeasurable) ?_
    intro b b' hne s t
    show cov[LQGMetric.KilledHeat.coordProc W (b, s), LQGMetric.KilledHeat.coordProc W (b', t); P] = 0
    rw [hW.cov]
    simp [hne]
  let Z : Bool → Ω → ContinuousPath ℝ := fun b => pathMap (Y b) (hYc b)
  have hZ : iIndepFun Z P := by
    rw [iIndepFun_iff_iIndep] at hind ⊢
    convert hind using 1
    funext b
    exact (congrArg (MeasurableSpace.comap (Z b))
      measurableSpace_continuousMap_eq_comap_coeFn).trans MeasurableSpace.comap_comp
  have hZm : ∀ b, Measurable (Z b) := fun b => measurable_pathMap _ (hYm b) (hYc b)
  have hZlaw : ∀ b, P.map (Z b) = brownianMotion 0 := fun b =>
    map_pathMap_eq_brownianMotion_zero (hYB b) (hYm b) (hYc b)
  have hpair : P.map (fun ω => (Z false ω, Z true ω)) =
      (brownianMotion 0).prod (brownianMotion 0) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hZm false).aemeasurable
      (hZm true).aemeasurable).1 (hZ.indepFun (by decide)), hZlaw, hZlaw]
  have hpt : (fun ω => (⟨fun t => W t ω, hc ω⟩ : ContinuousPath ℂ)) =
      complexPathOfReIm ∘ fun ω => (Z false ω, Z true ω) := by
    funext ω
    ext t
    simp [Z, Y, pathMap, LQGMetric.KilledHeat.coordProc, Complex.re_add_im]
  rw [hpt, ← Measure.map_map measurable_complexPathOfReIm ((hZm false).prodMk (hZm true)), hpair,
    planarBrownianMotion_apply, Complex.zero_re, Complex.zero_im]

/-- **The forward planar path of an uncorrelated pair is planar Brownian motion.** -/
theorem map_fwdPlanarPath_eq {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) :
    μ.map fwdPlanarPath = planarBrownianMotion 0 := by
  have := hμ.isProbabilityMeasure
  have hm : ∀ t : ℝ≥0, Measurable (forwardPlanarPath t) := fun t =>
    (Complex.measurable_ofReal.comp
        (measurable_lrCoord_path 0 (t : ℝ))).add
      ((Complex.measurable_ofReal.comp
        (measurable_lrCoord_path 1 (t : ℝ))).mul_const _)
  have hc : ∀ ω, Continuous fun t => forwardPlanarPath t ω := fun ω => by
    unfold forwardPlanarPath
    exact ((Complex.continuous_ofReal.comp ((continuous_lrCoord_time 0 ω).comp
      NNReal.continuous_coe)).add ((Complex.continuous_ofReal.comp
      ((continuous_lrCoord_time 1 ω).comp NNReal.continuous_coe)).mul
      continuous_const))
  have h := map_planarPath_eq_of_isPlanarBM (isPlanarBM_forwardPlanarPath hμ) hm hc
  have hae : fwdPlanarPath =ᵐ[μ]
      fun ω => (⟨fun t => forwardPlanarPath t ω, hc ω⟩ : ContinuousPath ℂ) := by
    filter_upwards [ae_eval_zero_eq_zero hμ] with p hp
    ext t
    simp [fwdPlanarPath, forwardPlanarPath, MatedCRTHarmonic.MatedCRT.lrCoord, hp]
  rw [Measure.map_congr hae]
  exact h

/-! ### Tubes around a straight path -/

/-- The straight path `t ↦ (t / T) (w.1 + i w.2)` from `0` to `w` on `[0, T]`, as a complex curve. -/
noncomputable def tubeCurve (T : ℝ) (w : ℝ × ℝ) (t : ℝ≥0) : ℂ :=
  (((t : ℝ) / T : ℝ) : ℂ) * ((w.1 : ℂ) + (w.2 : ℂ) * Complex.I)

theorem tubeCurve_zero (T : ℝ) (w : ℝ × ℝ) : tubeCurve T w 0 = 0 := by
  simp [tubeCurve]

theorem tubeCurve_sub_re (T : ℝ) (w : ℝ × ℝ) (t u : ℝ≥0) :
    (tubeCurve T w t - tubeCurve T w u).re = ((t : ℝ) / T - (u : ℝ) / T) * w.1 := by
  rw [tubeCurve, tubeCurve, ← sub_mul, ← Complex.ofReal_sub]
  simp [Complex.mul_re]

theorem tubeCurve_sub_im (T : ℝ) (w : ℝ × ℝ) (t u : ℝ≥0) :
    (tubeCurve T w t - tubeCurve T w u).im = ((t : ℝ) / T - (u : ℝ) / T) * w.2 := by
  rw [tubeCurve, tubeCurve, ← sub_mul, ← Complex.ofReal_sub]
  simp [Complex.mul_im]

theorem norm_tubeCurve_sub (T : ℝ) (w : ℝ × ℝ) (t u : ℝ≥0) :
    ‖tubeCurve T w t - tubeCurve T w u‖ ≤ |(t : ℝ) / T - (u : ℝ) / T| * (|w.1| + |w.2|) := by
  rw [tubeCurve, tubeCurve, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ‖(w.1 : ℂ) + (w.2 : ℂ) * Complex.I‖
      ≤ ‖(w.1 : ℂ)‖ + ‖(w.2 : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |w.1| + |w.2| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]

theorem fwdPlanarPath_sub_tubeCurve_re (p : Path2) (T : ℝ) (w : ℝ × ℝ) (t : ℝ≥0) :
    (fwdPlanarPath p t - tubeCurve T w t).re =
      ((p (t : ℝ)).1 - (p 0).1) - (t : ℝ) / T * w.1 := by
  simp [fwdPlanarPath, tubeCurve, Complex.mul_re]

theorem fwdPlanarPath_sub_tubeCurve_im (p : Path2) (T : ℝ) (w : ℝ × ℝ) (t : ℝ≥0) :
    (fwdPlanarPath p t - tubeCurve T w t).im =
      ((p (t : ℝ)).2 - (p 0).2) - (t : ℝ) / T * w.2 := by
  simp [fwdPlanarPath, tubeCurve, Complex.mul_im]

/-- **Tube positivity for the uncorrelated Brownian pair.** The planar path `(L - L 0, R - R 0)` of an
uncorrelated two-sided Brownian pair stays within `ε` of the straight path from `0` to `w` up to time
`T` with positive probability. -/
theorem planarTubePositive : PlanarTubePositive := by
  intro μ hμ T w ε hT hε
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / 4 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |w.1| + |w.2| := ⟨_, rfl⟩
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hw1 : |w.1| ≤ M := by rw [hM]; exact le_add_of_nonneg_right (abs_nonneg _)
  have hw2 : |w.2| ≤ M := by rw [hM]; exact le_add_of_nonneg_left (abs_nonneg _)
  have hpos : 0 < 16 * M / ε' + 512 * T / ε' ^ 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (16 * M / ε' + 512 * T / ε' ^ 2)
  have hNpos : (0 : ℝ) < N := hpos.trans hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have h1 : 16 * M / ε' ≤ N :=
    le_trans (le_add_of_nonneg_right (by positivity)) hN.le
  have h2 : 512 * T / ε' ^ 2 ≤ N :=
    le_trans (le_add_of_nonneg_left (by positivity)) hN.le
  have hM_le : M / N ≤ ε' / 16 := by
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hε'0] at h1
    linarith
  have hΔ_le' : T / N ≤ ε' ^ 2 / 512 := by
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ≥0, (Δ : ℝ) = T / N := ⟨⟨T / N, by positivity⟩, rfl⟩
  have hΔpos : 0 < Δ := by
    rw [← NNReal.coe_pos, hΔ]
    positivity
  have hΔle : (Δ : ℝ) ≤ ε' ^ 2 / 512 := by rw [hΔ]; exact hΔ_le'
  have hNΔ : (N : ℝ≥0) * Δ = T.toNNReal :=
    NNReal.eq (by
      rw [NNReal.coe_mul, NNReal.coe_natCast, hΔ, Real.coe_toNNReal _ hT.le]
      field_simp)
  have hinv : ((N : ℝ≥0) : ℝ) ≠ 0 := hNpos.ne'
  -- the steps of the straight path
  have hstep : ∀ i : ℕ,
      |(tubeCurve T w (((i + 1 : ℕ) : ℝ≥0) * Δ) - tubeCurve T w ((i : ℝ≥0) * Δ)).re| ≤ ε' / 16 ∧
      |(tubeCurve T w (((i + 1 : ℕ) : ℝ≥0) * Δ) - tubeCurve T w ((i : ℝ≥0) * Δ)).im| ≤ ε' / 16 := by
    intro i
    have hd : (((((i + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ)) / T -
        ((((i : ℝ≥0) * Δ : ℝ≥0) : ℝ)) / T = 1 / N := by
      push_cast
      rw [hΔ]
      field_simp
      ring
    have hcoef : |(1 / (N : ℝ))| = 1 / N := abs_of_pos (by positivity)
    rw [tubeCurve_sub_re, tubeCurve_sub_im, hd, abs_mul, abs_mul, hcoef]
    constructor
    · calc 1 / (N : ℝ) * |w.1| ≤ 1 / N * M := mul_le_mul_of_nonneg_left hw1 (by positivity)
        _ = M / N := by ring
        _ ≤ ε' / 16 := hM_le
    · calc 1 / (N : ℝ) * |w.2| ≤ 1 / N * M := mul_le_mul_of_nonneg_left hw2 (by positivity)
        _ = M / N := by ring
        _ ≤ ε' / 16 := hM_le
  -- the Lipschitz bound of the straight path
  have hg : ∀ t u : ℝ≥0, t ≤ u → u ≤ t + Δ → ‖tubeCurve T w t - tubeCurve T w u‖ ≤ M / N := by
    intro t u htu hut
    have htu' : (t : ℝ) ≤ u := by exact_mod_cast htu
    have hut' : (u : ℝ) ≤ t + T / N := by
      rw [← hΔ]; exact_mod_cast hut
    have habs : |(t : ℝ) / T - (u : ℝ) / T| ≤ 1 / N := by
      rw [abs_le]
      constructor
      · have : (u : ℝ) / T - t / T ≤ 1 / N := by
          rw [← sub_div, div_le_iff₀ hT]
          have : 1 / (N : ℝ) * T = T / N := by ring
          rw [this]; linarith
        linarith
      · have : (t : ℝ) / T ≤ u / T := div_le_div_of_nonneg_right htu' hT.le
        have : (0 : ℝ) ≤ 1 / N := by positivity
        linarith
    calc ‖tubeCurve T w t - tubeCurve T w u‖
        ≤ |(t : ℝ) / T - (u : ℝ) / T| * (|w.1| + |w.2|) := norm_tubeCurve_sub T w t u
      _ ≤ 1 / N * M := by
          rw [← hM]
          exact mul_le_mul_of_nonneg_right habs hMnn
      _ = M / N := by ring
  have hκ : Real.sqrt 2 * (3 * ε' / 4) + Real.sqrt 2 * (ε' / 16) + M / N ≤ ε := by
    have hs : Real.sqrt 2 ≤ 3 / 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    nlinarith [mul_le_mul_of_nonneg_right hs hε'0.le]
  have hy0 : tubeCurve T w (((0 : ℕ) : ℝ≥0) * Δ) = 0 := by simp [tubeCurve]
  have hε16 : 0 < ε' / 16 := by positivity
  have hx_re : |((0 : ℂ) - tubeCurve T w (((0 : ℕ) : ℝ≥0) * Δ)).re| < ε' / 16 := by
    rw [hy0]; simpa using hε16
  have hx_im : |((0 : ℂ) - tubeCurve T w (((0 : ℕ) : ℝ≥0) * Δ)).im| < ε' / 16 := by
    rw [hy0]; simpa using hε16
  have hchain := ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain hε'0 hΔpos N 0
    (fun i => tubeCurve T w ((i : ℝ≥0) * Δ)) hstep hx_re hx_im
  have hg0 : tubeCurve T w 0 = 0 := tubeCurve_zero T w
  have hsub := tubeChain_inter_subset_tube (ε := ε') (Δ := Δ) (N := N) hN0
    (g := tubeCurve T w) (L := M / N) (κ := ε) hg hκ (x := 0)
    (by rw [hg0]; simpa using hε16) (by rw [hg0]; simpa using hε16)
  have hpos0 : 0 < planarBrownianMotion 0
      (tubeChain ε' Δ N (fun i => tubeCurve T w ((i : ℝ≥0) * Δ))) :=
    lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.ofReal_pos.2
      (MatedCRTHarmonic.Brownian.oneStepConst_pos hε'0 hΔpos hΔle)) _) hchain
  have hS : MeasurableSet
      (tubeChain ε' Δ N (fun i => tubeCurve T w ((i : ℝ≥0) * Δ)) ∩
        {ω : ContinuousPath ℂ | ω 0 = 0}) :=
    (measurableSet_tubeChain ε' Δ N _).inter
      (measurableSet_eq_fun (ContinuousPath.measurable_coordinateProcess (alpha := ℂ) 0)
        measurable_const)
  have hmono : planarBrownianMotion 0
        (tubeChain ε' Δ N (fun i => tubeCurve T w ((i : ℝ≥0) * Δ))) ≤
      planarBrownianMotion 0 (tubeChain ε' Δ N (fun i => tubeCurve T w ((i : ℝ≥0) * Δ)) ∩
        {ω : ContinuousPath ℂ | ω 0 = 0}) := by
    apply measure_mono_ae
    filter_upwards [ae_planarBrownianMotion_eval_zero 0] with ω h0 hω
    exact ⟨hω, h0⟩
  refine lt_of_lt_of_le (hpos0.trans_le hmono) ?_
  rw [← map_fwdPlanarPath_eq hμ, Measure.map_apply measurable_fwdPlanarPath hS]
  refine measure_mono ?_
  intro p hp s hs
  have ht : s.toNNReal ≤ (N : ℝ≥0) * Δ := by
    rw [hNΔ]; exact Real.toNNReal_le_toNNReal hs.2
  have h := hsub hp s.toNNReal ht
  have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
  have hre := Complex.abs_re_le_norm (fwdPlanarPath p s.toNNReal - tubeCurve T w s.toNNReal)
  have him := Complex.abs_im_le_norm (fwdPlanarPath p s.toNNReal - tubeCurve T w s.toNNReal)
  rw [fwdPlanarPath_sub_tubeCurve_re, hcoe] at hre
  rw [fwdPlanarPath_sub_tubeCurve_im, hcoe] at him
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · calc _ ≤ _ := hre
      _ < ε := h
  · calc _ ≤ _ := him
      _ < ε := h

end MatedCRT.PeanosphereTriplePoints
