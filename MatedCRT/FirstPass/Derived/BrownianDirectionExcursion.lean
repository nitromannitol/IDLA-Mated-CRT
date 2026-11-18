import MatedCRT.FirstPass.LPBridge.ExitRestartLimit
import MatedCRT.FirstPass.Derived.TargetLawRotation
import LatticeProb.Prob.PlanarBrownianGermZeroOne

/-!
# Directional excursions of the centred planar Brownian law

`MatedCRT.ExitRestart.muPlanar` is the law of the centred planar Brownian motion on the path space `ℝ≥0 → ℂ`.
For `η ≥ 0` and `s ∈ ℝ` let `nonPosBefore η s` be the set of paths whose real part is at most `s` at every
rational time of `(0, η)`.

* `MatedCRT.ExitRestart.tendsto_muPlanar_nonPosBefore`: for `η > 0` the measure `muPlanar (nonPosBefore η s)`
  tends to `0` as `s ↓ 0`. Indeed, by Blumenthal's zero-one law a planar Brownian path has, almost surely,
  positive real part at rational times arbitrarily close to `0`
  (Mörters–Peres, *Brownian Motion*, Theorem 2.7 and Lemma 2.9).
* `MatedCRT.ExitRestart.map_muPlanar_linearIsometryEquiv`: `muPlanar` is invariant under every real linear
  isometry of `ℂ` applied pointwise in time (rotation and reflection invariance of planar Brownian motion).
* `MatedCRT.ExitRestart.muPlanar_dirNonPos_eq`: for a unit vector `n`, the paths whose component along `n` is at
  most `s` at every rational time of `(0, η)` have the same `muPlanar`-measure as `nonPosBefore η s`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.ExitRestart

/-- The paths whose real part is at most `s` at every rational time of `(0, η)`. -/
def nonPosBefore (η : ℝ≥0) (s : ℝ) : Set (ℝ≥0 → ℂ) :=
  {δ | ∀ q : ℚ, 0 < q → (q : ℝ) < η → (δ (Real.toNNReal q)).re ≤ s}

/-- The set `nonPosBefore η s` is measurable in the product σ-algebra of the path space. -/
theorem measurableSet_nonPosBefore (η : ℝ≥0) (s : ℝ) : MeasurableSet (nonPosBefore η s) := by
  have : nonPosBefore η s = ⋂ q : ℚ, {δ : ℝ≥0 → ℂ | 0 < q → (q : ℝ) < η →
      (δ (Real.toNNReal q)).re ≤ s} := by
    ext δ
    simp [nonPosBefore]
  rw [this]
  refine MeasurableSet.iInter fun q => ?_
  by_cases h : 0 < q ∧ (q : ℝ) < η
  · have : {δ : ℝ≥0 → ℂ | 0 < q → (q : ℝ) < η → (δ (Real.toNNReal q)).re ≤ s} =
        (fun δ : ℝ≥0 → ℂ => (δ (Real.toNNReal q)).re) ⁻¹' Iic s := by
      ext δ
      simp [h.1, h.2]
    rw [this]
    exact (Complex.measurable_re.comp (measurable_pi_apply _)) measurableSet_Iic
  · have : {δ : ℝ≥0 → ℂ | 0 < q → (q : ℝ) < η → (δ (Real.toNNReal q)).re ≤ s} = univ := by
      ext δ
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [this]
    exact MeasurableSet.univ

/-- The paths of `nonPosBefore η s` are monotone in `s`. -/
theorem nonPosBefore_mono (η : ℝ≥0) {s s' : ℝ} (h : s ≤ s') : nonPosBefore η s ⊆ nonPosBefore η s' :=
  fun _ hδ q hq0 hqη => (hδ q hq0 hqη).trans h

/-- The centred planar Brownian path law is the image of planar Brownian motion from `0`. -/
theorem muPlanar_apply_eq (Γ : Set (ℝ≥0 → ℂ)) (hΓ : MeasurableSet Γ) :
    muPlanar Γ = planarBrownianMotion 0 (cC 0 ⁻¹' Γ) := by
  rw [← map_cC_planarBrownianMotion 0, Measure.map_apply (measurable_cC 0) hΓ]

/-- Almost surely a planar Brownian path from `0` has positive real part at some rational time arbitrarily close
to `0` (Blumenthal's zero-one law). -/
theorem ae_planarBrownianMotion_exists_rat_re_pos :
    ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)), ∀ m : ℕ, ∃ q : ℚ, 0 < (q : ℝ) ∧
      (q : ℝ) < LatticeProb.PlanarBrownian.freqEps m ∧ 0 < (b (Real.toNNReal q)).re := by
  have hW : LatticeProb.PlanarBrownian.IsPlanarBrownian (fun t (b : ContinuousPath ℂ) => cC 0 b t)
      (planarBrownianMotion (0 : ℂ)) :=
    isPlanarBrownian_of_law (I := cC 0) (measurable_cC 0)
      (fun b => b.continuous.sub continuous_const) (map_cC_planarBrownianMotion 0)
  have hm := LatticeProb.PlanarBrownian.ae_forall_exists_rat_pos_of_marginal
    (P := planarBrownianMotion (0 : ℂ)) (X := fun t (b : ContinuousPath ℂ) => (cC 0 b t).re)
    (fun t => Complex.measurable_re.comp (hW.measurable t))
    (fun q hq => by
      have h := LatticeProb.PlanarBrownian.measure_pairing_pos hW (v := 1) one_ne_zero (t := q) hq.ne'
      convert h using 2
      ext b
      simp [LatticeProb.PlanarBrownian.pairing])
    (fun A hA => LatticeProb.isTrivialSigma_iInf_bmPast hW.re
      (fun t => Complex.measurable_re.comp (hW.measurable t)) A hA)
  filter_upwards [hm] with b hb m
  obtain ⟨q, hq0, hqm, hpos⟩ := hb m
  exact ⟨q, hq0, hqm, by simpa [cC] using hpos⟩

/-- **Directional excursion.** For `η > 0` the `muPlanar`-measure of the paths whose real part is at most `s` at
all rational times of `(0, η)` tends to `0` as `s ↓ 0`. -/
theorem tendsto_muPlanar_nonPosBefore {η : ℝ≥0} (hη : 0 < η) :
    Tendsto (fun s : ℝ => muPlanar (nonPosBefore η s)) (𝓝[>] 0) (𝓝 0) := by
  have hmeasE : ∀ s : ℝ, MeasurableSet (cC (0 : ℂ) ⁻¹' nonPosBefore η s) :=
    fun s => (measurable_cC 0) (measurableSet_nonPosBefore η s)
  have hlim := tendsto_measure_biInter_gt (μ := planarBrownianMotion (0 : ℂ))
    (s := fun s : ℝ => cC (0 : ℂ) ⁻¹' nonPosBefore η s) (a := (0 : ℝ))
    (fun r _ => (hmeasE r).nullMeasurableSet)
    (fun i j _ hij => preimage_mono (nonPosBefore_mono η hij))
    ⟨1, one_pos, measure_ne_top _ _⟩
  have h0 : planarBrownianMotion (0 : ℂ) (⋂ r > (0 : ℝ), cC (0 : ℂ) ⁻¹' nonPosBefore η r) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 ae_planarBrownianMotion_exists_rat_re_pos)
    intro b hb hgood
    simp only [mem_iInter, mem_preimage] at hb
    obtain ⟨m, hm⟩ := (LatticeProb.PlanarBrownian.tendsto_freqEps.eventually
      (gt_mem_nhds hη)).exists
    obtain ⟨q, hq0, hqm, hpos⟩ := hgood m
    have hqη : (q : ℝ) < η := hqm.trans (NNReal.coe_lt_coe.2 hm)
    have h1 := hb ((b (Real.toNNReal q)).re / 2) (half_pos hpos) q (by exact_mod_cast hq0) hqη
    simp only [cC, sub_zero] at h1
    linarith
  have hfun : (fun s : ℝ => muPlanar (nonPosBefore η s)) =
      fun s : ℝ => planarBrownianMotion (0 : ℂ) (cC (0 : ℂ) ⁻¹' nonPosBefore η s) :=
    funext fun s => muPlanar_apply_eq _ (measurableSet_nonPosBefore η s)
  rw [hfun]
  rw [h0] at hlim
  exact hlim

/-- **Rotation and reflection invariance of the centred planar Brownian law.** Applying a real linear isometry of
`ℂ` at every time preserves `muPlanar`. -/
theorem map_muPlanar_linearIsometryEquiv (L : ℂ ≃ₗᵢ[ℝ] ℂ) :
    muPlanar.map (fun (δ : ℝ≥0 → ℂ) t => L (δ t)) = muPlanar := by
  have hmeasL : Measurable (fun (δ : ℝ≥0 → ℂ) t => L (δ t)) :=
    Measurable.of_eval fun t => L.continuous.measurable.comp (measurable_pi_apply t)
  have h := MatedCRT.TargetLawRotation.planarBrownianMotion_map_linearIsometryEquiv L 0
  rw [map_zero] at h
  have hcomp : (fun (δ : ℝ≥0 → ℂ) t => L (δ t)) ∘ cC 0 =
      cC 0 ∘ ContinuousPath.rescale L.toHomeomorph 1 := by
    funext b t
    simp [cC]
  rw [← map_cC_planarBrownianMotion 0, Measure.map_map hmeasL (measurable_cC 0), hcomp,
    ← Measure.map_map (measurable_cC 0) (ContinuousPath.measurable_rescale _ _), ← h]

/-- **Direction independence.** For a unit vector `n`, the `muPlanar`-measure of the paths whose component along `n`
is at most `s` at all rational times of `(0, η)` is the measure of `nonPosBefore η s` (the case `n = 1`). -/
theorem muPlanar_dirNonPos_eq (η : ℝ≥0) (s : ℝ) {n : ℂ} (hn : ‖n‖ = 1) :
    muPlanar {δ : ℝ≥0 → ℂ | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
        n.re * (δ (Real.toNNReal q)).re + n.im * (δ (Real.toNNReal q)).im ≤ s} =
      muPlanar (nonPosBefore η s) := by
  let a : Circle := ⟨(starRingEnd ℂ) n, by simp [Submonoid.unitSphere, hn]⟩
  have hmeasL : Measurable (fun (δ : ℝ≥0 → ℂ) t => rotation a (δ t)) :=
    Measurable.of_eval fun t => (rotation a).continuous.measurable.comp (measurable_pi_apply t)
  have hset : {δ : ℝ≥0 → ℂ | ∀ q : ℚ, 0 < q → (q : ℝ) < η →
      n.re * (δ (Real.toNNReal q)).re + n.im * (δ (Real.toNNReal q)).im ≤ s} =
      (fun (δ : ℝ≥0 → ℂ) t => rotation a (δ t)) ⁻¹' nonPosBefore η s := by
    ext δ
    simp only [mem_ofPred_eq, mem_preimage, nonPosBefore, rotation_apply]
    refine forall_congr' fun q => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    simp [a, Complex.mul_re]
  rw [hset, ← Measure.map_apply hmeasL (measurableSet_nonPosBefore η s),
    map_muPlanar_linearIsometryEquiv]

end MatedCRT.ExitRestart
