import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraBarrierPlanar
import MatedCRT.FirstPass.Derived.CanonicalBrownianPathLaw
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import LatticeProb.Prob.BrownianPathCoords

/-!
# The killed interval kernel near the lower barrier

`killedBarrierPositive : KilledBarrierPositive` (`ShimuraSteps.lean`): for real Brownian motion `B`, `T > 0` and
`0 < y₁ < y₂ < H` there is `c > 0` such that for `0 < e ≤ 1` the increment `B s - B 0` stays in `(-e, H)` up to time
`T` and ends in `(y₁, y₂)` with probability at least `c e` (Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, §2.8.C).

The probability depends only on the law of the path: a continuous modification of `B`
(`IsBrownianReal.exists_continuous_indistinguishable`) has the path law `brownianMotion 0`
(`map_pathMap_eq_brownianMotion_zero`), which is the law of the real part of planar Brownian motion
(`planarBrownianMotion_map_reImPath`); the bound for planar Brownian motion is
`exists_le_planarBrownianMotion_killedStrip`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls

namespace MatedCRT.PeanosphereTriplePoints

/-- The time-`t` evaluation of a real path is measurable for the canonical filtration at any time `T ≥ t`. -/
theorem measurable_eval_canonicalFiltration_real {t T : ℝ≥0} (ht : t ≤ T) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℝ) T] (fun f : ContinuousPath ℝ => f t) :=
  (ContinuousPath.measurable_coordinateProcess_canonicalFiltration t).mono
    ((ContinuousPath.canonicalFiltration (alpha := ℝ)).mono ht) le_rfl

/-- The event of `KilledBarrierPositive` for a real path, in terms of its increments from time `0`. -/
def killedIncrementSet (e H y₁ y₂ : ℝ) (T : ℝ≥0) : Set (ContinuousPath ℝ) :=
  {f | (∀ s ≤ T, -e < f s - f 0 ∧ f s - f 0 < H) ∧ f T - f 0 ∈ Ioo y₁ y₂}

theorem measurableSet_killedIncrementSet (e H y₁ y₂ : ℝ) (T : ℝ≥0) :
    MeasurableSet (killedIncrementSet e H y₁ y₂ T) := by
  have hF : Continuous fun x : ℝ × ℝ => max (-(x.1 - x.2) - e) ((x.1 - x.2) - H) := by fun_prop
  have hset : killedIncrementSet e H y₁ y₂ T =
      {f : ContinuousPath ℝ | ∀ s ≤ T, max (-(f s - f 0) - e) ((f s - f 0) - H) < 0} ∩
        {f | f T - f 0 ∈ Ioo y₁ y₂} := by
    ext f
    simp only [killedIncrementSet, mem_ofPred_eq, mem_inter_iff, max_lt_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun s hs => ⟨by linarith [(h1 s hs).1], by linarith [(h1 s hs).2]⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun s hs => ⟨by linarith [(h1 s hs).1], by linarith [(h1 s hs).2]⟩, h2⟩
  have h0 := measurable_eval_canonicalFiltration_real (T := T) (zero_le : (0 : ℝ≥0) ≤ T)
  rw [hset]
  refine ((ContinuousPath.canonicalFiltration (alpha := ℝ)).le T) _ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_forall_le_lt_canonicalFiltration T
      (fun s f => max (-(f s - f 0) - e) ((f s - f 0) - H))
      (fun s hs => hF.measurable.comp ((measurable_eval_canonicalFiltration_real hs).prodMk h0))
      (fun f => hF.comp ((f.continuous.prodMk continuous_const))) 0
  · exact ((measurable_eval_canonicalFiltration_real le_rfl).sub h0) measurableSet_Ioo

/-- **The killed interval kernel near the lower barrier** (`KilledBarrierPositive`). -/
theorem killedBarrierPositive : KilledBarrierPositive := by
  intro Ω _ P _ B hB T H y₁ y₂ hT hy₁ hy₁₂ hy₂
  obtain ⟨c, hc, hcb⟩ := exists_le_planarBrownianMotion_killedStrip hT hy₁ hy₁₂ hy₂
  refine ⟨c, hc, fun e he0 he1 => ?_⟩
  obtain ⟨D, hDm, hDB, hDind, hDc⟩ := LatticeProb.IsBrownianReal.exists_continuous_indistinguishable hB
  set E := killedIncrementSet e H y₁ y₂ T with hEdef
  have hE := measurableSet_killedIncrementSet e H y₁ y₂ T
  -- the event of `B` is the event of its continuous modification, up to a null set
  have hBD : {ω | (∀ s ≤ T, -e < B s ω - B 0 ω ∧ B s ω - B 0 ω < H) ∧ B T ω - B 0 ω ∈ Ioo y₁ y₂} =ᵐ[P]
      LatticeProb.pathMap D hDc ⁻¹' E := by
    filter_upwards [hDind] with ω hω
    simp only [hEdef, killedIncrementSet, mem_preimage, LatticeProb.pathMap, hω]
    rfl
  rw [measure_congr hBD, ← Measure.map_apply (LatticeProb.measurable_pathMap D hDm hDc) hE,
    map_pathMap_eq_brownianMotion_zero hDB hDm hDc]
  -- the path law is the law of the real part of planar Brownian motion
  have hplanar : brownianMotion (0 : ℝ) E = planarBrownianMotion 0 (reImPath ⁻¹' (E ×ˢ univ)) := by
    rw [← Measure.map_apply measurable_reImPath (hE.prod MeasurableSet.univ),
      planarBrownianMotion_map_reImPath, Complex.zero_re, Complex.zero_im, Measure.prod_prod,
      measure_univ, mul_one]
  rw [hplanar]
  refine (hcb e he0 he1).trans (measure_mono_ae ?_)
  filter_upwards [ae_planarBrownianMotion_eval_zero (0 : ℂ)] with ω hω0 hω
  obtain ⟨h1, h2⟩ := hω
  simp only [mem_preimage, mem_prod, mem_univ, and_true, hEdef, killedIncrementSet, mem_ofPred_eq,
    reImPath_fst_apply, hω0, Complex.zero_re, sub_zero]
  exact ⟨h1, h2⟩

end MatedCRT.PeanosphereTriplePoints
