import MatedCRT.FirstPass.S3t.Bounds
import MatedCRT.FirstPass.S3t.BoundaryShells
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkExitMeasurable

/-!
# Truncated quenched laws, Step 11: integrating the pathwise estimate

Step 11 of the truncated-laws argument.

For a fixed environment `ω` and a fixed mesh scale `ε` with `m_ε > 0`, the quenched discrete occupation `A ε ω` and the
stopped occupation `C ε ω` are integrals against the quenched simple-random-walk law `ν`. Step 10 gives a pathwise bound
for `ν`-almost every walk `q` on the mesh-good event, with the shell functional `R` as the error term. Step 11 integrates
that bound: `|A - C| ≤ c + M · ∫ R dν`.

Integrability uses boundedness (Step 1: `abs_quenchedDiscreteOccupation_le`, `abs_stoppedOccupation_le`) and
measurability in the walk variable `q`. The measurability of the discrete occupation is proved here
(`measurable_quenchedDiscreteOccupation`). Measurability of the stopped occupation and of the shell functional in `q` is not
written in the answer; it enters `S3t.lean` as a named hypothesis.

Terminology: Duplantier–Sheffield (Liouville Brownian motion, boundary-shell functionals), Berestycki–Gwynne (quenched
random-walk laws on mated-CRT maps).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- Abstract Step 11. If `f`, `g`, `h` are integrable for a probability measure `ν`, `M ≥ 0`, and
`|f - g| ≤ c + M · h` holds `ν`-almost everywhere, then `|∫ f - ∫ g| ≤ c + M · ∫ h`. -/
theorem abs_integral_sub_le_of_ae_bound {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f g h : α → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) (hh : Integrable h ν) {c M : ℝ}
    (hpath : ∀ᵐ q ∂ν, |f q - g q| ≤ c + M * h q) :
    |∫ q, f q ∂ν - ∫ q, g q ∂ν| ≤ c + M * ∫ q, h q ∂ν := by
  rw [← integral_sub hf hg]
  have h1 : |∫ q, (f q - g q) ∂ν| ≤ ∫ q, |f q - g q| ∂ν := by
    have := norm_integral_le_integral_norm (μ := ν) (fun q => f q - g q)
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∫ q, |f q - g q| ∂ν ≤ ∫ q, (c + M * h q) ∂ν :=
    integral_mono_ae (hf.sub hg).abs ((integrable_const c).add (hh.const_mul M)) hpath
  have h3 : ∫ q, (c + M * h q) ∂ν = c + M * ∫ q, h q ∂ν := by
    rw [integral_add (integrable_const c) (hh.const_mul M), integral_const, integral_const_mul]
    simp
  linarith

/-- The quenched discrete occupation `q ↦ Q_ε(ω, g, T, q)` is measurable on the walk space `ℕ → ℤ`: a finite sum of
indicators of events determined by finitely many coordinates, times a measurable function of one coordinate. -/
theorem measurable_quenchedDiscreteOccupation {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (D : Set ℂ) {g : ℂ → ℝ} (hg : Measurable g) (T ε : ℝ) :
    Measurable (fun q : ℕ → ℤ => quenchedDiscreteOccupation S ω D g T ε q) := by
  unfold quenchedDiscreteOccupation
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · have hset : {q : ℕ → ℤ | ∀ j ≤ k, q j ∈ interiorCellVertices ε (S.η ω) D} =
        ⋂ j, ⋂ (_ : j ≤ k), (fun q : ℕ → ℤ => q j) ⁻¹' interiorCellVertices ε (S.η ω) D := by
      ext q
      simp
    rw [hset]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurable_pi_apply j) MeasurableSet.of_discrete
  · exact hg.comp ((measurable_of_countable (vertexPoint ε (S.η ω))).comp (measurable_pi_apply k))

/-- Step 11 for one environment `ω` and one mesh scale `ε`: if the pathwise bound `|Q - C| ≤ c + M · R` holds
`ν`-a.e. on the walk space, then the integrated quenched discrete and stopped occupations satisfy the same bound with
`R` replaced by its `ν`-integral. Here `W q` is the interpolated walk, `Rq q` the shell functional of the walk. -/
theorem abs_quenchedDiscrete_sub_stopped_integral_le {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {D : Set ℂ} {g : ℂ → ℝ} (hgm : Measurable g) {T M ε c : ℝ} (hg : ∀ x, |g x| ≤ M) (hT : 0 ≤ T)
    (hm : 0 < S.mε ε) {ν : Measure (ℕ → ℤ)} [IsProbabilityMeasure ν] {W : (ℕ → ℤ) → ℝ≥0 → ℂ} {Rq : (ℕ → ℤ) → ℝ}
    (hCm : Measurable (fun q => stoppedOccupation D T g (W q)))
    (hRm : Measurable Rq) (hR0 : ∀ q, 0 ≤ Rq q) (hRT : ∀ q, Rq q ≤ T)
    (hpath : ∀ᵐ q ∂ν, |quenchedDiscreteOccupation S ω D g T ε q - stoppedOccupation D T g (W q)| ≤ c + M * Rq q) :
    |∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂ν - ∫ q, stoppedOccupation D T g (W q) ∂ν|
      ≤ c + M * ∫ q, Rq q ∂ν := by
  have hAm := measurable_quenchedDiscreteOccupation S ω D hgm T ε
  have hAi : Integrable (fun q => quenchedDiscreteOccupation S ω D g T ε q) ν :=
    Integrable.of_bound hAm.aestronglyMeasurable (T * M) (ae_of_all _ fun q => by
      rw [Real.norm_eq_abs]
      exact abs_quenchedDiscreteOccupation_le S ω hg hT hm q)
  have hCi : Integrable (fun q => stoppedOccupation D T g (W q)) ν :=
    Integrable.of_bound hCm.aestronglyMeasurable (T * M) (ae_of_all _ fun q => by
      rw [Real.norm_eq_abs]
      exact abs_stoppedOccupation_le hg hT (W q))
  have hRi : Integrable Rq ν :=
    Integrable.of_bound hRm.aestronglyMeasurable T (ae_of_all _ fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hR0 q)]
      exact hRT q)
  exact abs_integral_sub_le_of_ae_bound hAi hCi hRi hpath

/-- The deterministic error of Step 11, `T C (2 ε^α)^χ + 4 M m_ε⁻¹`, tends to `0` along `𝓝[>] 0` when `α, χ > 0` and
`m_ε⁻¹ → 0` (Steps 7 and 8). -/
theorem tendsto_deterministicError {T C χ α M : ℝ} {mInv : ℝ → ℝ} (hα : 0 < α) (hχ : 0 < χ)
    (hmInv : Tendsto mInv (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => T * C * (2 * ε ^ α) ^ χ + 4 * M * mInv ε) (𝓝[>] 0) (𝓝 0) := by
  have hpow : ∀ β : ℝ, 0 < β → Tendsto (fun ε : ℝ => ε ^ β) (𝓝[>] 0) (𝓝 0) := by
    intro β hβ
    have h : Tendsto (fun x : ℝ => x ^ β) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hβ.ne'] using (Real.continuousAt_rpow_const (0 : ℝ) β (Or.inr hβ.le)).tendsto
    exact h.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun ε : ℝ => (2 * ε ^ α) ^ χ) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ χ) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hχ.ne'] using (Real.continuousAt_rpow_const (0 : ℝ) χ (Or.inr hχ.le)).tendsto
    have h2 : Tendsto (fun ε : ℝ => 2 * ε ^ α) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hpow α hα).const_mul 2
    exact h.comp h2
  have := (h1.const_mul (T * C)).add (hmInv.const_mul (4 * M))
  simpa only [mul_zero, add_zero] using this

/-- Measurability in the walk variable of the stopped occupation of the interpolated walk, for the ball `ball z r`
(Duplantier–Sheffield truncated occupation `∫_{(0, min (T, τ_D)]} g(W_t) dt` with `D = B_r(z)`). Fubini, as in
`MatedCRT.aestronglyMeasurable_truncatedOccupation_interpolatedWalk`, with the `ENNReal` truncation of `stoppedOccupation`. -/
theorem measurable_stoppedOccupation_interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (z : ℂ) (r T : ℝ)
    {g : ℂ → ℝ} (hg : Continuous g) :
    Measurable (fun x : ℕ → ℤ => stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε η m x)) := by
  have hτ : Measurable (fun x : ℕ → ℤ => pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x)) :=
    MatedCRT.measurable_pathExitTime_interpolatedWalk ε η m z r
  have ha : Measurable (fun x : ℕ → ℤ =>
      (min (ENNReal.ofReal T) (pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x))).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_const.min hτ)
  have hu : Measurable (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
      g (interpolatedWalk ε η m x t.toNNReal)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun x => hg.comp ((MatedCRT.continuous_interpolatedWalk ε m η x).comp continuous_real_toNNReal))
      (fun t => hg.measurable.comp (MatedCRT.measurable_interpolatedWalk_apply ε η m t.toNNReal))
  set E : Set (ℝ × (ℕ → ℤ)) :=
    {q | 0 < q.1} ∩ {q | q.1 ≤ (min (ENNReal.ofReal T)
      (pathExitTime (Metric.ball z r) (interpolatedWalk ε η m q.2))).toReal} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (ha.comp measurable_snd))
  have hFm := hu.indicator hEm
  have hsm : StronglyMeasurable (fun x : ℕ → ℤ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
        g (interpolatedWalk ε η m x t.toNNReal)) (t, x)) :=
    StronglyMeasurable.integral_prod_left' hFm.stronglyMeasurable
  have heq : (fun x : ℕ → ℤ => stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε η m x)) =
      fun x : ℕ → ℤ => ∫ t : ℝ,
        E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
          g (interpolatedWalk ε η m x t.toNNReal)) (t, x) := by
    funext x
    unfold stoppedOccupation
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [heq]
  exact hsm.measurable

/-- Measurability in the walk variable of the truncated shell functional `shellTime (D_n) (B_r(z)) T` of the
interpolated walk, for the concentric exhaustion `D_n = ballExhaustion z r a n` (Step 6). Both exit times are exit times of
balls, so `MatedCRT.measurable_pathExitTime_interpolatedWalk` applies to each. -/
theorem measurable_shellTime_interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (m : ℝ) (z : ℂ) (r a T : ℝ) (n : ℕ) :
    Measurable (fun x : ℕ → ℤ =>
      shellTime (ballExhaustion z r a n) (Metric.ball z r) T (interpolatedWalk ε η m x)) := by
  unfold shellTime ballExhaustion
  have h1 : Measurable (fun x : ℕ → ℤ =>
      (min (ENNReal.ofReal T) (pathExitTime (Metric.ball z r) (interpolatedWalk ε η m x))).toReal) :=
    ENNReal.measurable_toReal.comp
      (measurable_const.min (MatedCRT.measurable_pathExitTime_interpolatedWalk ε η m z r))
  have h2 : Measurable (fun x : ℕ → ℤ =>
      (min (ENNReal.ofReal T)
        (pathExitTime (Metric.ball z (r - a / ((n : ℝ) + 1))) (interpolatedWalk ε η m x))).toReal) :=
    ENNReal.measurable_toReal.comp
      (measurable_const.min (MatedCRT.measurable_pathExitTime_interpolatedWalk ε η m z (r - a / ((n : ℝ) + 1))))
  exact h1.sub h2

end MatedCRT.TruncatedLaws
