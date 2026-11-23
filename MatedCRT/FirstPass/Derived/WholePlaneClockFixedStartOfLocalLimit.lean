import MatedCRT.FirstPass.Derived.WholePlaneClockStrictMonoOfOneStart

/-!
# Fixed-start convergence of the dyadic Liouville clocks from their locally uniform limit for the Gaussian field

The hypothesis `hfix` of `Sec1.hasReferenceEnvironments_of_coupling_wholePlane_fixedStart` asks, for the normalized
whole-plane Gaussian free field `Y'` and every continuous jointly measurable version `c'` of its circle averages, that
from Lebesgue-almost every start the dyadic clocks `A_k(t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(B_s)} ds` of `c' ∘ Y'` be
uniformly Cauchy on every `[0, T]`, almost surely for the joint law of the field and the planar Brownian path
(Berestycki 2015).

This file derives `hfix` from the convergence statement for the whole-plane GFF of `LatticeProb.Gauss`
(`LatticeProb.Gauss.IsWholePlaneGFF`, field `LatticeProb.Gauss.fieldCircleAverage 0 hcirc`): from every start `x`,
almost surely for the joint law, the clocks `A_{n+1}` converge locally uniformly on `[0, ∞)` to a continuous,
nonnegative, nondecreasing limit. The Gaussian representation of `Y'` (`MatedCRT.exists_normalizedGFF_coordinates`)
has circle averages that agree with `c' ∘ Y'` almost surely at every positive radius and centre
(`Sec1.ae_forall_eq_of_continuousOn_of_ae_eq`); this event of the field has full measure for the joint law, and on it
the two families of clocks coincide.

## Main statements

* `ae_uniformCauchy_wholePlane_fixedStart_of_localLimit`: the conclusion of `hfix` for one parameter `γ`, from every
  start.
* `wholePlane_fixedStart_uniformCauchy_of_localLimit`: the hypothesis `hfix` as typed, from the convergence statement
  for every `γ ∈ (0, 2)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology HarmonicBalls LQGMetric MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

/-- **Fixed-start convergence of the dyadic clocks from the Gaussian locally uniform limit.** Let `Y'` be a normalized
whole-plane GFF with a version `c'` of its circle averages that is continuous on `(0, ∞) × ℂ` and jointly measurable.
Suppose that for every whole-plane GFF of `LatticeProb.Gauss` and every start `x`, almost surely for the joint law of
the field and planar Brownian motion from `x`, the dyadic clocks `A_{n+1}` converge locally uniformly on `[0, ∞)` to a
continuous, nonnegative, nondecreasing limit. Then from every start `y`, almost surely for the joint law, the dyadic
clocks of `c' ∘ Y'` are uniformly Cauchy on `[0, T]`. -/
theorem ae_uniformCauchy_wholePlane_fixedStart_of_localLimit {γ : ℝ}
    (hloc : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
      {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
      ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
        ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
          ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                (q.2 s.toNNReal))) - F t| < η)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ}
    (hY : IsNormalizedWPGFF Y' P')
    (hver : ∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ))
    (T : ℝ≥0) (y : ℂ) :
    ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T) := by
  obtain ⟨hC, hcirc, hG, -, hcircEq, -⟩ := MatedCRT.exists_normalizedGFF_coordinates hY
  have hid : ∀ᵐ ω ∂P', ∀ r, 0 < r → ∀ z, hcirc ω r z = c' (Y' ω) r z :=
    ae_forall_eq_of_continuousOn_of_ae_eq (G := fun ω => c' (Y' ω)) hG.ae_continuousOn_circle
      (Eventually.of_forall fun ω => hcont (Y' ω)) fun r hr z => by
        filter_upwards [hcircEq r hr z, hver r hr z] with ω h1 h2
        exact h1.trans h2.symm
  have hid' : ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      ∀ r, 0 < r → ∀ z, hcirc p.1 r z = c' (Y' p.1) r z :=
    Measure.quasiMeasurePreserving_fst.ae hid
  filter_upwards [hloc hG y, hid'] with p hp hidp
  obtain ⟨F, -, -, -, hF⟩ := hp
  have hfun : ∀ n, LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) (HarmonicBalls.dyadicScale n) =
      c' (Y' p.1) (HarmonicBalls.dyadicScale n) := fun n => funext fun z => by
    simp only [LatticeProb.Gauss.fieldCircleAverage, zero_mul, sub_zero]
    exact hidp _ (HarmonicBalls.dyadicScale_pos n) z
  have hT : TendstoUniformlyOn
      (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t) F atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hF T η hη)
    refine eventually_atTop.2 ⟨N + 1, fun k hk t ht => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have h := hN n (by omega) t ht.2
    rw [hfun] at h
    rw [Real.dist_eq, abs_sub_comm]
    exact h
  exact hT.uniformCauchySeqOn

/-- **The convergence binder of the whole-plane reference environments from the Gaussian locally uniform limit.** The
hypothesis `hfix` of `hasReferenceEnvironments_of_coupling_wholePlane_fixedStart` follows from the locally uniform
convergence, for every `γ ∈ (0, 2)`, every whole-plane GFF of `LatticeProb.Gauss` and every start, of the dyadic clocks
`A_{n+1}` to a continuous, nonnegative, nondecreasing limit, almost surely for the joint law (Berestycki 2015). -/
theorem wholePlane_fixedStart_uniformCauchy_of_localLimit
    (hloc : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc → ∀ x : ℂ,
        ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
          ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
            ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
              |(∫ s in (0 : ℝ)..(t : ℝ), HarmonicBalls.dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (HarmonicBalls.dyadicScale (n + 1))
                  (q.2 s.toNNReal))) - F t| < η) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T) :=
  fun γ hγ0 hγ2 {_} _ {_} _ {_} {_} hY hver hcont _ T =>
    Eventually.of_forall fun y =>
      ae_uniformCauchy_wholePlane_fixedStart_of_localLimit (hloc γ hγ0 hγ2) hY hver hcont T y

end MatedCRT.Sec1
