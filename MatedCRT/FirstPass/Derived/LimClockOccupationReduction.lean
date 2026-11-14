import MatedCRT.FirstPass.Derived.LimClockOccupationAgreement
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosureCone

/-!
# Reduction of the occupation identity of the Liouville clock to three inputs

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ` (`0 < γ < 2`), `Γ` the cut-off chaos limit of its
circle averages, `D = B_r(z) ⊆ B_ρ(0)` and `y ∈ D`. The occupation identity of the limiting Liouville clock on `D`
(the hypothesis `hGFF` of `frozenLBMGreenOccupationRescaled_of_coneGFFLaw`, Garban-Rhodes-Vargas 2016,
Theorem 2.7(1)) asserts that almost surely the expected occupation measure `m₁` of the limit clock, up to the exit time
of `D`, is finite on `D` and agrees on a countable family of measurable subsets of `D` with the Green-weighted measure
`m₂ = 1_D · 2 G_D(y, ·) · Γ`.

This file derives it from three inputs, taken as explicit hypotheses:

* (B) the occupation identity of planar Brownian motion killed on exiting a disc,
  `E_y ∫_0^τ f(B_t) dt = 2 ∫_D G_D(y, x) f(x) dx` (`KilledBrownianOccupationOnBall`);
* (U) uniform integrability of the regularized clock integrals `∫_0^τ g(B_u) dF_ε(u)` of nonnegative continuous test
  functions `g` compactly supported in `D ∖ {0, y}`, under the annealed law of the field and the Brownian motion;
* (F0) at the pole `y = 0`: almost surely `m₂(D) = ∫_D 2 G_D(0, x) Γ(dx) < ∞`.

For `y ≠ 0` the finiteness of `m₁(D)` was proved from (B) and (U) (`ae_mem_occupationAgreementEvent_of_ne_zero`);
for `y = 0` it follows from `m₁|_D = m₂` and (F0).

## Main results

* `ae_mem_occupationAgreementEvent_of_pole`: the occupation-agreement event for one disc, pole and dyadic sequence,
  for every pole `y ∈ D`, given the finiteness of `m₂(D)` when `y = 0`;
* `ae_mem_occupationAgreementEvent_of_killedOccupation`: the full statement of `hGFF` from (B), (U) and (F0);
* `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation`: the occupation identity of the median-rescaled
  Liouville Brownian motion on the γ-quantum cone from the law of the field, (B), (U) and (F0).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **The occupation-agreement event at every pole.** Under the hypotheses of
`ae_mem_occupationAgreementEvent_of_ne_zero`, without `y ≠ 0`, and given that at the pole `y = 0` the Green-weighted
measure `1_D · 2 G_D(0, ·) · Γ` is almost surely finite on `D`, almost surely the circle averages lie in the
occupation-agreement event of `m₁`, `m₂`, `D` and any family `C` of measurable subsets of `D`. -/
theorem ae_mem_occupationAgreementEvent_of_pole {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ}
    (hρ1 : ρ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hF0 : y = 0 → ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r
      (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (ball z r) < ∞)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (hui : ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y)))
    (C : Set (Set ℂ)) (hC : ∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) :
    ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
      occupationAgreementEvent
        (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
        (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C := by
  by_cases hy0 : y = 0
  · have hρρ₂ : ρ < (1 + ρ) / 2 := by linarith
    have hρ₂ : (1 + ρ) / 2 < 1 := by linarith
    filter_upwards [hF0 hy0, ae_restrict_ball_limClockOccupationMeasure_eq_gmcGreenMeasure hG hγ hγ2 hρρ₂ hρ₂
      hball hy hB hn hn0 hgapLaw hui] with ω' hfin heq
    refine (show _ ∧ _ from ⟨?_, fun S hS => ?_⟩)
    · rw [← Measure.restrict_apply_self _ (ball z r), heq]
      exact hfin
    · rw [← heq, Measure.restrict_apply (hC S hS).1, Set.inter_eq_left.2 (hC S hS).2]
  · exact ae_mem_occupationAgreementEvent_of_ne_zero hG hγ hγ2 hρ1 hball hy hy0 hB hn hn0 hgapLaw hui C hC

/-- **The occupation identity of the Liouville clock from (B), (U) and (F0).** The statement of the hypothesis `hGFF`
of `frozenLBMGreenOccupationRescaled_of_coneGFFLaw`, derived from

* `hK`: the occupation identity of planar Brownian motion killed on exiting every disc;
* `hU`: uniform integrability of the regularized clock integrals of nonnegative continuous test functions compactly
  supported in `D ∖ {0, y}`, for every whole-plane GFF model and every admissible dyadic sequence;
* `hF0`: almost sure finiteness of `∫_D 2 G_D(0, x) Γ(dx)` when `0 ∈ D`. -/
theorem ae_mem_occupationAgreementEvent_of_killedOccupation
    (hK : ∀ (z : ℂ) (r : ℝ), 0 < r → KilledBrownianOccupationOnBall z r)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y)))
    (hF0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → (0 : ℂ) ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ((1 + ρ) / 2) z 0 r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (ball z r) < ∞) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C := by
  intro γ hγ hγ2 ρ hρ0 hρ1 r z y hr hball hy Ω' _ P' hC' hc hP hG n hn hn0 hgapLaw C _ hCm
  refine ae_mem_occupationAgreementEvent_of_pole hG hγ hγ2 hρ1 hball hy ?_
    (brownianOccupationOnBall_of_killed (hK z r hr)) hn hn0 hgapLaw
    (hU γ hγ hγ2 ρ hρ0 hρ1 r z y hr hball hy Ω' P' hC' hc hP hG n hn hn0 hgapLaw) C hCm
  rintro rfl
  exact hF0 γ hγ hγ2 ρ hρ0 hρ1 r z hr hball hy Ω' P' hC' hc hP hG

/-- **Occupation identity of the median-rescaled Liouville Brownian motion on the γ-quantum cone** from the law of the
field (`hlaw`), the occupation identity of killed planar Brownian motion (`hK`), uniform integrability of the
regularized clock integrals (`hU`) and finiteness of the Green-weighted chaos at the pole `0` (`hF0`); see
`ae_mem_occupationAgreementEvent_of_killedOccupation`. -/
theorem frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation (𝒮 : SpaceFillingSLEModel)
    (hlaw : ConeUnitDiskGFFLaw)
    (hK : ∀ (z : ℂ) (r : ℝ), 0 < r → KilledBrownianOccupationOnBall z r)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) → HasCompactSupport g →
      tsupport g ⊆ ball z r \ ({0, y} : Set ℂ) →
      UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y)))
    (hF0 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → (0 : ℂ) ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ᵐ ω' ∂P', gmcGreenMeasure γ ρ ((1 + ρ) / 2) z 0 r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') (ball z r) < ∞) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw 𝒮 hlaw
    (ae_mem_occupationAgreementEvent_of_killedOccupation hK hU hF0)

end MatedCRT.KilledOccupation
