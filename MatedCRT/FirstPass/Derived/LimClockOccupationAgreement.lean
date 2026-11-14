import MatedCRT.FirstPass.Derived.LimClockOccupationOnDisc
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds

/-!
# Agreement of the occupation measure of the limiting Liouville clock with the Green-weighted LQG measure

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ` (`0 < γ < 2`). The cut-off chaos limit
`Γ = gmcLimit γ ρ ρ₂` of the circle averages of `h` is almost surely the γ-LQG measure `μ_h` of `h` times a cut-off
function (`ae_gmcLimit_eq_withDensity`), and `μ_h` has no atoms (Duplantier-Sheffield 2011; `lqgMeasureNonatomic_holds`,
existence at the insertion `α₀ = γ < Q`). Hence almost surely `Γ` and the Green-weighted measure
`m₂ = 1_D · 2 G_D(y, ·) · Γ` (`gmcGreenMeasure`) have no atoms, for all discs `D = B_r(z)` and poles `y` at once.

With the identification of the expected occupation measure `m₁` of the limiting clock on the punctured disc
(`ae_restrict_ball_limClockOccupationMeasure_eq`), this gives almost surely `m₁|_D = m₂`, and, for `y ≠ 0`, that the
occupation-agreement event holds: `m₁(D) < ∞` and `m₁ S = m₂ S` for every measurable `S ⊆ D`.

## Main results

* `ae_gmcLimit_singleton_gff`: a.s. `Γ{x} = 0` for every `x`;
* `ae_gmcGreenMeasure_singleton_gff`: a.s. `m₂{x} = 0` for all `z, y, r, x`;
* `ae_restrict_ball_limClockOccupationMeasure_eq_gmcGreenMeasure`: a.s. `m₁|_D = m₂`;
* `ae_mem_occupationAgreementEvent_of_ne_zero`: for `y ≠ 0` and `ρ₂ = (1 + ρ)/2`, a.s. the circle averages lie in the
  occupation-agreement event of `m₁`, `m₂`, `D` and any family `C` of measurable subsets of `D`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **The cut-off chaos limit has no atoms.** For a whole-plane GFF `h^ℂ`, `0 < γ < 2` and `ρ < ρ₂ < 1`, almost surely
the cut-off γ-LQG chaos limit of `h^ℂ - γ log |·|` gives no mass to any point. -/
theorem ae_gmcLimit_singleton_gff {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω' ∂P', ∀ x : ℂ,
      gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') {x} = 0 := by
  have hQ : γ < lqgQ γ := by
    have h : γ * (lqgQ γ - γ) = 2 - γ ^ 2 / 2 := by unfold lqgQ; field_simp; ring
    nlinarith
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P' γ γ hC' hc hG hγ hγ2 hQ
  have hcont : ∀ᵐ ω' ∂P', ContinuousOn (fun p : ℝ × ℂ => fieldCircleAverage γ (hc ω') p.1 p.2)
      (Ioi 0 ×ˢ univ) :=
    hG.ae_continuousOn_circle.mono fun _ hcc => continuousOn_fieldCircleAverage (α₀ := γ) hcc
  filter_upwards [ae_gmcLimit_eq_withDensity hμ hcont hρρ₂ hρ₂,
    lqgMeasureNonatomic_holds _ P' γ γ hC' hc hG hγ hγ2 hQ μ hμ] with ω' heq hat x
  have h1 : gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') =
      (μ ω').withDensity fun x => ENNReal.ofReal (gmcCutoff ρ ρ₂ x) := heq
  rw [h1]
  exact withDensity_absolutelyContinuous _ _ (hat x)

/-- **The Green-weighted chaos limit has no atoms.** Almost surely, for every disc `B_r(z)`, pole `y` and point `x`,
the measure `1_D · 2 G_D(y, ·) · Γ` gives no mass to `x`. -/
theorem ae_gmcGreenMeasure_singleton_gff {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω' ∂P', ∀ (z y : ℂ) (r : ℝ) (x : ℂ),
      gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') {x} = 0 := by
  filter_upwards [ae_gmcLimit_singleton_gff hG hγ hγ2 hρρ₂ hρ₂] with ω' h z y r x
  exact withDensity_absolutelyContinuous
    (gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) (greenOccupationDensity z y r) (h x)

/-- **Identification of the expected occupation measure of the limiting clock.** Under the hypotheses of
`ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure` (in particular the uniform integrability `hui` of the
regularized clock integrals of the test functions of `D ∖ {0, y}`), almost surely the expected occupation measure of
the limiting clock restricted to `D` is the Green-weighted γ-LQG measure `1_D · 2 G_D(y, ·) · Γ`. -/
theorem ae_restrict_ball_limClockOccupationMeasure_eq_gmcGreenMeasure {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
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
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y)
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')).restrict (ball z r) =
      gmcGreenMeasure γ ρ ρ₂ z y r (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') := by
  filter_upwards [ae_restrict_ball_limClockOccupationMeasure_eq hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn hn0 hgapLaw hui,
    ae_gmcGreenMeasure_singleton_gff hG hγ hγ2 hρρ₂ hρ₂] with ω' h1 h2
  rw [h1, Measure.restrict_congr_set (sdiff_null_ae_eq_self ?_)]
  · exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (gmcGreenMeasure_compl_ball γ ρ ρ₂ z y r _))
  · rw [Set.insert_eq]
    exact measure_union_null (h2 z y r 0) (h2 z y r y)

/-- **The occupation-agreement event away from the singularity.** For `0 < ρ < 1`, `ρ₂ = (1 + ρ)/2`, a disc
`D = B_r(z) ⊆ B_ρ(0)` and a pole `y ∈ D` with `y ≠ 0`, under the hypotheses of
`ae_restrict_limClockOccupationMeasure_eq_gmcGreenMeasure`, almost surely the circle averages lie in the
occupation-agreement event: the expected occupation measure of the limiting clock is finite on `D` and agrees with
`1_D · 2 G_D(y, ·) · Γ` on every member of a family `C` of measurable subsets of `D`. -/
theorem ae_mem_occupationAgreementEvent_of_ne_zero {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ}
    (hρ1 : ρ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) (hy0 : y ≠ 0)
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
  have hρρ₂ : ρ < (1 + ρ) / 2 := by linarith
  have hρ₂ : (1 + ρ) / 2 < 1 := by linarith
  filter_upwards [ae_limClockOccupationMeasure_ball_lt_top hG hγ hγ2 hρρ₂ hρ₂ hball hy hy0 hB hn hn0 hgapLaw hui,
    ae_restrict_ball_limClockOccupationMeasure_eq_gmcGreenMeasure hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn hn0
      hgapLaw hui] with ω' hfin heq
  refine (show _ ∧ _ from ⟨hfin, fun S hS => ?_⟩)
  rw [← heq, Measure.restrict_apply (hC S hS).1, Set.inter_eq_left.2 (hC S hS).2]

end MatedCRT.KilledOccupation
