import MatedCRT.FirstPass.Derived.RegClockIntegralMeasurable
import MatedCRT.FirstPass.Derived.RegClockAnnealedLimit
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockOccupationMeasure
import LatticeProb.Prob.ProductSectionVitali

/-!
# The Brownian expectation of the limiting occupation clock

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ` (`0 < γ < 2`), let `b` be a planar Brownian motion
started at `y ∈ D = B_r(z)` and killed on exiting `D`, and let `n_k → ∞` be a subsequence along which the regularized
occupation clocks `w_{2^{-n_k}}(b_u) du` converge for `P' ⊗ P_y`-almost every `(ω', b)` to the limiting clock
`limClockKernel`. For a continuous `g ≥ 0` with compact support in `D` and `y ∉ tsupport g`, write
`A_k(ω', b) = ∫_0^{σ_D(b)} g(b_u) w_{2^{-n_k}}(b_u) du`.

If the real parts of `A_k` are uniformly integrable for `P' ⊗ P_y`, then almost surely in the field
`E_y ∫_0^{σ_D} g(b_u) dA^∞_u = ∫ g d(1_D · 2 G_D(y, ·) · Γ)`, with `A^∞` the limiting clock and `Γ` the cut-off
γ-LQG measure (`ae_lintegral_limClockKernel_eq_gmcGreenMeasure`). The proof identifies the limit of the section
integrals (`LatticeProb.Prob.ae_lintegral_section_eq_of_uniformIntegrable`): the almost-sure convergence on the product
space is `ae_prod_tendsto_setLIntegral_regClockMeasure`, and the annealed limit of the section integrals is
`ae_tendsto_lintegral_setLIntegral_regClockMeasure`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Occupation identity of the limiting clock, from uniform integrability.** For a whole-plane GFF `h^ℂ`,
`0 < γ < 2`, `ρ < ρ₂ < 1`, a disc `D = B_r(z) ⊆ B_ρ(0)` with pole `y ∈ D`, a strictly increasing `n` with
`2^{-n_0} < 1 - ρ` and summable clock gaps (`hgapLaw`), and a continuous `g ≥ 0` with compact support in `D` and
`y ∉ tsupport g`: if the regularized clock integrals `A_k(ω', b)` of `g` have uniformly integrable real parts for
`P' ⊗ P_y`, then for `P'`-almost every `ω'` the Brownian expectation of the integral of `g(b_u)` against the limiting
clock on `[0, σ_D(b)]` equals `∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`. -/
theorem ae_lintegral_limClockKernel_eq_gmcGreenMeasure {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {g : ℂ → ℝ} (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgK : HasCompactSupport g)
    (hgD : tsupport g ⊆ ball z r) (hgy : y ∉ tsupport g)
    (hui : UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', ∫⁻ b, (∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
        ∂limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r)
          (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω', b)) ∂planarBrownianMotion y =
      ∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') := by
  obtain ⟨C, hC⟩ := hgK.exists_bound_of_continuous hgc
  have hgC : ∀ x, g x ≤ C := fun x => (le_abs_self (g x)).trans (by simpa only [Real.norm_eq_abs] using hC x)
  have hD : ball z r ⊆ closedBall 0 ρ := hball.trans ball_subset_closedBall
  have hfg := ae_prod_tendsto_setLIntegral_regClockMeasure hG γ ρ r z y hball n hn hn0 hgapLaw
  have hL := ae_tendsto_lintegral_setLIntegral_regClockMeasure hG hγ hγ2 hρρ₂ hρ₂ hD hy hB
  refine LatticeProb.Prob.ae_lintegral_section_eq_of_uniformIntegrable
    (f := fun k (p : Ω' × ContinuousPath ℂ) => ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
      ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
        (exitNN z r) p.2)
    (g := fun p => ∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
      ∂limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r)
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1, p.2))
    (fun k => (measurable_prod_setLIntegral_regClockMeasure hG γ (dyadicScale (n k)) r z hgc.measurable).aemeasurable)
    (fun k => ae_prod_setLIntegral_regClockMeasure_ne_top hG γ ρ r z y hball n hn hn0 hgapLaw hgc.measurable hgC k)
    hui ?_ ?_
  · filter_upwards [hfg] with p hp
    exact hp g hgc hg0
  · filter_upwards [hL] with ω' hω
    exact hω n hn.tendsto_atTop g hgc hg0 hgK hgD hgy

/-- `ae_lintegral_limClockKernel_eq_gmcGreenMeasure` from the bounded-integrand form `KilledBrownianOccupationOnBall`
of the Brownian occupation identity. -/
theorem ae_lintegral_limClockKernel_eq_gmcGreenMeasure_of_killed {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hK : KilledBrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {g : ℂ → ℝ} (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgK : HasCompactSupport g)
    (hgD : tsupport g ⊆ ball z r) (hgy : y ∉ tsupport g)
    (hui : UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', ∫⁻ b, (∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
        ∂limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r)
          (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω', b)) ∂planarBrownianMotion y =
      ∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') :=
  ae_lintegral_limClockKernel_eq_gmcGreenMeasure hG hγ hγ2 hρρ₂ hρ₂ hball hy
    (brownianOccupationOnBall_of_killed hK) hn hn0 hgapLaw hgc hg0 hgK hgD hgy hui

/-- **Test-function form of the Revuz identity.** Under the hypotheses of
`ae_lintegral_limClockKernel_eq_gmcGreenMeasure`, for `P'`-almost every `ω'` the expected occupation measure of the
limiting clock (Brownian motion started at `y`, killed on exiting `D`) and the Green-weighted γ-LQG measure
`1_D · 2 G_D(y, ·) · Γ` give the same integral to `g`. -/
theorem ae_lintegral_limClockOccupationMeasure_eq_gmcGreenMeasure {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r)
    (hB : BrownianOccupationOnBall z r) {n : ℕ → ℕ} (hn : StrictMono n) (hn0 : dyadicScale (n 0) < 1 - ρ)
    (hgapLaw : ∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    {g : ℂ → ℝ} (hgc : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgK : HasCompactSupport g)
    (hgD : tsupport g ⊆ ball z r) (hgy : y ∉ tsupport g)
    (hui : UniformIntegrable (fun k (p : Ω' × ContinuousPath ℂ) =>
        (∫⁻ u in Icc 0 (exitNN z r p.2), ENNReal.ofReal (g (p.2 u))
          ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) p.1)
            (exitNN z r) p.2).toReal) 1 (P'.prod (planarBrownianMotion y))) :
    ∀ᵐ ω' ∂P', ∫⁻ x, ENNReal.ofReal (g x) ∂limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r
        (planarBrownianMotion y) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') =
      ∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
        (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') := by
  filter_upwards [ae_lintegral_limClockKernel_eq_gmcGreenMeasure hG hγ hγ2 hρρ₂ hρ₂ hball hy hB hn hn0 hgapLaw
    hgc hg0 hgK hgD hgy hui] with ω' hω
  rw [lintegral_limClockOccupationMeasure _ _ _ _ _ _ (g := fun x => ENNReal.ofReal (g x))
    hgc.measurable.ennreal_ofReal]
  exact hω

end MatedCRT.KilledOccupation
