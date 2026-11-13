import MatedCRT.FirstPass.Derived.GmcGreenApprox
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockAnnealedCauchy
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Green-weighted chaos limit for the field `h^ℂ - γ log |·|` of a whole-plane GFF

Let `h^ℂ` be a whole-plane GFF (`IsWholePlaneGFF`) and `0 < γ < 2`. Almost surely, the cut-off circle-average
approximations `gmcApproxCut γ ρ ρ₂ k ψ` of the γ-LQG measure of `h = h^ℂ - γ log |·|` (with
`ψ = clockPsi (fieldCircleAverage γ ∘ hcirc)`) are eventually finite on compact sets and converge vaguely to the
measurable cut-off limit `gmcLimit γ ρ ρ₂ ψ` (`ae_gmcApproxCut_finite_and_isVagueLimitOn_gff`). The LQG measure used
is the one of `lqgMeasureExistence_derived` at `α₀ = γ < Q` (Duplantier-Sheffield 2011, Prop. 1.1).

Combined with `tendsto_two_mul_setLIntegral_green_regWeight`, almost surely and simultaneously for every disc
`D = B_r(z) ⊆ closedBall 0 ρ`, every `y ∈ D`, every sequence of dyadic scales `n k → ∞` and every continuous `g ≥ 0`
with compact support in `D` vanishing near `y`,
`2 ∫_D G_D(y, x) w_{n k}(x) g(x) dx → ∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`
(`ae_tendsto_two_mul_setLIntegral_green_regWeight_gff`), where `w_k = ε_k^{γ²/2} e^{γ h_{ε_k}}`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Almost-sure vague convergence of the cut-off approximations for `h^ℂ - γ log |·|`.** For a whole-plane GFF
`h^ℂ`, `0 < γ < 2` and `ρ < ρ₂ < 1`, almost surely the cut-off circle-average approximations of the γ-LQG measure of
`h^ℂ - γ log |·|` are eventually finite on compact sets and converge vaguely to `gmcLimit γ ρ ρ₂`. -/
theorem ae_gmcApproxCut_finite_and_isVagueLimitOn_gff {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ} (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω' ∂P',
      (∀ K, IsCompact K → ∀ᶠ k in atTop,
        gmcApproxCut γ ρ ρ₂ k (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') K < ∞) ∧
      QuantumZipper.IsVagueLimitOn univ
        (fun k => gmcApproxCut γ ρ ρ₂ k (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω'))
        (gmcLimit γ ρ ρ₂ (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')) := by
  have hQ : γ < lqgQ γ := by
    have h : γ * (lqgQ γ - γ) = 2 - γ ^ 2 / 2 := by unfold lqgQ; field_simp; ring
    nlinarith
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P' γ γ hC' hc hG hγ hγ2 hQ
  filter_upwards [hμ, hG.ae_continuousOn_circle] with ω' hL hcc
  have hcF := continuousOn_fieldCircleAverage (α₀ := γ) hcc
  have hψ : Continuous (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') :=
    hcF.comp_continuous continuous_subtype_val (fun q => ⟨q.2.1, mem_univ _⟩)
  have hHc : ∀ ε : ℝ, 0 < ε → Continuous fun x => fieldCircleAverage γ (hc ω') ε x := fun ε hε =>
    hcF.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hε, mem_univ _⟩
  obtain ⟨hfin, hlim⟩ :=
    gmcApproxCut_finite_and_isVagueLimitOn_of_continuous hρρ₂ hρ₂ hψ (fun _ => rfl) hL hHc
  refine ⟨hfin, ?_⟩
  rwa [gmcLimit_eq hfin hlim]

/-- **Green-weighted chaos limit for `h^ℂ - γ log |·|` (chaos side of the Revuz identity).** For a whole-plane GFF
`h^ℂ`, `0 < γ < 2` and `ρ < ρ₂ < 1`, almost surely: for every disc `D = B_r(z) ⊆ closedBall 0 ρ`, every `y ∈ D`, every
sequence `n k → ∞` and every continuous `g ≥ 0` with compact support in `D` and `y ∉ tsupport g`,
`2 ∫_D G_D(y, x) w_{n k}(x) g(x) dx → ∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`, where
`w_k = ε_k^{γ²/2} e^{γ h_{ε_k}}` is the circle-average weight of `h = h^ℂ - γ log |·|` at `ε_k = 2^{-k}`. -/
theorem ae_tendsto_two_mul_setLIntegral_green_regWeight_gff {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) :
    ∀ᵐ ω' ∂P', ∀ (z y : ℂ) (r : ℝ), ball z r ⊆ closedBall 0 ρ → y ∈ ball z r →
      ∀ n : ℕ → ℕ, Tendsto n atTop atTop → ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
        HasCompactSupport g → tsupport g ⊆ ball z r → y ∉ tsupport g →
        Tendsto (fun k => 2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
            (ENNReal.ofReal (dyadicScale (n k) ^ (γ ^ 2 / 2) *
              Real.exp (γ * circleAverageRep (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
                (dyadicScale (n k)) x)) * ENNReal.ofReal (g x)))
          atTop (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
            (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω'))) := by
  filter_upwards [ae_gmcApproxCut_finite_and_isVagueLimitOn_gff hG hγ hγ2 hρρ₂ hρ₂]
    with ω' hω z y r hD hy n hn g hgc hg0 hgK hgD hgy
  exact tendsto_two_mul_setLIntegral_green_regWeight hρρ₂ hD hy hω.1 hω.2 hn hgc hg0 hgK hgD hgy

end MatedCRT.KilledOccupation
