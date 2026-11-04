import MatedCRT.Proofs.Sec6.AnnulusHit.FieldTightness
import MatedCRT.Proofs.Infra.LogKernel

/-!
# Logarithmic potential on the unit annulus

The dyadic volume bound gives the deterministic potential estimate used in
the tightness argument. The field-law bridge uses Leonardo Bonanno's
circle-average interface.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set Metric Topology HarmonicBalls
open scoped ENNReal

/-- The unit-annulus logarithmic potential is bounded by the potential on the
containing ball. -/
theorem goodAnnulus_potential_le_ball (m : Measure ℂ) :
    (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
      ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂m) ≤
      largestExitTimeRV m (ball 0 2) := by
  have hsub : annulus (0 : ℂ) 1 (2 * 1) ⊆ ball 0 2 := by
    intro x hx
    simpa only [mul_one] using hx.1
  have heq : (⨆ v ∈ annulus (0 : ℂ) 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
      ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂m) =
      largestExitTimeRV m (annulus 0 1 (2 * 1)) := by
    unfold largestExitTimeRV
    simp only [norm_sub_rev]
  rw [heq]
  exact largestExitTimeRV_mono m hsub

/-- A dyadic volume bound on a surrounding ball implies finiteness of the
unit-annulus logarithmic potential. -/
theorem goodAnnulus_potential_lt_top_of_dyadic {m : Measure ℂ} {r β : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hβ : 0 < β)
    (hV : DyadicVolumeBound m 3 r β) :
    (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
      ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂m) < ∞ :=
  (goodAnnulus_potential_le_ball m).trans_lt
    (largestExitTimeRV_ball_zero_lt_top_of_dyadic hr hr1 hβ (by norm_num) hV)

/-- Polynomial failure bounds for a uniform volume estimate imply almost-sure
finiteness of the unit-annulus logarithmic potential. -/
theorem goodAnnulus_potential_ae_finite_of_volume_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {β p K r₀ : ℝ} (hβ : 0 < β) (hp : 0 < p) (hr₀ : 0 < r₀)
    (hV : ∀ s : ℝ, 0 < s → s < r₀ →
      P {ω | ∀ z ∈ ball (0 : ℂ) 3,
        μ ω (ball z s) ≤ ENNReal.ofReal (s ^ β)}ᶜ ≤ ENNReal.ofReal (K * s ^ p)) :
    ∀ᵐ ω ∂P, (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
      ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂(μ ω)) < ∞ := by
  have hdy : ∀ r : ℝ, 0 < r → r < r₀ →
      P {ω | DyadicVolumeBound (μ ω) 3 r β}ᶜ ≤
        ENNReal.ofReal (max K 0 * (1 - (1 / 2) ^ p)⁻¹ * r ^ p) := by
    intro r hr hrr
    refine measure_compl_iInter_le hp hV hr hrr ?_
    intro ω hω z hz k
    exact (mem_iInter.mp hω k) z hz
  rw [ae_iff]
  refine le_antisymm (ge_of_tendsto
    (tendsto_ofReal_mul_rpow (max K 0 * (1 - (1 / 2) ^ p)⁻¹) 1 p hp) ?_) zero_le
  filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ (by norm_num : (0 : ℝ) < 1))] with r hr
  have hr0 : 0 < r := hr.1
  have hrr : r < r₀ := hr.2.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := (hr.2.trans_le (min_le_right _ _)).le
  have hsub : {ω | ¬ (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
      ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂(μ ω)) < ∞} ⊆
      {ω | DyadicVolumeBound (μ ω) 3 r β}ᶜ := by
    intro ω hω hv
    exact hω (goodAnnulus_potential_lt_top_of_dyadic hr0 hr1 hβ hv)
  simpa only [one_mul] using (measure_mono hsub).trans (hdy r hr0 hrr)

/-- For a whole-plane realization, a polynomial upper-volume tail implies a
good-annulus probability bound that is uniform across realizations. -/
theorem wholePlane_goodAnnulus_uniform_of_volume_tail
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {β q K r₀ : ℝ} (hβ : 0 < β) (hq : 0 < q) (hr₀ : 0 < r₀)
    (hV : ∀ s : ℝ, 0 < s → s < r₀ →
      P {ω | ∀ z ∈ ball (0 : ℂ) 3,
        μ ω (ball z s) ≤ ENNReal.ofReal (s ^ β)}ᶜ ≤ ENNReal.ofReal (K * s ^ q))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5)
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
      P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C 1 0} ≤ ENNReal.ofReal (1 - p) :=
  wholePlane_goodAnnulus_uniform_of_ae_finite_potential hγ hγ2 h hμ hc₀ hc₀'
    (goodAnnulus_potential_ae_finite_of_volume_tail hβ hq hr₀ hV) hp

end MatedCRT.Field
