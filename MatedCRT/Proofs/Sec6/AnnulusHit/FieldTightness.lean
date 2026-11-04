import MatedCRT.Proofs.Sec6.AnnulusHit.FieldLaw
import MatedCRT.Proofs.Sec6.AnnulusHit.EventInvariance
import MatedCRT.Proofs.Field.WholePlaneFullSupport

/-!
# Reduction of whole-plane good-annulus tightness

If the good-annulus event holds for some finite constant almost surely in one
whole-plane realization, its constants have uniform probability bounds across
all realizations. The circle-law bridge uses Leonardo Bonanno's interface.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- A finite logarithmic potential and a positive denominator give a finite
good-annulus constant. -/
theorem goodAnnulus_exists_of_finite_potential {m : Measure ℂ} {c₀ r : ℝ} {z : ℂ}
    (hL : (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
      ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂m) < ∞)
    (hR : 0 < ⨅ w ∈ annulus z r (2 * r), m (ball w (c₀ * r))) :
    ∃ C : ℝ, IsGoodAnnulusEvent m c₀ C r z := by
  let L : ℝ≥0∞ := ⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r),
    ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂m
  let R : ℝ≥0∞ := ⨅ w ∈ annulus z r (2 * r), m (ball w (c₀ * r))
  change L < ∞ at hL
  change 0 < R at hR
  by_cases hRtop : R = ∞
  · refine ⟨1, ?_⟩
    change L ≤ ENNReal.ofReal 1 * R
    rw [hRtop]
    simp
  · have hquot : L / R < ∞ := ENNReal.div_lt_top hL.ne hR.ne'
    refine ⟨(L / R).toReal, ?_⟩
    change L ≤ ENNReal.ofReal (L / R).toReal * R
    rw [ENNReal.ofReal_toReal hquot.ne, ENNReal.div_mul_cancel hR.ne' hRtop]

/-- An almost-sure finite good-annulus constant for one realization gives a
uniform probability bound for all whole-plane realizations. -/
theorem wholePlane_goodAnnulus_uniform_of_ae_exists
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {r c₀ : ℝ} (hr : 0 < r) (hc₀ : c₀ < 1 / 5) (z : ℂ)
    (hgood : ∀ᵐ ω ∂P, ∃ C : ℝ, IsGoodAnnulusEvent (μ ω) c₀ C r z)
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
      P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C r z} ≤ ENNReal.ofReal (1 - p) := by
  let _ : IsProbabilityMeasure P := h.isProbabilityMeasure
  let A : ℕ → Set Ω := fun n => {ω | ¬ IsGoodAnnulusEvent (μ ω) c₀ ((n : ℝ) + 1) r z}
  have hmeas (n : ℕ) : NullMeasurableSet (A n) P := by
    let T : Ω → CircleIndex → ℝ := fun ω p => hcirc ω p.1 p.2
    have hT : Measurable T := Measurable.of_eval fun p => h.measurable_circle p.1 p.2 p.1.2
    have hS := measurableSet_circleGoodAnnulusCriterion hr γ c₀ ((n : ℝ) + 1) z
    apply (hS.compl.preimage hT).nullMeasurableSet.congr
    filter_upwards [goodAnnulus_ae_iff_circleCriterion h hμ hr hc₀ ((n : ℝ) + 1) z] with ω hω
    exact propext (not_congr hω).symm
  have hanti : Antitone A := by
    intro i j hij ω hω hgood'
    exact hω (hgood'.mono_const (by exact_mod_cast Nat.add_le_add_right hij 1))
  have hzero : P (⋂ n, A n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hgood] with ω ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have hn' : IsGoodAnnulusEvent (μ ω) c₀ ((n : ℝ) + 1) r z :=
      hC.mono_const (by linarith)
    simp only [mem_iInter, A, mem_ofPred_eq, not_forall, not_not]
    exact ⟨n, hn'⟩
  have hlim := tendsto_measure_iInter_atTop (μ := P) hmeas hanti ⟨0, measure_ne_top P _⟩
  rw [hzero] at hlim
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim _ he).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  intro Ω' _ P' hC' hcirc' μ' h' hμ'
  rw [← wholePlane_goodAnnulus_law h hμ h' hμ' hr hc₀ ((n : ℝ) + 1) z]
  exact hn

/-- Finite unit-annulus logarithmic potential in one realization implies
uniform good-annulus bounds. Positivity of the denominator follows from full
support of the whole-plane LQG measure. -/
theorem wholePlane_goodAnnulus_uniform_of_ae_finite_potential
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 5)
    (hfinite : ∀ᵐ ω ∂P,
      (⨆ v ∈ annulus 0 1 (2 * 1), ∫⁻ u in annulus 0 1 (2 * 1),
        ENNReal.ofReal (Real.log (1 / ‖u - v‖) + 1) ∂(μ ω)) < ∞)
    {p : ℝ} (hp : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasure P' γ hcirc' μ' →
      P' {ω | ¬ IsGoodAnnulusEvent (μ' ω) c₀ C 1 0} ≤ ENNReal.ofReal (1 - p) := by
  apply wholePlane_goodAnnulus_uniform_of_ae_exists h hμ (by norm_num) hc₀' 0 _ hp
  filter_upwards [hfinite, wholePlane_goodAnnulus_denominator_pos_ae hγ hγ2 h hμ] with ω hL hR
  exact goodAnnulus_exists_of_finite_potential hL (hR c₀ hc₀)

end MatedCRT.Field
