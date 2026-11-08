import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Measurability.FieldCircle

/-! # The cone scale radius is determined by the field

The last level time is recovered from countably many circle averages. Their
field-measurable versions come from the pairing-to-circle approximation. -/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.Sec1

/-- The cone scale radius has a version measurable with respect to the field
sigma-algebra. -/
theorem exists_fieldMeasurable_coneScaleRadius
    (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {b : ℝ} (hb : 0 < b) :
    ∃ R : Ω → ℝ, Measurable[S.fieldSigma] R ∧
      R =ᵐ[S.P] fun ω => coneScaleRadius γ (S.hcirc ω) b := by
  classical
  let X : Ω → ℝ → ℝ := fun ω r => S.hcirc ω r 0 + lqgQ γ * Real.log r
  let Y : Ω → ℝ → ℝ := fun ω r => FieldCircle.circleField S r 0 ω + lqgQ γ * Real.log r
  let c : ℝ := γ⁻¹ * Real.log b
  let Φ : ℚ → Ω → Prop := fun q ω =>
    ∀ M : ℕ, ∃ k : ℕ, ∀ x : {x : ℚ // (q : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ M},
      1 / ((k : ℝ) + 1) ≤ |Y ω x - c|
  have hΦ : ∀ q : ℚ, MeasurableSet[S.fieldSigma] {ω | Φ q ω} := by
    intro q
    simp only [Φ, Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun k => MeasurableSet.iInter fun x => ?_
    exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp (((FieldCircle.measurable_circleField S _ _).add_const _).sub_const _))
  let F : ℚ → Ω → ℝ≥0∞ := fun q ω =>
    if 0 < (q : ℝ) ∧ Φ q ω then ENNReal.ofReal q else ⊤
  have hF : ∀ q, Measurable[S.fieldSigma] (F q) := by
    intro q
    exact Measurable.ite ((MeasurableSet.const _).inter (hΦ q)) measurable_const measurable_const
  let R : Ω → ℝ := fun ω => (⨅ q : ℚ, F q ω).toReal
  refine ⟨R, (Measurable.iInf hF).ennreal_toReal, ?_⟩
  have hY : ∀ᵐ ω ∂S.P, ∀ q : ℚ, 0 < (q : ℝ) → Y ω q = X ω q := by
    simp only [ae_all_iff]
    intro q hq
    filter_upwards [FieldCircle.ae_circleField_eq hS hq (show ‖(0 : ℂ)‖ ≠ (q : ℝ) by simpa using hq.ne)] with ω hω
    simp only [Y, X, hω]
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hpos := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  filter_upwards [hY, hpos, hS.isQuantumCone.ae_continuousOn_circle] with ω hYω hR hcont
  have hX : ContinuousOn (X ω) (Ioi 0) := by
    have h1 : ContinuousOn (fun r : ℝ => S.hcirc ω r 0) (Ioi 0) :=
      hcont.comp (continuous_id.prodMk continuous_const).continuousOn fun r hr => ⟨hr, mem_univ _⟩
    exact h1.add (continuousOn_const.mul (Real.continuousOn_log.mono fun r hr => (mem_Ioi.1 hr).ne'))
  have hΦiff : ∀ q : ℚ, 0 < (q : ℝ) →
      (Φ q ω ↔ coneScaleRadius γ (S.hcirc ω) b < q) := by
    intro q hq
    have heq : Φ q ω ↔ ∀ M : ℕ, ∃ k : ℕ,
        ∀ x : {x : ℚ // (q : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ M},
          1 / ((k : ℝ) + 1) ≤ |X ω x - c| := by
      simp only [Φ]
      apply forall_congr' fun M => exists_congr fun k => forall_congr' fun x => ?_
      rw [hYω x (lt_of_lt_of_le hq x.2.1)]
    rw [heq]
    exact (sSup_levelSet_lt_iff hX hR hq).symm
  obtain ⟨q₀, hq₀, _⟩ := exists_rat_btwn (show coneScaleRadius γ (S.hcirc ω) b <
    coneScaleRadius γ (S.hcirc ω) b + 1 by linarith)
  have hq₀pos : 0 < (q₀ : ℝ) := hR.trans hq₀
  have hF₀ : F q₀ ω = ENNReal.ofReal q₀ := by
    dsimp only [F]
    rw [ite_eq_left ⟨hq₀pos, (hΦiff q₀ hq₀pos).2 hq₀⟩]
  have hfinite : (⨅ q : ℚ, F q ω) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) (by
    calc (⨅ q : ℚ, F q ω) ≤ F q₀ ω := iInf_le _ q₀
      _ = ENNReal.ofReal q₀ := hF₀)
  have hlower : ENNReal.ofReal (coneScaleRadius γ (S.hcirc ω) b) ≤ ⨅ q : ℚ, F q ω := by
    refine le_iInf fun q => ?_
    by_cases hq : 0 < (q : ℝ) ∧ Φ q ω
    · dsimp only [F]
      rw [ite_eq_left hq]
      exact ENNReal.ofReal_le_ofReal ((hΦiff q hq.1).1 hq.2).le
    · dsimp only [F]
      rw [ite_eq_right hq]
      exact le_top
  have hlower' : coneScaleRadius γ (S.hcirc ω) b ≤ R ω := by
    have := ENNReal.toReal_mono hfinite hlower
    simpa [R, ENNReal.toReal_ofReal hR.le] using this
  have hupper : R ω ≤ coneScaleRadius γ (S.hcirc ω) b := by
    apply le_of_forall_gt
    intro a ha
    obtain ⟨q, hq, hqa⟩ := exists_rat_btwn ha
    have hqpos : 0 < (q : ℝ) := hR.trans hq
    have heq : F q ω = ENNReal.ofReal q := by
      dsimp only [F]
      rw [ite_eq_left ⟨hqpos, (hΦiff q hqpos).2 hq⟩]
    have hle : (⨅ q : ℚ, F q ω) ≤ ENNReal.ofReal q := by
      calc (⨅ q : ℚ, F q ω) ≤ F q ω := iInf_le _ q
        _ = ENNReal.ofReal q := heq
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    have : R ω ≤ (q : ℝ) := by simpa [R, ENNReal.toReal_ofReal hqpos.le] using this
    exact this.trans_lt hqa
  exact le_antisymm hupper hlower'

end MatedCRT.Sec1
