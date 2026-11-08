import MatedCRT.Steps.Sec3.PointwiseSameWalkRates
import MatedCRT.Steps.Sec3.PowerTailIntegral

/-! # Almost-everywhere same-walk rates (internal successors of the pointwise statements)

Repaired quenched rates of `notes/wpn-steps2/steps2-r2.tex`, Section 3 (lines 525–532 and 749–766). The pointwise
environment quantifier `∀ ω ∈ E ε` is replaced by `∀ᵐ ω ∂S.P, ω ∈ E ε → …`; the null set may depend on `ε`. Every
other quantity is copied verbatim: the constants `C, ε₀`, the exponents `a, β, ν, κ, q, χ`, the event `E` with its
polynomial complement, the sectionwise annealed bound and the three mean regimes. The frozen declarations
`PointwiseSameWalkRatesStep` and `CorrectedHarmonicSameWalkRateStmt` are not changed; the literal pointwise
form is false (steps2-r2.tex, proposition at lines 491–512). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- Almost-everywhere successor of `PointwiseSameWalkRatesStep`. Only the environment quantifier changes: for each
small mesh, `S.P`-almost every `ω` in `E ε` satisfies the tail and mean bounds at every interior label `v`. -/
def PointwiseSameWalkRatesAeStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (E : ℝ → Set Ω) (ρ a β ν : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ᵐ ω ∂S.P, ω ∈ E ε →
        ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
          (srwLaw (S.mult ε ω) v)
            {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
              ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) ∧
          (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
            C * (H : ℝ) *
              (if (χ : ℝ) < ν then ε ^ (min a β * χ)
               else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
               else ε ^ (min a β * ν))

/-- A pointwise bound gives the almost-everywhere one: `PointwiseSameWalkRatesStep` implies its successor. -/
theorem pointwiseSameWalkRatesAe_of_pointwise {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {E : ℝ → Set Ω} {ρ a β ν : ℝ}
    (h : PointwiseSameWalkRatesStep S E ρ a β ν) : PointwiseSameWalkRatesAeStep S E ρ a β ν := by
  intro r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C, ε₀, hC, hε₀, hpt⟩ := h r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  refine ⟨C, ε₀, hC, hε₀, fun ε hε hεs => ?_⟩
  exact Eventually.of_forall fun ω hω v hv => hpt ε hε hεs ω hω v hv

open Classical in
/-- The repaired exported same-walk statement, as an internal successor of the frozen
`CorrectedHarmonicSameWalkRateStmt` (`Draft/Section3HarmonicCorrected.lean`). The quenched clause is the
almost-everywhere implication `∀ᵐ ω ∂S.P, ω ∈ E ε → …`; everything else is identical to the frozen statement:
the exponents `bAnn, ν, κ`, the measurable event `E` with its polynomial complement, the sectionwise annealed
bound, and the three mean regimes with the factor `H`. -/
def CorrectedHarmonicSameWalkRateAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ bAnn : ℝ, 0 < bAnn ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
  ∃ CE εE : ℝ, 0 ≤ CE ∧ 0 < εE ∧
    (∀ ε : ℝ, 0 < ε → ε < εE → S.P (E ε)ᶜ ≤ ENNReal.ofReal (CE * ε ^ κ)) ∧
    ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
    ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
    ∀ q : ℝ, 0 < q → q < min a bAnn * (χ : ℝ) →
    ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
            ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a bAnn - q / χ)))) ∧
        ∀ᵐ ω ∂S.P, ω ∈ E ε →
          ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
            (srwLaw (S.mult ε ω) v)
              {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
                ENNReal.ofReal (C * ε ^ (ν * (min a bAnn - q / χ))) ∧
            (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
              C * (H : ℝ) *
                (if (χ : ℝ) < ν then ε ^ (min a bAnn * χ)
                 else if (χ : ℝ) = ν then ε ^ (min a bAnn * ν) * (1 + |Real.log ε|)
                 else ε ^ (min a bAnn * ν))

/-! ## Three-regime mean under a distance tail (steps2-r2.tex lines 735-747; identical in steps2-r3.tex)

For `X ≥ 0`, `X ≤ R` a.s. and `P(X > t) ≤ K (ℓ/t)^ν` on `(ℓ, R)`, the layer-cake identity
`lintegral_rpow_eq_lintegral_tail` and direct integration give the three regimes of eq:mean-three in `ℓ`. -/


theorem lintegral_Ioc_zero_chi {χ ℓ : ℝ} (hχ : 0 < χ) (hℓ : 0 ≤ ℓ) :
    ∫⁻ t in Ioc 0 ℓ, ENNReal.ofReal (χ * t ^ (χ - 1)) = ENNReal.ofReal (ℓ ^ χ) := by
  have hχ0 : χ ≠ 0 := hχ.ne'
  have hint : IntervalIntegrable (fun t : ℝ => χ * t ^ (χ - 1)) volume 0 ℓ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < χ - 1)).const_mul χ
  have hfi : IntegrableOn (fun t : ℝ => χ * t ^ (χ - 1)) (Ioc 0 ℓ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hℓ).1 hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 ℓ)] fun t : ℝ => χ * t ^ (χ - 1) := by
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    exact mul_nonneg hχ.le (Real.rpow_nonneg ht.1.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, ← intervalIntegral.integral_of_le hℓ,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < χ - 1))]
  have h1 : χ - 1 + 1 = χ := by ring
  rw [h1, Real.zero_rpow hχ0, sub_zero]
  congr 1
  field_simp

theorem lintegral_Ioc_tail_eq {c p ℓ R : ℝ} (hc : 0 ≤ c) (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R) :
    ∫⁻ t in Ioc ℓ R, ENNReal.ofReal (c * t ^ p) = ENNReal.ofReal (c * ∫ t in ℓ..R, t ^ p) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ p) (uIcc ℓ R) := by
    rw [uIcc_of_le hℓR]
    exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hℓ ht.1))
  have hint : IntervalIntegrable (fun t : ℝ => t ^ p) volume ℓ R := hcont.intervalIntegrable
  have hfi : IntegrableOn (fun t : ℝ => c * t ^ p) (Ioc ℓ R) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hℓR).1 hint).const_mul c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc ℓ R)] fun t : ℝ => c * t ^ p := by
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    exact mul_nonneg hc (Real.rpow_nonneg (lt_trans hℓ ht.1).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, intervalIntegral.integral_of_le hℓR,
    integral_const_mul]

theorem lintegral_rpow_le_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : AEMeasurable X μ) {R ℓ K χ ν : ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXR : ∀ᵐ ω ∂μ, X ω ≤ R)
    (hχ : 0 < χ) (hK : 0 ≤ K) (hℓ : 0 < ℓ)
    (htail : ∀ t : ℝ, ℓ < t → t < R → μ {ω | t < X ω} ≤ ENNReal.ofReal (K * (ℓ / t) ^ ν)) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ χ) ∂μ ≤
      (∫⁻ t in Ioc 0 ℓ, ENNReal.ofReal (χ * t ^ (χ - 1))) +
        (∫⁻ t in Ioc ℓ R, ENNReal.ofReal (K * ℓ ^ ν * χ * t ^ (χ - 1 - ν))) := by
  have hzero : ∀ t : ℝ, R ≤ t → μ {ω | t < X ω} = 0 := by
    intro t ht
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hXR)
    exact not_le.2 (lt_of_le_of_lt ht hω)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {ω | t < X ω} * ENNReal.ofReal (χ * t ^ (χ - 1)) ≤
      (Ioc 0 ℓ).indicator (fun t => ENNReal.ofReal (χ * t ^ (χ - 1))) t +
        (Ioc ℓ R).indicator (fun t => ENNReal.ofReal (K * ℓ ^ ν * χ * t ^ (χ - 1 - ν))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h1 : t ≤ ℓ
    · rw [Set.indicator_of_mem (show t ∈ Ioc 0 ℓ from ⟨ht0, h1⟩),
        Set.indicator_of_notMem (show t ∉ Ioc ℓ R from fun h => absurd h.1 (not_lt.2 h1)), add_zero]
      exact mul_le_of_le_one_left zero_le prob_le_one
    · have h1' : ℓ < t := not_le.1 h1
      by_cases h2 : t < R
      · rw [Set.indicator_of_notMem (show t ∉ Ioc 0 ℓ from fun h => absurd h.2 (not_le.2 h1')),
          Set.indicator_of_mem (show t ∈ Ioc ℓ R from ⟨h1', h2.le⟩), zero_add]
        refine le_trans (mul_le_mul_of_nonneg_right (htail t h1' h2) zero_le) (le_of_eq ?_)
        have hK' : 0 ≤ K * (ℓ / t) ^ ν := mul_nonneg hK (Real.rpow_nonneg (div_nonneg hℓ.le ht0.le) _)
        rw [← ENNReal.ofReal_mul hK']
        congr 1
        rw [Real.div_rpow hℓ.le ht0.le, Real.rpow_sub ht0 (χ - 1) ν]
        ring
      · have h2' : R ≤ t := not_lt.1 h2
        rw [hzero t h2', zero_mul]
        exact zero_le
  have hmeas1 : Measurable (fun t : ℝ => ENNReal.ofReal (χ * t ^ (χ - 1))) :=
    ((measurable_id.pow_const _).const_mul χ).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal (X ω ^ χ) ∂μ
      = ∫⁻ t in Ioi 0, μ {ω | t < X ω} * ENNReal.ofReal (χ * t ^ (χ - 1)) :=
        lintegral_rpow_eq_lintegral_tail μ X χ hχ hX0 hXm
    _ ≤ ∫⁻ t in Ioi 0, ((Ioc 0 ℓ).indicator (fun t => ENNReal.ofReal (χ * t ^ (χ - 1))) t +
          (Ioc ℓ R).indicator (fun t => ENNReal.ofReal (K * ℓ ^ ν * χ * t ^ (χ - 1 - ν))) t) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ t in Ioc 0 ℓ, ENNReal.ofReal (χ * t ^ (χ - 1))) +
          (∫⁻ t in Ioc ℓ R, ENNReal.ofReal (K * ℓ ^ ν * χ * t ^ (χ - 1 - ν))) := by
        rw [lintegral_add_left (hmeas1.indicator measurableSet_Ioc), lintegral_indicator measurableSet_Ioc,
          lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          Measure.restrict_restrict measurableSet_Ioc]
        have e1 : Ioc (0 : ℝ) ℓ ∩ Ioi 0 = Ioc 0 ℓ := Set.inter_eq_left.2 fun x hx => hx.1
        have e2 : Ioc ℓ R ∩ Ioi (0 : ℝ) = Ioc ℓ R := Set.inter_eq_left.2 fun x hx => lt_trans hℓ hx.1
        rw [e1, e2]

theorem integral_rpow_tail_eq {χ ν ℓ R : ℝ} (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R) (hχν : χ = ν) :
    ∫ t in ℓ..R, t ^ (χ - 1 - ν) ≤ |Real.log R| + |Real.log ℓ| := by
  have e : χ - 1 - ν = -1 := by linarith
  rw [e]
  simp only [Real.rpow_neg_one]
  rw [integral_inv_of_pos hℓ (lt_of_lt_of_le hℓ hℓR),
    Real.log_div (ne_of_gt (lt_of_lt_of_le hℓ hℓR)) (ne_of_gt hℓ)]
  have h1 := le_abs_self (Real.log R)
  have h2 := neg_abs_le (Real.log ℓ)
  linarith [abs_nonneg (Real.log R)]

theorem integral_rpow_tail_le_lt {χ ν ℓ R : ℝ} (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R) (hlt : χ < ν) :
    ∫ t in ℓ..R, t ^ (χ - 1 - ν) ≤ ℓ ^ (χ - ν) / (ν - χ) := by
  have hne : χ - 1 - ν ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc ℓ R := by
    intro h
    rcases Set.mem_uIcc.1 h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_rpow (Or.inr ⟨hne, h0⟩), show χ - 1 - ν + 1 = χ - ν by ring]
  have hνχ : ν - χ ≠ 0 := by intro h; linarith
  have hs : χ - ν < 0 := by linarith
  have hR : 0 ≤ R ^ (χ - ν) := Real.rpow_nonneg (by linarith) _
  rw [div_le_iff_of_neg hs]
  have hmul : ℓ ^ (χ - ν) / (ν - χ) * (χ - ν) = -(ℓ ^ (χ - ν)) := by
    rw [div_mul_eq_mul_div, div_eq_iff hνχ]
    ring
  rw [hmul]
  linarith

theorem integral_rpow_tail_le_gt {χ ν ℓ R : ℝ} (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R) (hgt : ν < χ) :
    ∫ t in ℓ..R, t ^ (χ - 1 - ν) ≤ R ^ (χ - ν) / (χ - ν) := by
  have hne : χ - 1 - ν ≠ -1 := by intro h; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc ℓ R := by
    intro h
    rcases Set.mem_uIcc.1 h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_rpow (Or.inr ⟨hne, h0⟩), show χ - 1 - ν + 1 = χ - ν by ring]
  have hpos : 0 < χ - ν := by linarith
  have hl : 0 ≤ ℓ ^ (χ - ν) := Real.rpow_nonneg hℓ.le _
  refine div_le_div_of_nonneg_right ?_ hpos.le
  linarith

theorem lintegral_rpow_le_regime_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : AEMeasurable X μ) {R ℓ K χ ν : ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXR : ∀ᵐ ω ∂μ, X ω ≤ R)
    (hχ : 0 < χ) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R)
    (htail : ∀ t : ℝ, ℓ < t → t < R → μ {ω | t < X ω} ≤ ENNReal.ofReal (K * (ℓ / t) ^ ν))
    (hlt : χ < ν) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ χ) ∂μ ≤ ENNReal.ofReal ((1 + K * χ / (ν - χ)) * ℓ ^ χ) := by
  have hc : 0 ≤ K * ℓ ^ ν * χ := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hℓ.le _)) hχ.le
  have hI := integral_rpow_tail_le_lt (χ := χ) (ν := ν) hℓ hℓR hlt
  have hI0 : 0 ≤ ∫ t in ℓ..R, t ^ (χ - 1 - ν) :=
    intervalIntegral.integral_nonneg hℓR fun t ht => Real.rpow_nonneg (lt_of_lt_of_le hℓ ht.1).le _
  have hνχ0 : ν - χ ≠ 0 := by intro h; linarith
  have hpow : ℓ ^ ν * ℓ ^ (χ - ν) = ℓ ^ χ := by
    rw [← Real.rpow_add hℓ]; congr 1; ring
  have h1 : K * ℓ ^ ν * χ * (∫ t in ℓ..R, t ^ (χ - 1 - ν)) ≤
      K * ℓ ^ ν * χ * (ℓ ^ (χ - ν) / (ν - χ)) := mul_le_mul_of_nonneg_left hI hc
  have h2 : K * ℓ ^ ν * χ * (ℓ ^ (χ - ν) / (ν - χ)) = K * χ / (ν - χ) * ℓ ^ χ := by
    rw [← hpow]; field_simp
  have h3 : (1 + K * χ / (ν - χ)) * ℓ ^ χ = ℓ ^ χ + K * χ / (ν - χ) * ℓ ^ χ := by ring
  refine (lintegral_rpow_le_split μ X hXm hX0 hXR hχ hK hℓ htail).trans ?_
  rw [lintegral_Ioc_zero_chi hχ hℓ.le, lintegral_Ioc_tail_eq hc hℓ hℓR,
    ← ENNReal.ofReal_add (Real.rpow_nonneg hℓ.le _) (mul_nonneg hc hI0)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [h1, h2, h3]

theorem lintegral_rpow_le_regime_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : AEMeasurable X μ) {R ℓ K χ ν : ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXR : ∀ᵐ ω ∂μ, X ω ≤ R)
    (hχ : 0 < χ) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R)
    (htail : ∀ t : ℝ, ℓ < t → t < R → μ {ω | t < X ω} ≤ ENNReal.ofReal (K * (ℓ / t) ^ ν))
    (hχν : χ = ν) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ χ) ∂μ ≤
      ENNReal.ofReal ((1 + K * ν * (1 + |Real.log R|)) * ℓ ^ ν * (1 + |Real.log ℓ|)) := by
  have hc : 0 ≤ K * ℓ ^ ν * χ := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hℓ.le _)) hχ.le
  have hI := integral_rpow_tail_eq (χ := χ) (ν := ν) hℓ hℓR hχν
  have hI0 : 0 ≤ ∫ t in ℓ..R, t ^ (χ - 1 - ν) :=
    intervalIntegral.integral_nonneg hℓR fun t ht => Real.rpow_nonneg (lt_of_lt_of_le hℓ ht.1).le _
  refine (lintegral_rpow_le_split μ X hXm hX0 hXR hχ hK hℓ htail).trans ?_
  rw [lintegral_Ioc_zero_chi hχ hℓ.le, lintegral_Ioc_tail_eq hc hℓ hℓR,
    ← ENNReal.ofReal_add (Real.rpow_nonneg hℓ.le _) (mul_nonneg hc hI0)]
  refine ENNReal.ofReal_le_ofReal ?_
  subst hχν
  have ha : 0 ≤ |Real.log R| := abs_nonneg _
  have hb : 0 ≤ |Real.log ℓ| := abs_nonneg _
  have hp : 0 ≤ ℓ ^ χ := Real.rpow_nonneg hℓ.le _
  have hq : 0 ≤ K * χ := mul_nonneg hK hχ.le
  have hab : |Real.log R| + |Real.log ℓ| ≤ (1 + |Real.log R|) * (1 + |Real.log ℓ|) := by
    nlinarith [mul_nonneg ha hb]
  have hstep : K * ℓ ^ χ * χ * (∫ t in ℓ..R, t ^ (χ - 1 - χ)) ≤
      K * ℓ ^ χ * χ * (|Real.log R| + |Real.log ℓ|) :=
    mul_le_mul_of_nonneg_left hI (mul_nonneg (mul_nonneg hK hp) hχ.le)
  have hmain : ℓ ^ χ + K * ℓ ^ χ * χ * (|Real.log R| + |Real.log ℓ|) ≤
      (1 + K * χ * (1 + |Real.log R|)) * ℓ ^ χ * (1 + |Real.log ℓ|) := by
    nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg hq hp), mul_nonneg hp hb, mul_nonneg hp hq]
  linarith [hstep, hmain]

theorem lintegral_rpow_le_regime_gt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXm : AEMeasurable X μ) {R ℓ K χ ν : ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXR : ∀ᵐ ω ∂μ, X ω ≤ R)
    (hχ : 0 < χ) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hℓR : ℓ ≤ R)
    (htail : ∀ t : ℝ, ℓ < t → t < R → μ {ω | t < X ω} ≤ ENNReal.ofReal (K * (ℓ / t) ^ ν))
    (hgt : ν < χ) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ χ) ∂μ ≤
      ENNReal.ofReal ((1 + K * χ / (χ - ν)) * R ^ (χ - ν) * ℓ ^ ν) := by
  have hc : 0 ≤ K * ℓ ^ ν * χ := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hℓ.le _)) hχ.le
  have hI := integral_rpow_tail_le_gt (χ := χ) (ν := ν) hℓ hℓR hgt
  have hI0 : 0 ≤ ∫ t in ℓ..R, t ^ (χ - 1 - ν) :=
    intervalIntegral.integral_nonneg hℓR fun t ht => Real.rpow_nonneg (lt_of_lt_of_le hℓ ht.1).le _
  have hs : 0 < χ - ν := by linarith
  have hsne : χ - ν ≠ 0 := hs.ne'
  have hpow : ℓ ^ ν * ℓ ^ (χ - ν) = ℓ ^ χ := by
    rw [← Real.rpow_add hℓ]; congr 1; ring
  have hle : ℓ ^ (χ - ν) ≤ R ^ (χ - ν) := Real.rpow_le_rpow hℓ.le hℓR hs.le
  have hle2 : ℓ ^ χ ≤ R ^ (χ - ν) * ℓ ^ ν := by
    rw [← hpow, mul_comm (R ^ (χ - ν))]
    exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hℓ.le _)
  have hsub : K * ℓ ^ ν * χ * (∫ t in ℓ..R, t ^ (χ - 1 - ν)) ≤
      K * ℓ ^ ν * χ * (R ^ (χ - ν) / (χ - ν)) := mul_le_mul_of_nonneg_left hI hc
  have h2 : K * ℓ ^ ν * χ * (R ^ (χ - ν) / (χ - ν)) = K * χ / (χ - ν) * R ^ (χ - ν) * ℓ ^ ν := by
    field_simp
  have h3 : (1 + K * χ / (χ - ν)) * R ^ (χ - ν) * ℓ ^ ν =
      R ^ (χ - ν) * ℓ ^ ν + K * χ / (χ - ν) * R ^ (χ - ν) * ℓ ^ ν := by ring
  refine (lintegral_rpow_le_split μ X hXm hX0 hXR hχ hK hℓ htail).trans ?_
  rw [lintegral_Ioc_zero_chi hχ hℓ.le, lintegral_Ioc_tail_eq hc hℓ hℓR,
    ← ENNReal.ofReal_add (Real.rpow_nonneg hℓ.le _) (mul_nonneg hc hI0)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [hsub, h2, h3, hle2]

end MatedCRT

#print axioms MatedCRT.pointwiseSameWalkRatesAe_of_pointwise
#print axioms MatedCRT.lintegral_rpow_le_regime_lt
#print axioms MatedCRT.lintegral_rpow_le_regime_eq
#print axioms MatedCRT.lintegral_rpow_le_regime_gt
