import MatedCRT.Steps.Sec3.PointwiseSameWalkRates

/-! # Assembly of annealed and pointwise same-walk rates -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The annealed tail component, at fixed model parameters and exponents. -/
def AnnealedSameWalkRateStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ a β ν κ : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        {p | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2} ≤
          ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * (min a β - q / χ))))

/-- Assembly input with exactly the frozen uniform exponent quantifiers.
The event and the two rate components are kept explicit proof steps. -/
def UniformSameWalkAssemblyStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
    AnnealedSameWalkRateStep S ρ a β ν κ ∧ PointwiseSameWalkRatesStep S E ρ a β ν

/-- Combining the two estimates preserves the frozen same-walk statement. -/
theorem correctedHarmonicSameWalkRate_of_assembly (𝒮 : SpaceFillingSLEModel)
    (h : UniformSameWalkAssemblyStep 𝒮) : CorrectedHarmonicSameWalkRateStmt 𝒮 := by
  intro γ hγ hγ2
  obtain ⟨β, hβ, h⟩ := h γ hγ hγ2
  refine ⟨β, hβ, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨ν, hν, h⟩ := h ρ hρ hρ1
  refine ⟨ν, hν, ?_⟩
  intro a ha ha'
  obtain ⟨κ, hκ, h⟩ := h a ha ha'
  refine ⟨κ, hκ, ?_⟩
  intro Ω _ S hS
  obtain ⟨E, hEm, ⟨D, δ, hD, hδ, hbad⟩, hann, hpoint⟩ := h Ω S hS
  refine ⟨E, hEm, D, δ, hD, hδ, hbad, ?_⟩
  intro r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := hann r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  obtain ⟨C₂, δ₂, hC₂, hδ₂, h₂⟩ := hpoint r z hr hball ψ H χ hχ hχ1 hψ q hq hq' y hy
  refine ⟨max C₁ C₂, min δ₁ δ₂, le_trans hC₁ (le_max_left _ _), lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε hsmall
  have he₁ : ε < δ₁ := hsmall.trans_le (min_le_left _ _)
  have he₂ : ε < δ₂ := hsmall.trans_le (min_le_right _ _)
  constructor
  · apply (h₁ ε hε he₁).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    positivity
  · intro ω hω v hv
    obtain ⟨htail, hmean⟩ := h₂ ε hε he₂ ω hω v hv
    constructor
    · apply htail.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hε.le _)
    · apply hmean.trans
      have hscale : 0 ≤ (H : ℝ) *
          (if (χ : ℝ) < ν then ε ^ (min a β * χ)
           else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
           else ε ^ (min a β * ν)) := by
        split_ifs <;> positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hscale]

end MatedCRT

#print axioms MatedCRT.correctedHarmonicSameWalkRate_of_assembly
