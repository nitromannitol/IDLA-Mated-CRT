import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialBound
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Draft.Section2

/-! Polynomial smallness of buffered Green potentials from Lemma 2.17. -/

open Set Metric MeasureTheory HarmonicBalls

namespace MatedCRT

/-- Lemma 2.17 controls uniformly the Green potential of every nonnegative
source bounded by one and supported in a small ball around its pole. -/
theorem bumpPotential_polyHighProb (h217 : BoundedExitTimeRVStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ →
      PolyHighProb P fun δ => {ω | ∀ x ∈ ball (0 : ℂ) ρ, ∀ O : Set ℂ,
        O ⊆ closedBall x 2 → x ∈ O → ∀ φ : ℂ → ℝ,
        (∀ w, 0 ≤ φ w) → (∀ w, φ w ≤ 1) → (∀ w ∉ ball x δ, φ w = 0) →
        ENNReal.ofReal (∫ w, greenFunction O x w * φ w ∂μ ω) ≤ ENNReal.ofReal (δ ^ q)} := by
  obtain ⟨q, hq, h217q⟩ := h217 γ hγ hγ2
  refine ⟨q, hq, ?_⟩
  intro ρ hρ hρ1 Ω _ P hC hcirc μ hcone
  have hprob := (h217q ρ hρ hρ1 Ω P hC hcirc μ hcone).2
  apply polyHighProb_of_inter_subset hprob (G := Set.univ) (by simp) (show (0 : ℝ) < 1 by norm_num)
  intro δ hδ hδ1 ω hω x hx O hO hxO φ hφ0 hφ1 hsupp
  exact (ofReal_integral_green_mul_bump_le_largestExitTimeRV (μ ω) φ hδ hδ1.le hO hxO
    hφ0 hφ1 hsupp).trans (hω.1 x hx)

end MatedCRT
