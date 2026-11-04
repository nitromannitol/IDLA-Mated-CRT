import MatedCRT.Draft.Section7
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-! Comparison of the walk events in the shell contraction argument. -/

namespace MatedCRT.Sec7

open MeasureTheory Set

/-- A path which exits `B` before hitting `B \ Λ` remains in `A` up to its
exit, provided `A` contains the occupied part of `B`. -/
theorem exit_before_hit_subset_survival (B Λ A : Set ℤ) (hA : B ∩ Λ ⊆ A) :
    {x : ℕ → ℤ | vExitTime B x < vHitTime (B \ Λ) x} ⊆
      {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} := by
  intro x hx n hn
  have hnB : x n ∈ B := (ConstantOrderDiv.lt_vExitTime_iff'.1 hn) n le_rfl
  have hnHit : (n : ℕ∞) < vHitTime (B \ Λ) x := lt_trans hn hx
  have hncompl : x n ∉ B \ Λ := by
    have := (ConstantOrderDiv.lt_vExitTime_iff'.1 hnHit) n le_rfl
    exact this
  have hnΛ : x n ∈ Λ := by
    by_contra hnΛ
    exact hncompl ⟨hnB, hnΛ⟩
  exact hA ⟨hnB, hnΛ⟩

/-- The survival-probability bound of Lemma 6.8 also bounds the strict
exit-before-hit probability appearing in Lemma 7.3. -/
theorem exit_before_hit_probability_le (m : ℤ → ℤ → ℕ) (b : ℤ)
    (B Λ A : Set ℤ) (q : ℝ) (hq : 0 ≤ q) (hA : B ∩ Λ ⊆ A)
    (hprob : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
      ENNReal.ofReal q) :
    (srwLaw m b {x | vExitTime B x < vHitTime (B \ Λ) x}).toReal ≤ q := by
  have hle := (measure_mono (exit_before_hit_subset_survival B Λ A hA)).trans hprob
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal q ≠ ⊤) hle
  simpa [ENNReal.toReal_ofReal hq] using hreal

/-- Pointwise contraction of the stopped odometer from the walk estimate and
the odometer bound on an annulus. -/
theorem stopped_odometer_le_of_survival_bound
    (m : ℤ → ℤ → ℕ) (ε ρ t : ℝ) (η : ℝ → ℂ)
    (B A : Set ℤ) (b : ℤ) (M q : ℝ) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hA : B ∩ matedDiscreteCluster m ε η ρ t ⊆ A)
    (hodo : stoppedOdometer m ε η ρ t b ≤ M *
      (srwLaw m b {x | vExitTime B x <
        vHitTime (B \ matedDiscreteCluster m ε η ρ t) x}).toReal)
    (hprob : srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
      ENNReal.ofReal q) :
    stoppedOdometer m ε η ρ t b ≤ M * q := by
  exact hodo.trans (mul_le_mul_of_nonneg_left
    (exit_before_hit_probability_le m b B (matedDiscreteCluster m ε η ρ t) A q hq hA hprob) hM)

/-- Lemma 7.3 and a survival bound imply pointwise odometer contraction on the
annulus, simultaneously for all admissible scales and annuli. -/
theorem stopped_odometer_le_of_survival_bound_ae
    (𝒮 : SpaceFillingSLEModel) (hodo : OdometerBoundMassStmt 𝒮)
    (γ ρ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε t : ℝ, 0 < ε → 0 < t → ∀ (B A : Set ℤ) (b : ℤ) (q : ℝ),
      B ⊆ cellVertices ε (S.η ω) (Metric.ball 0 ρ) \ {0} → b ∈ B → 0 ≤ q →
      0 ≤ (⨆ c : vBoundary (S.mult ε ω) B,
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) →
      B ∩ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆ A →
      srwLaw (S.mult ε ω) b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime B x → x n ∈ A} ≤
        ENNReal.ofReal q →
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤
        (⨆ c : vBoundary (S.mult ε ω) B,
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c) * q := by
  filter_upwards [hodo γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hω
  intro ε t hε ht B A b q hB hb hq hM hA hprob
  exact stopped_odometer_le_of_survival_bound (S.mult ε ω) ε ρ t (S.η ω) B A b _ q
    hM hq hA (hω ε t hε ht B hB b hb) hprob

end MatedCRT.Sec7
