import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaDeviation
import MatedCRT.Proofs.Infra.LocallyFinite

/-! # Measurable proxies for the selection in `OdometerMeasurableSelectionStep`

For a compact `K`, a family `cen p i` of functions continuous on `K` and rational thresholds `(1/2)^q`,
the events `{ω | ∀ x ∈ K, |w̄^{ε_n}_t(x; ω) - cen p i x| ≤ (1/2)^q}` have `σ(h, η)`-measurable versions,
equal almost surely. The complements of the envSigma deviation events of `EnvSigmaDeviation` give them. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Measurable versions, indexed by `(p, i, n, q)`, of the events that the rescaled least supersolution
at mesh `εs n` lies within `(1/2)^q` on `K` of the continuous function `cen p i`. -/
theorem exists_selection_proxies {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ' : γ < 2)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (ρ t : ℝ) (ht : 0 < t) (εs : ℕ → ℝ) (hεpos : ∀ n, 0 < εs n)
    (K : Set ℂ) (hK : IsCompact K) (cen : ℕ → ℕ → ℂ → ℝ) (hcen : ∀ p i, ContinuousOn (cen p i) K) :
    ∃ G : ℕ → ℕ → ℕ → ℕ → Set Ω, (∀ p i n q, MeasurableSet[S.envSigma] (G p i n q)) ∧
      ∀ᵐ ω ∂S.P, ∀ p i n q, (ω ∈ G p i n q ↔
        ∀ x ∈ K, |rescaledMatedLeastSupersolution S ρ t (εs n) ω x - cen p i x| ≤ (1 / 2 : ℝ) ^ q) := by
  classical
  have hloc := MatedCRTEnv.IsValid.ae_isLocallyFiniteMult hγ hγ' hS hcell
  have hdev : ∀ p i n q : ℕ, ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K,
        (1 / 2 : ℝ) ^ q < |rescaledMatedLeastSupersolution S ρ t (εs n) ω x - cen p i x|) := by
    intro p i n q
    exact MatedCRTEnv.IsValid.exists_envSigma_measurable_rescaledLeastSupersolution_deviation hS hγ hγ'
      (hεpos n) ρ t ht (hloc.mono fun ω hω b => hω (εs n) (hεpos n) b) K hK (cen p i) (hcen p i)
      ((1 / 2 : ℝ) ^ q)
  choose A hAm hAae using hdev
  have hall : ∀ᵐ ω ∂S.P, ∀ p i n q : ℕ, (ω ∈ A p i n q ↔
      ∃ x ∈ K, (1 / 2 : ℝ) ^ q < |rescaledMatedLeastSupersolution S ρ t (εs n) ω x - cen p i x|) :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun i => ae_all_iff.2 fun n => ae_all_iff.2 fun q => hAae p i n q
  refine ⟨fun p i n q => (A p i n q)ᶜ, fun p i n q => (hAm p i n q).compl, ?_⟩
  filter_upwards [hall] with ω hω
  intro p i n q
  show ω ∈ (A p i n q)ᶜ ↔ _
  rw [Set.mem_compl_iff, hω p i n q]
  simp only [not_exists, not_and, not_lt]

end MatedCRT
