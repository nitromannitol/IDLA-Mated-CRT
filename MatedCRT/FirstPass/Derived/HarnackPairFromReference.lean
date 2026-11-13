import MatedCRT.FirstPass.Derived.HarnackPairTransfer

/-!
# The pair events of the Harnack inequality for every valid environment, from the events of one reference environment

Berestycki–Gwynne (2020), Lemmas 3.9–3.11.  Let `ν` be a normalized space-filling SLE law, `𝒮` and `𝒮ref` two
models with law `ν`, and `G` a one-sided mating-rigid set that is full for every correlated Brownian law. Suppose
that for every `γ ∈ (0, 2)` some valid environment `S'` of `𝒮ref` on the standard Borel space `ℝ` satisfies the
failure bounds `C ε^α₀` for the itinerary events (3.21) at the circles `∂B_r(z)`, `ε^β₀ ≤ r`,
`B_{2r}(z) ⊆ B_{ρ'}(0)`, and for the disconnection event (3.35) of Lemma 3.11 with floor `ε^β₀`, with exponents
`β₀, α₀` before `ρ'` and constants `p₀, p₁, C` depending on `ρ'` only. Then every valid environment `S` of `𝒮`
satisfies the same bounds with the same constants (`hPair_of_reference_events`): the events depend on the Brownian
pair only through the edge multiplicities (`pairItin_failure_le_of_valid`, `pairL311_failure_le_of_valid`).
The conclusion is the hypothesis `hPair` of `greenKernelUpperBoundStmt_of_pair_single_cellSize`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace MatedCRT.FirstPass.Derived

/-- **The failure bounds of the itinerary events (3.21) and of the disconnection event (3.35) of Lemma 3.11 in every
valid environment** (Berestycki–Gwynne (2020), Lemmas 3.9–3.11) from the same bounds in one valid environment on
`ℝ` of a model with the same normalized space-filling SLE law, on a one-sided mating-rigid set `G`. -/
theorem hPair_of_reference_events {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G)
    (hrefE : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ S' : MatedCRTEnv ℝ, S'.IsValid 𝒮ref γ ∧
      ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
        ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
            S'.P {ω | ¬ PairItinGood ε (S'.bm ω) (S'.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
          S'.P {ω | ¬ PairL311Good ε (S'.bm ω) (S'.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀) := by
  intro γ hγ0 hγ2
  obtain ⟨S', hS', β₀, α₀, hβ₀, hα₀, hpair⟩ := hrefE γ hγ0 hγ2
  refine ⟨β₀, α₀, hβ₀, hα₀, fun ρ' hρ0 hρ1 => ?_⟩
  obtain ⟨p₀, p₁, hp₀, hp₁, C, hC⟩ := hpair ρ' hρ0 hρ1
  refine ⟨p₀, p₁, hp₀, hp₁, fun Ω _ S hS => ⟨C, fun ε hε0 hε1 => ?_⟩⟩
  obtain ⟨hA, hL⟩ := hC ε hε0 hε1
  exact ⟨fun z r hr hball =>
    (pairItin_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' (hGnull γ hγ0 hγ2) hG hε0.le p₀ z r).trans
      (hA z r hr hball),
    (pairL311_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' (hGnull γ hγ0 hγ2) hG hε0.le ρ' (ε ^ β₀) p₁).trans hL⟩

end MatedCRT.FirstPass.Derived

/-! ## Audit -/
#print axioms MatedCRT.FirstPass.Derived.hPair_of_reference_events
