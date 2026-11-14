import MatedCRT.FirstPass.Derived.HarnackPairFromCoupling

/-!
# The pair events of the Harnack inequality with the mating-rigid set chosen for each `γ`

Berestycki–Gwynne (2020), Lemmas 3.9–3.11. The conclusion of `hPair_of_reference` (the per-circle failure bounds
`hPair` of `greenKernelUpperBoundStmt_of_pair_single_cellSize`) when, for every `γ ∈ (0, 2)`, there is a one-sided
mating-rigid set `G_γ` that is full for every `γ`-correlated two-sided Brownian law; the set may depend on `γ`. The
proof at a fixed `γ` uses the full-measure property of the mating-rigid set only at that `γ`: the reference
environment `S'` of `γ` gives the exponents and constants through `pairEventsReal_of_coupling`, and the transfer
`pairItin_failure_le_of_valid` / `pairL311_failure_le_of_valid` carries the failure bounds to every valid
environment `S` of `γ`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric LatticeProb.LQG.ExplicitScale

namespace MatedCRT.FirstPass.Derived

/-- **The failure bounds of the itinerary events (3.21) and of the disconnection event (3.35) of Lemma 3.11 in every
valid environment, with the mating-rigid set chosen for each `γ`** (Berestycki–Gwynne (2020), Lemmas 3.9–3.11). The
conclusion of `hPair_of_reference`, when for every `γ ∈ (0, 2)` there is a one-sided mating-rigid set `G_γ` that is
full for every `γ`-correlated two-sided Brownian law. -/
theorem hPair_of_reference_of_forall_gamma {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀) := by
  intro γ hγ0 hγ2
  obtain ⟨G, hGnull, hG⟩ := hU γ hγ0 hγ2
  obtain ⟨S', hS'⟩ := href γ hγ0 hγ2
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η'', η₀, D, hae⟩ := hS'.matingOfTrees
  obtain ⟨α, hα, β, hβ, hpair⟩ := pairEventsReal_of_coupling D inferInstance ⟨hγ0, hγ2⟩
  refine ⟨β, α, hβ, hα, fun ρ' hρ0 hρ1 => ?_⟩
  obtain ⟨p₀, hp₀, p₁, hp₁, C, hC⟩ := hpair ρ' hρ0 hρ1
  refine ⟨p₀, p₁, hp₀, hp₁, fun Ω _ S hS => ⟨C, fun ε hε0 hε1 => ?_⟩⟩
  obtain ⟨hA, hL⟩ := hC ε hε0 hε1
  refine ⟨fun z r hr hball => ?_, ?_⟩
  · refine (pairItin_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' hGnull hG hε0.le p₀ z r).trans ?_
    refine (measure_mono_ae ?_).trans (hA z r hr hball)
    filter_upwards [hae] with w hw hnot hmem
    obtain ⟨h, H, hcell, hgood⟩ := hmem
    refine hnot ⟨h, H, ?_, hgood⟩
    funext x
    rw [hcell x, hw.1]
    rfl
  · refine (pairL311_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' hGnull hG hε0.le ρ' (ε ^ β) p₁).trans ?_
    refine (measure_mono_ae ?_).trans hL
    filter_upwards [hae] with w hw hnot hmem
    obtain ⟨h, H, hcell, h311⟩ := hmem
    refine hnot (pairL311Good_of_lemma311Holds h H ?_ h311)
    funext x
    rw [hcell x, hw.1]
    rfl

end MatedCRT.FirstPass.Derived
