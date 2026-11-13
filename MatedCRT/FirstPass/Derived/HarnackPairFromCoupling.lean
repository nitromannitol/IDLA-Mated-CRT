import MatedCRT.FirstPass.Derived.HarnackPairTransfer
import MatedCRT.FirstPass.SLERef.Reference
import LatticeProb.LQG.ItineraryRealMesh

/-!
# The pair events of the Harnack inequality for every valid environment, from a reference environment

Berestycki–Gwynne (2020), Lemmas 3.9–3.11.  Let `ν` be a normalized space-filling SLE law, `𝒮ref` a model with law
`ν` that has valid environments on the standard Borel space `ℝ` for every `γ ∈ (0, 2)`
(`HasReferenceEnvironments`), and `G` a one-sided mating-rigid set that is full for every correlated Brownian law.
For a reference environment `S'` of `γ`, the library theorem `pairEventsReal_of_coupling` gives the exponents
`α, β > 0` and, for every `ρ`, the constants `p₀, p₁, C` for the itinerary event at every circle `∂B_r(z)` with
`ε^β ≤ r`, `B_{2r}(z) ⊆ B_ρ(0)`, and for the disconnection event of Lemma 3.11 with floor `ε^β`, of the embedded
mated-CRT map of the mating-of-trees coupling of `S'`. These events depend on the Brownian pair only through the
edge multiplicities, so the transfer `pairItin_failure_le_of_valid` / `pairL311_failure_le_of_valid` bounds the
failure probabilities in every valid environment `S` of every model `𝒮` with law `ν` by the same `C ε^α`.
The result is `hPair_of_reference`: the per-circle failure bounds `hPair` of
`greenKernelUpperBoundStmt_of_pair_single_cellSize`, for every `γ ∈ (0, 2)`, with exponents `β₀, α₀` before `ρ'`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric LatticeProb.LQG.ExplicitScale

namespace MatedCRT.FirstPass.Derived

/-- **The failure bounds of the itinerary events (3.21) and of the disconnection event (3.35) of Lemma 3.11 in every
valid environment** (Berestycki–Gwynne (2020), Lemmas 3.9–3.11), from the reference environments of a model with the
same normalized space-filling SLE law and a one-sided mating-rigid set `G` (full for every `γ`-correlated Brownian
law). The conclusion is the hypothesis `hPair` of `greenKernelUpperBoundStmt_of_pair_single_cellSize`. -/
theorem hPair_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀) := by
  intro γ hγ0 hγ2
  obtain ⟨S', hS'⟩ := href γ hγ0 hγ2
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η'', η₀, D, hae⟩ := hS'.matingOfTrees
  obtain ⟨α, hα, β, hβ, hpair⟩ := pairEventsReal_of_coupling D inferInstance ⟨hγ0, hγ2⟩
  refine ⟨β, α, hβ, hα, fun ρ' hρ0 hρ1 => ?_⟩
  obtain ⟨p₀, hp₀, p₁, hp₁, C, hC⟩ := hpair ρ' hρ0 hρ1
  refine ⟨p₀, p₁, hp₀, hp₁, fun Ω _ S hS => ⟨C, fun ε hε0 hε1 => ?_⟩⟩
  obtain ⟨hA, hL⟩ := hC ε hε0 hε1
  refine ⟨fun z r hr hball => ?_, ?_⟩
  · refine (pairItin_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' (hGnull γ hγ0 hγ2) hG hε0.le p₀ z r).trans ?_
    refine (measure_mono_ae ?_).trans (hA z r hr hball)
    filter_upwards [hae] with w hw hnot hmem
    obtain ⟨h, H, hcell, hgood⟩ := hmem
    refine hnot ⟨h, H, ?_, hgood⟩
    funext x
    rw [hcell x, hw.1]
    rfl
  · refine (pairL311_failure_le_of_valid hν hνref hγ0 hγ2 hS hS' (hGnull γ hγ0 hγ2) hG hε0.le ρ' (ε ^ β) p₁).trans ?_
    refine (measure_mono_ae ?_).trans hL
    filter_upwards [hae] with w hw hnot hmem
    obtain ⟨h, H, hcell, h311⟩ := hmem
    refine hnot (pairL311Good_of_lemma311Holds h H ?_ h311)
    funext x
    rw [hcell x, hw.1]
    rfl

end MatedCRT.FirstPass.Derived
