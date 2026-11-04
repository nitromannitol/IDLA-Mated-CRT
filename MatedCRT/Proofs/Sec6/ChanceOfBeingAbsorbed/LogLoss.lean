import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.LogLoss
import MatedCRT.Steps.Sec6.IterativeBound

/-!
# Lemma 6.9, route (b) of E-A10 (lemma:chance-of-being-absorbed, line 2626)

The proof of Lemma 6.9 (lines 2637-2666) applies Lemma 6.7 at one radius `r` and then the Chernoff-type iteration
(`AbsorptionChernoffStep`, proved as `Absorption.absorptionChernoffStep`), which holds for every absorption
probability `s₂ ∈ (0, 1)`. With Lemma 6.7 in its route (b) form (absorption probability `s₂ / (1 + |log r|)²`), it
gives the rates `s₃ = s₄ = (s₂ / 4) / (1 + |log r|)²`, i.e. `ChanceOfBeingAbsorbedLogLossStmt` (the form of Lemma 6.9
used by Lemma 6.10, with `s₃` chosen after `s₀`, ESCALATION E-c5-1).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Lemma 6.9, route (b), from Lemma 6.7, route (b)**, and the Chernoff-type iteration, with `s₃ = s₄ = s₂/4`,
`s₅ = s₁`, and the same `ω₀` and `𝛅` as in Lemma 6.7. -/
theorem chanceOfBeingAbsorbedLogLoss_of_steps (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundLogStmt 𝒮)
    (hC : AbsorptionChernoffStep) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβ
  obtain ⟨ω₀, hω₀, h⟩ := h67 γ hγ hγ2 ρ hρ hρ1 βm hβ
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h'⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₂ / 4, s₂ / 4, s₁, by positivity, by positivity, by linarith, hs₁, hs₁1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hP⟩ := h' Ω S hS
  refine ⟨dd, hdd, hddpos, hP.mono' fun ε ω hω => ?_⟩
  intro r hr1 hr2 Θ hΘ1 hΘ2 k a hk ha
  have hL : 1 ≤ (1 + |Real.log r|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hpos : 0 < s₂ / (1 + |Real.log r|) ^ 2 := div_pos hs₂ (by positivity)
  have hlt : s₂ / (1 + |Real.log r|) ^ 2 < 1 := (div_le_self hs₂.le hL).trans_lt hs₂1
  have key := hC (S.mult ε ω) Θ _ (s₂ / (1 + |Real.log r|) ^ 2) (s₁ * r ^ (2 * βm) / ε) hpos hlt
    (hω r hr1 hr2 Θ hΘ1 hΘ2) k a hk ha
  have e : s₂ / (1 + |Real.log r|) ^ 2 / 4 = s₂ / 4 / (1 + |Real.log r|) ^ 2 := by ring
  rw [e] at key
  exact key

/-- **Lemma 6.9, route (b)**, from Lemma 6.7, route (b) (the Chernoff-type iteration is proved). -/
theorem chanceOfBeingAbsorbedLogLoss (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundLogStmt 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 :=
  chanceOfBeingAbsorbedLogLoss_of_steps 𝒮 h67 Absorption.absorptionChernoffStep

/-- **Lemma 6.9, route (b)**, from Lemma 6.8, route (b) (`ConstantOrderLowerBoundDivLogStmt`), Lemmas 2.7, 2.8, 2.19,
and `AdjacentCellsMeetAeStep`, through Lemma 6.7, route (b). -/
theorem chanceOfBeingAbsorbedLogLoss_of_div (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivLogStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 :=
  chanceOfBeingAbsorbedLogLoss 𝒮 (constantOrderLowerBoundLog 𝒮 h68 h27 h28 h219 hcell)

end MatedCRT
