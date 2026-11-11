import MatedCRT.FirstPass.S5d.StoppedExitInput
import MatedCRT.FirstPass.S5d.FloorCells
import MatedCRT.FirstPass.S5e.SecondGreenStep

/-!
# The single floor input of the stopped clause: `StoppedFloorCellStep`

`StoppedFloorCellStep 𝒮` is the floor on every cell meeting `B⁻_{δ/2}(Λ_t)` (corrected tex 2362). It is the ONE floor input of Proposition 5.1 and of the
second Green step (`StoppedFloorHalfStep`, S5e/SecondGreenStep.lean:29). Here it is derived:
* `stoppedFloorStep_of_cellFloor`: `StoppedFloorStep` (the floor on the vertices `V^ε(B⁻_δ(Λ_t))`, S5d/StoppedExitInput.lean:129),
  since every target vertex `a` has its cell meeting `B⁻_δ(Λ_t) ⊆ B⁻_{δ/2}(Λ_t)`;
* `stoppedFloorHalfStep_of_cellFloor`: `StoppedFloorHalfStep` (positivity of the odometer on the cells meeting `B⁻_{δ/2}`).
The Prop is OPEN; nothing in this file proves it.
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT

/-- **The floor on every cell meeting `B⁻_{δ/2}(Λ_t)` (the single floor input of Proposition 5.1, OPEN).** For `δ ∈ (0, ρ)` and `t > 0`
there is a measurable random constant `c > 0` such that, on `{t < T}`, with probability tending to one as `ε → 0⁺`: every cell
`cell ε (S.η ω) k` meeting `B⁻_{δ/2}(Λ_t)` satisfies `c/ε ≤ u^ε(k)` (`stoppedOdometer`). Source: corrected tex 2362 ([C21]) and the
expanded argument (Steps 1-9; its inputs are h41, h33, h28, hm, hgap, hμae, hcell). -/
def StoppedFloorCellStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω | ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
        c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k}

/-- The cell floor implies the vertex floor `StoppedFloorStep` (targets `V^ε(B⁻_δ(Λ_t))` are vertices of cells meeting
`B⁻_δ(Λ_t) ⊆ B⁻_{δ/2}(Λ_t)`, `innerNbhd_half_of_innerNbhd`). -/
theorem stoppedFloorStep_of_cellFloor {𝒮 : SpaceFillingSLEModel} (h : StoppedFloorCellStep 𝒮) :
    StoppedFloorStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, hc, hcpos, hT⟩ := h γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨c, hc, hcpos, ?_⟩
  unfold TendsToOneOn at hT ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  refine Eventually.of_forall fun ε => measure_mono ?_
  rintro ω ⟨hF, hω⟩
  refine ⟨hF, fun hcell => hω ?_⟩
  have hcell' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
      c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k := hcell
  show ∀ a ∈ stoppedTargetSet S Λ δ t ε ω, c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a
  intro a ha
  obtain ⟨y, hy1, hy2⟩ := ha
  exact hcell' a ⟨y, hy1, innerNbhd_half_of_innerNbhd hδ _ hy2⟩

/-- The cell floor implies the positivity `StoppedFloorHalfStep` used by the second Green inequality (S5e/SecondGreenStep.lean:29):
`c/ε > 0` for `ε > 0`. -/
theorem stoppedFloorHalfStep_of_cellFloor {𝒮 : SpaceFillingSLEModel} (h : StoppedFloorCellStep 𝒮) :
    S5e.StoppedFloorHalfStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, _, hcpos, hT⟩ := h γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  unfold TendsToOneOn at hT ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono
  rintro ω ⟨hF, hω⟩
  refine ⟨hF, fun hcell => hω ?_⟩
  have hcell' : ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
      c ω / ε ≤ stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k := hcell
  show ∀ k : ℤ, (cell ε (S.η ω) k ∩ innerNbhd (δ / 2) (Λ ω t)).Nonempty →
    0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t k
  intro k hk
  exact lt_of_lt_of_le (div_pos (hcpos ω) hε) (hcell' k hk)

end MatedCRT
