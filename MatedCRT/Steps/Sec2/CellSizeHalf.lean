import MatedCRT.Steps.Sec2.VolumeGrowthHalf

/-!
# Lemma 2.8 in two halves: the upper and the lower cell-diameter bound

Lemma 2.8 (lemma:cell-size-estimate, line 669; BG20 Lemma 2.4) is the conjunction of two estimates with polynomially
high probability as `ε → 0`, for the cells `H^ε_a` which meet `B_ρ`:
* the **upper half** `diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}` (`CellSizeUpperStmt`);
* the **lower half** `ε^{2/(2-γ)² + ζ} ≤ diam(H^ε_a)` (`CellSizeLowerStmt`).
`cellSizeEstimateStmt_iff_halves` proves `CellSizeEstimateStmt 𝒮 ↔ CellSizeUpperStmt 𝒮 ∧ CellSizeLowerStmt 𝒮`.

The upper half is derived (`MatedCRT/Proofs/Sec2/CellSizeHalf/Main.lean`) from Leonardo Bonanno's formalization of
GMS19 Lemma 2.7 (`MatedCRTHarmonic.GMSLemma27.lemma27_segments`, adapted from Leonardo Bonanno's lean-formalizations,
https://github.com/leobon12/lean-formalizations, as ported to Lattice-Probability), the field `segmentsContainBalls`
(GHM15 Proposition 3.4 with Remark 3.9) of the mating-of-trees coupling of `MatedCRTEnv.IsValid`, Bonanno's GHM15
Lemma 3.12 and the step `ConeAreaDominatesWholePlaneGFFStep`. The lower half needs the sharp upper volume bound (the
upper half of Lemma 2.7), which is not in Bonanno's code, and stays the cited input.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 2.8, upper half** (lemma:cell-size-estimate, line 669; BG20 Lemma 2.4, upper bound; GMS19 Lemma 2.7).
Fix `ζ ∈ (0, 1)` and `ρ ∈ (0, 1)`. With polynomially high probability as `ε → 0`, every cell `H^ε_a` which meets `B_ρ`
has `diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}`. -/
def CellSizeUpperStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ζ ρ : ℝ, 0 < ζ → ζ < 1 → 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
    diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}

/-- **Lemma 2.8, lower half** (lemma:cell-size-estimate, line 669; BG20 Lemma 2.4, lower bound). Fix `ζ ∈ (0, 1)` and
`ρ ∈ (0, 1)`. With polynomially high probability as `ε → 0`, every cell `H^ε_a` which meets `B_ρ` has
`ε^{2/(2-γ)² + ζ} ≤ diam(H^ε_a)`. Cited (BG20 Lemma 2.4); not in Bonanno's formalization. -/
def CellSizeLowerStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ζ ρ : ℝ, 0 < ζ → ζ < 1 → 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
    ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k)}

/-- **Lemma 2.8 is the conjunction of its two halves.** -/
theorem cellSizeEstimateStmt_iff_halves (𝒮 : SpaceFillingSLEModel) :
    CellSizeEstimateStmt 𝒮 ↔ CellSizeUpperStmt 𝒮 ∧ CellSizeLowerStmt 𝒮 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
      exact polyHighProb_mono_of_subset (h γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS)
        fun ε ω hω k hk => (hω k hk).2
    · intro γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
      exact polyHighProb_mono_of_subset (h γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS)
        fun ε ω hω k hk => (hω k hk).1
  · rintro ⟨hu, hl⟩ γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
    exact polyHighProb_of_inter (hl γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS)
      (hu γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS) fun ε ω hω k hk => ⟨hω.1 k hk, hω.2 k hk⟩

end MatedCRT
