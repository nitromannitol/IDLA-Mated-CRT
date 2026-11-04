import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeAmbient
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-! The final crude-path step of the stopped-shell argument. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric _root_.HarmonicBalls Filter Topology

/-- If the shell construction gives an intermediate vertex set with small boundary
odometer and localized filled closure, the crude estimate finishes the localization.
The shell event also supplies the graph-interior inclusion needed for comparison. -/
theorem stopped_confinement_of_intermediate_shell
    (𝒮 : SpaceFillingSLEModel) (hcell : CellSizeEstimateStmt 𝒮)
    (hcrude : CrudeUpperBoundStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ζ ρ ω₀ δ : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hω : 0 < ω₀) (hωα : ω₀ < 2 / (2 + γ) ^ 2 - ζ) (hδ : 0 < δ)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (t : ℝ) (ht : 0 < t) (F : Set Ω)
    (hshell : TendsToOneOn S.P F fun ε => {ω |
      let m := S.mult ε ω
      let η := S.η ω
      let A := matedDiscreteCluster m ε η ρ t
      A ⊆ vInterior m (ballInterior ε η ρ) ∧
        ∃ Θ : Set ℤ, (0 : ℤ) ∈ Θ ∧
          (∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ ε ^ (-ω₀)) ∧
          fillCells ε η (vClosure m Θ) ⊆ outerNbhd (δ / 2) (Λ ω t)}) :
    TendsToOneOn S.P F fun ε => {ω |
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
        vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
      fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆ outerNbhd δ (Λ ω t)} := by
  have hgood := MatedCRT.HarmonicBalls.PolyHighProb.probTendsToOne
    (crude_confinement_without_closure_hypothesis 𝒮 hcell hcrude hadj
    γ hγ hγ2 ζ ρ ω₀ (δ / 2) hζ hζ1 hρ hρ1 hω hωα (by positivity) Ω S hS t ht)
  unfold ProbTendsToOne at hgood
  unfold TendsToOneOn at hshell ⊢
  have hlim := hgood.add hshell
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  apply Eventually.of_forall
  intro ε
  calc
    _ ≤ S.P ({ω | ∀ Θ : Set ℤ, (0 : ℤ) ∈ Θ →
        (∀ c ∈ vBoundary (S.mult ε ω) Θ, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c ≤ ε ^ (-ω₀)) →
        fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆
          cthickening (δ / 2) (fillCells ε (S.η ω) (vClosure (S.mult ε ω) Θ))}ᶜ ∪
        (F ∩ {ω | matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
          vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
          ∃ Θ : Set ℤ, (0 : ℤ) ∈ Θ ∧
            (∀ c ∈ vBoundary (S.mult ε ω) Θ, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c ≤ ε ^ (-ω₀)) ∧
            fillCells ε (S.η ω) (vClosure (S.mult ε ω) Θ) ⊆ outerNbhd (δ / 2) (Λ ω t)}ᶜ)) := by
      apply measure_mono
      intro ω hbad
      by_cases hg : ∀ Θ : Set ℤ, (0 : ℤ) ∈ Θ →
        (∀ c ∈ vBoundary (S.mult ε ω) Θ, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c ≤ ε ^ (-ω₀)) →
        fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆
          cthickening (δ / 2) (fillCells ε (S.η ω) (vClosure (S.mult ε ω) Θ))
      · right
        refine ⟨hbad.1, ?_⟩
        intro hs
        obtain ⟨hinterior, Θ, hzero, hbound, hloc⟩ := hs
        apply hbad.2
        refine ⟨hinterior, ?_⟩
        exact (hg Θ hzero hbound).trans <|
          (cthickening_subset_of_subset (δ / 2) hloc).trans <| by
            change cthickening (δ / 2) (cthickening (δ / 2) (Λ ω t)) ⊆ cthickening δ (Λ ω t)
            simpa using cthickening_cthickening_subset (show 0 ≤ δ / 2 by positivity)
              (show 0 ≤ δ / 2 by positivity) (Λ ω t)
      · exact Or.inl hg
    _ ≤ _ := measure_union_le _ _

end MatedCRT.Sec7
