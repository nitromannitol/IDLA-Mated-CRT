import MatedCRT.FirstPass.Derived.CellInballOfSegmentBalls
import MatedCRT.FirstPass.Derived.SegmentPathSelection

/-!
# The crude Green function bound from the segment-ball estimate and segment reachability

Composition of three reductions of `GreenFunctionCrudeBoundStmt` (BG20 Lemma 2.15 / Lemma 5.6):

* `greenFunctionCrudeBoundStmt_of_inball_of_segmentPaths`: the bound from the cell size estimate,
  the degree bound, the inradius event and the segment-path event;
* `MatedCRTEnv.IsValid.polyHighProb_cellInballEvent_of_segmentBalls`: the inradius event from
  the cell size estimate and the segment-ball estimate of Gwynne-Holden-Miller (Prop. 3.4 and
  Remark 3.9 of the almost sure KPZ relation for SLE and Brownian motion);
* `MatedCRTEnv.mem_segmentPathEvent_of_reachable`: the segment-path event from reachability of a
  vertex outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` through the cells met by the segment.

The result: `GreenFunctionCrudeBoundStmt` follows from the cell size estimate, the degree bound,
the segment-ball estimate and the segment reachability event with polynomially high probability.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- The segment-ball event `E_ε(2, r)` for the space-filling curve: every segment `η([a, b])`
inside `B_2` of diameter at least `t^{1-r}`, for a scale `t ≤ ε`, contains a Euclidean ball of
radius `t`. -/
def MatedCRTEnv.segmentBallEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (r ε : ℝ) : Set Ω :=
  {ω | ∀ t ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → S.η ω '' Icc a b ⊆ ball 0 2 →
    t ^ (1 - r) ≤ diam (S.η ω '' Icc a b) → ∃ w : ℂ, ball w t ⊆ S.η ω '' Icc a b}

/-- The segment reachability event: every vertex `x` of `V^ε(B_ρ) \ V^ε(∂B_ρ)` has a point `u`
with `‖u‖ ≤ U`, a length `ℓ` and a finite set `Y` of cells such that, in every direction `θ`, the
cell of `x` is met by the segment from `u` and a vertex outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` is
reachable from `x` in `𝒢^ε` through cells of `V^ε(B_ρ)` met by the segment. -/
def MatedCRTEnv.segmentReachEvent {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ U ε : ℝ) : Set Ω :=
  {ω | ∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ),
    ‖u‖ ≤ U ∧ ∀ θ : ℝ,
      x ∈ LatticeProb.hitFinset Y
        (fun y => LatticeProb.segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
      ∃ b ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ), Relation.ReflTransGen
        (fun a c => (c ∈ LatticeProb.hitFinset Y
            (fun y => LatticeProb.segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
          c ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧ S.mult ε ω a c ≠ 0) x b}

theorem MatedCRTEnv.segmentReachEvent_subset_segmentPathEvent {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ U ε : ℝ) : S.segmentReachEvent ρ U ε ⊆ S.segmentPathEvent ρ U ε :=
  fun _ h => MatedCRTEnv.mem_segmentPathEvent_of_reachable h

/-- **Lemma 2.15 from the segment-ball estimate and segment reachability.** The cell size
estimate, the degree bound, the segment-ball estimate `E_ε(2, r)` for every `r ∈ (0, 1)` and
the segment reachability event (at some radius `U`), each with polynomially high probability for
every valid environment, give `GreenFunctionCrudeBoundStmt`. -/
theorem greenFunctionCrudeBoundStmt_of_segmentBalls_of_reachable {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (hseg : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ r ∈ Ioo (0 : ℝ) 1, PolyHighProb S.P (S.segmentBallEvent r))
    (hR : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ U : ℝ, 0 ≤ U ∧ PolyHighProb S.P (S.segmentReachEvent ρ U)) :
    GreenFunctionCrudeBoundStmt 𝒮 := by
  refine greenFunctionCrudeBoundStmt_of_inball_of_segmentPaths hcell hdeg
    (fun γ hγ hγ2 δ ρ hδ hρ hρ1 Ω _ S hS =>
      hS.polyHighProb_cellInballEvent_of_segmentBalls hcell hγ hγ2 hδ hρ hρ1
        (hseg γ hγ hγ2 Ω S hS))
    (fun γ hγ hγ2 ρ hρ hρ1 Ω _ S hS => ?_)
  obtain ⟨U, hU, hRU⟩ := hR γ hγ hγ2 ρ hρ hρ1 Ω S hS
  exact ⟨U, hU, hRU.mono fun ε => S.segmentReachEvent_subset_segmentPathEvent ρ U ε⟩

end MatedCRT
