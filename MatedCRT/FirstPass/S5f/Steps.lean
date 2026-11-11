import MatedCRT.Defs.Setting
import MatedCRT.Defs.Map

/-!
# First pass: the three NEW steps of the surplus maximum outside the killing set

`stoppedMaxOutside_of_steps` (MatedCRT/FirstPass/S5f.lean) proves `StoppedMaxOutsideStep 𝒮` from the Draft statements
of Theorems 4.1 and Lemma 3.3 and the External input `MepsScalingInput`, and from the three NEW steps below. These are
paper-owned claims (not frozen inputs): they concern the SLE curve `η`, its cells `cell ε η k` and the mesh-`ε`
vertex labels, and they are taken as explicit hypotheses until proved. Each is stated with its written source.

Terminology: Duplantier–Sheffield (quantum-area parametrization, cells of the mesh `ε` as images of intervals), and
Armitage–Gardiner (Green functions, neighbourhood of the pole).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **NEW step N-cell (cell representative).** For every mesh `ε > 0`, almost surely, every cell `cell ε η k` that meets
`B_ρ` contains a point of `B_ρ` which belongs to no other cell with a smaller index, i.e. a point `x` with
`vertexOf ε η x = k` (`a^ε_x = k`, eq:plane-to-embedding). Source: corrected tex 2360 (proof of Proposition 5.1, [C21]): "quantum-area
parametrization makes distinct-cell overlaps `μ_h`-null, so each cell contains a point belonging to no other cell; evaluate the
rescaled convergence there", and notes/fp-gaps/CHATGPT-idla-C20-C21-referee.md (Line 2360). The written source does not
prove the overlap nullity for non-adjacent cells, nor that the representative lies in `B_ρ`; it is a gap to be filled. -/
def StoppedCellRepresentativeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ).Nonempty →
    ∃ x ∈ cell ε (S.η ω) k ∩ ball (0 : ℂ) ρ, vertexOf ε (S.η ω) x = k

/-- **NEW step N-pole (pole cell).** For all small mesh sizes, almost surely the pole of the discrete Green function of the
stopped clause is the vertex `0`: `a^ε_0 = 0`. Needed because the discrete obstacle `matedObstacle` uses the vertex `0` as its
pole (Defs/Sandpile.lean:75), whereas Lemma 3.3 (`UniformConvergenceGreenKernelStmt`) uses the pole `a^ε_y` with `y = 0`.
Source: corrected tex 2360 ("the cell indexed by `0` contains `η(0) = 0 ∈ Λ_t`", used for `0 ∈ I^ε`). The written source
states only that the cell indexed by `0` contains `η(0)`; it does not exclude an earlier cell containing `0`, i.e.
`η⁻¹{0} = {0}` a.s. is not written. -/
def StoppedPoleCellStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂S.P, vertexOf ε (S.η ω) 0 = 0

/-- **NEW step N-rad (random radius of the origin neighbourhood).** For every `t > 0`, the probability, on the event
`{t < T}`, that the cluster `Λ_t` does not contain a ball `B_s(0)` tends to `0` as `s → 0⁺`. Source: corrected tex 2360:
"`Λ_t` contains a neighborhood of zero. Thus all cells that can contribute positively to `M_ε` stay outside some random
positive-radius disk." The written source gives the deterministic inclusion (`Λ_t` is open and contains `0` on `{t < T}`)
but not the passage from a random radius to a deterministic one, which needs measurability of the events
`{B_s(0) ⊆ Λ_t}` (or of the random radius); this is a gap to be filled. -/
def StoppedOriginRadiusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
    Tendsto (fun s : ℝ => S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ ¬ ball (0 : ℂ) s ⊆ Λ ω t})
      (𝓝[>] 0) (𝓝 0)

end MatedCRT
