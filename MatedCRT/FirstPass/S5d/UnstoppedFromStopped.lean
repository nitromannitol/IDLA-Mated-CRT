import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.Draft.Section5
import MatedCRT.FirstPass.S5d.StoppedMono

/-!
# The unstopped conjunct of Proposition 5.1 from the stopped conjunct

Corrected proof [C21] (paper/idla_mated_crt-corrected.tex, proof of Proposition 5.1): "monotonicity in the stopping domain gives
both conclusions". The IDLA cluster is the stopped cluster with the whole lattice as stopping domain,
`idlaCluster xs n = stoppedIDLACluster univ xs n` (Defs/RandomWalk.lean:159-165), so monotonicity of the stopped cluster in the
stopping domain (`stoppedIDLACluster_mono_domain`, StoppedMono.lean) gives `stoppedIDLACluster Θ xs n ⊆ idlaCluster xs n` for
every `Θ`. The unstopped bad event is then contained in the stopped bad event, and the stopped conjunct
`IDLALowerBoundStoppedStep` (Steps/Sec5/IDLALowerBound.lean:68) gives the unstopped conjunct by squeezing.
No discrete-cluster inner bound (Proposition 4.2) and no strict positivity input is needed for this conjunct.
-/

namespace MatedCRT.S5d

open MeasureTheory Filter Topology Set

/-- The IDLA cluster is the stopped cluster with the whole lattice as stopping domain (definitional). -/
theorem idlaCluster_eq_stoppedIDLACluster_univ (xs : ℕ → ℕ → ℤ) (n : ℕ) :
    idlaCluster xs n = stoppedIDLACluster univ xs n := rfl

/-- A stopped IDLA cluster (any stopping domain) is contained in the unstopped IDLA cluster. -/
theorem stoppedIDLACluster_subset_idlaCluster (Θ : Set ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ) :
    stoppedIDLACluster Θ xs n ⊆ idlaCluster xs n := by
  rw [idlaCluster_eq_stoppedIDLACluster_univ]
  exact stoppedIDLACluster_mono_domain (subset_univ Θ) xs n

/-- `fillCells` is monotone in the set of labels. -/
theorem fillCells_mono_labels {ε : ℝ} {η : ℝ → ℂ} {A B : Set ℤ} (h : A ⊆ B) :
    fillCells ε η A ⊆ fillCells ε η B :=
  biUnion_subset_biUnion_left h

/-- **The unstopped conjunct from the stopped step.** `IDLALowerBoundStoppedStep` implies `IDLALowerBoundStmt`: the first
conjunct's bad event is contained in the stopped bad event (stopped cluster ⊆ IDLA cluster), so its probability tends to
zero by squeezing. -/
theorem iDLALowerBound_of_stoppedStep (𝒮 : SpaceFillingSLEModel) (hstop : IDLALowerBoundStoppedStep 𝒮) :
    IDLALowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hs := hstop γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨?_, hs⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ε => measure_mono ?_)
  intro p hp
  refine ⟨hp.1, fun h => hp.2 (h.trans ?_)⟩
  exact fillCells_mono_labels (stoppedIDLACluster_subset_idlaCluster _ _ _)

end MatedCRT.S5d
