import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ConnectedFaceChain
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-! # Locally finite covers by space-filling curve cells -/

namespace MatedCRT

open Set Filter Topology Metric

/-- The cells of a continuous proper curve form a locally finite family. -/
theorem locallyFinite_cells_of_proper {ε : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) : LocallyFinite (cell ε η) := by
  intro z
  refine ⟨closedBall z 1, closedBall_mem_nhds z (by norm_num), ?_⟩
  exact cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall z 1)

/-- A compact connected set covered by cells of a continuous, proper,
surjective curve gives a graph path between two cells meeting the set, when
cells that intersect on the set have connected graph labels. -/
theorem IsPreconnected.reachable_of_cell_cover
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hsurj : Function.Surjective η) {K : Set ℂ}
    (hK : IsPreconnected K) (hcompact : IsCompact K)
    (G : SimpleGraph ℤ)
    (hlink : ∀ i j, (K ∩ cell ε η i ∩ cell ε η j).Nonempty → G.Reachable i j)
    {first last : ℤ} (hfirst : (K ∩ cell ε η first).Nonempty)
    (hlast : (K ∩ cell ε η last).Nonempty) : G.Reachable first last := by
  apply IsPreconnected.reachable_of_locallyFinite_closed_face_cover hK hcompact
    (cell ε η) (locallyFinite_cells_of_proper hη hp hε)
    (fun _ => (isCompact_Icc.image hη).isClosed) ?_ G id hlink hfirst hlast
  intro z hz
  obtain ⟨t, rfl⟩ := hsurj z
  exact mem_iUnion.mpr ⟨_, Tightness.mem_cell_ceil hε t⟩

end MatedCRT
