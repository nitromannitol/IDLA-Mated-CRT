import MatedCRT.FirstPass.Derived.BlockExitSkeletonGoodGSandwich
import MatedCRT.FirstPass.Derived.BlockExitBallFrozenWalkClose
import MatedCRT.FirstPass.Derived.BlockExitGridCellFrozenBridge
import MatedCRT.FirstPass.Derived.BlockExitWalkLocalEdgesAe
import MatedCRT.FirstPass.Derived.BlockExitWalkGridRectBounds

/-!
# The uniform-start invariance principle from the diagonal estimate

The uniform-start statement `GMS21UniformStartInput` follows from the walk-side block-exit estimates
(`BlockExitSkeletonGoodGSandwich`), which in turn follow, for the frozen set `ballFrozenSet s (R + d')` of
closed grid cells missing a ball, from

* the almost sure eventual smallness of the edges starting in a ball (`MatedCRTEnv.IsValid.ae_eventually_edges_le_of_norm_le`),
  which gives the short exit edges (`exitEdgesShort_of_localEdges`);
* the diagonal estimate `hdiag`: almost surely, eventually in the mesh, for every vertex `u` within `θ` of a point
  `y` off the frozen set, the one-step block-exit kernel of the walk restarted at `u` is `(δ, δ / 2)`-close to the
  exit law of planar Brownian motion from the embedded vertex `u` out of the block of the cell of `y`.

`hdiag` is an inline hypothesis (it is the uniform-start invariance principle itself), not a new proposition.

## Main results

* `gms21UniformStartInput_of_hdiag`: the diagonal estimate implies `GMS21UniformStartInput`.
-/

open MeasureTheory Set Metric MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit

/-- **The uniform-start invariance principle from the diagonal estimate.** If for every valid environment, null
sequence of meshes `e`, block size `s > 0`, radius `ρ₀` and tolerance `δ > 0` there is a scale `θ ∈ (0, s / 2]` with
`24 θ / s ≤ δ / 2` such that almost surely, eventually in `n`, for every `y` off the union of closed grid cells
missing `ball 0 ρ₀` and every vertex `u` with `dist (v u) y ≤ θ`, the one-step block-exit kernel of the
walk restarted at `u` is `(δ, δ / 2)`-close to the exit law of planar Brownian motion from `v u` out of the
block of the cell of `y`, then the uniform-start statement holds. -/
theorem gms21UniformStartInput_of_hdiag {𝒮 : SpaceFillingSLEModel}
    (hdiag : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (e : ℕ → ℝ), (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ (s ρ₀ δ : ℝ), 0 < s → 0 < δ →
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ s / 2 ∧ 24 * θ / s ≤ δ / 2 ∧
        ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ∀ y ∉ ballFrozenSet s ρ₀, ∀ u : ℤ,
          dist (vertexPoint (e n) (S.η ω) u) y ≤ θ →
          ProkhorovLE (walkNextBlockExitKernel (S.mult (e n) ω) (vertexPoint (e n) (S.η ω)) zero_le_one s
              (ballFrozenSet s ρ₀) (y, u))
            (blockExitKernel s (cellIndex s y) (vertexPoint (e n) (S.η ω) u)) δ (δ / 2)) :
    GMS21UniformStartInput 𝒮 := by
  have hN := fun (s ρ₀ κ : ℝ) (hs : 0 < s) (hρ₀ : 0 ≤ ρ₀) (hκ : 0 < κ) =>
    exists_blockExit_frozen_walk_bounds (F := ballFrozenSet s ρ₀) hs (measurableSet_ballFrozenSet s ρ₀)
      (gridLineStable_ballFrozenSet hs ρ₀) (D := 2 * (ρ₀ + 2 * s)) (by linarith)
      (fun y hy z hz => norm_sub_le_of_notMem_ballFrozenSet hs ρ₀ hy hz) hκ
  choose! N₀ hN₀pos hN₀ using hN
  refine gms21UniformStartInput_of_blockExit_sandwich (fun R κ s d' => N₀ s (R + d') ((κ / 2) / 16)) ?_
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ e he he0 s d' d₁ δ₀ N hs hd' hd₁ hδ₀ hgN _
  have hgN' : N₀ s (R + d') ((κ / 2) / 16) ≤ N := hgN
  have hρ₀ : 0 ≤ R + d' := by linarith
  have hκf : 0 < (κ / 2) / 16 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hN₀ s (R + d') ((κ / 2) / 16) hs hρ₀ hκf N hgN' δ₀ hδ₀
  obtain ⟨δ₂, hδ₂, H₂⟩ := hN₀ s (R + d') ((κ / 2) / 16) hs hρ₀ hκf (N + 1) (Nat.le_succ_of_le hgN') 1 one_pos
  obtain ⟨θ, hθ0, hθs, hθδ, hdiag'⟩ := hdiag γ hγ hγ2 Ω S hS e he he0 s (R + d') (min δ₁ δ₂) hs
    (lt_min hδ₁ hδ₂)
  have hedges := hS.ae_eventually_edges_le_of_norm_le hγ hγ2 he he0 ((R + d' + 2 * s) + 4 * s)
  filter_upwards [hdiag', hedges, TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hdω hedω hcont hcoc hlf
  filter_upwards [hdω, hedω θ hθ0] with n hdn hen
  intro x hx
  have hxF : vertexPoint (e n) (S.η ω) x ∉ ballFrozenSet s (R + d') := by
    refine notMem_ballFrozenSet_of_mem_ball ?_
    rw [mem_ball_zero_iff]
    rw [mem_closedBall_zero_iff] at hx
    linarith
  have hE : ExitEdgesShort (S.mult (e n) ω) (vertexPoint (e n) (S.η ω)) zero_le_one s
      (ballFrozenSet s (R + d')) θ :=
    exitEdgesShort_of_localEdges one_pos hs (fun y hy => norm_le_of_notMem_ballFrozenSet hs (R + d') hy)
      (fun b b' hb hnb _ => hen b b' hb hnb)
  have hclose : ∀ y ∉ ballFrozenSet s (R + d'), ∀ u : ℤ, dist (vertexPoint (e n) (S.η ω) u) y ≤ θ →
      ProkhorovLE (walkNextBlockExitKernel (S.mult (e n) ω) (vertexPoint (e n) (S.η ω)) zero_le_one s
        (ballFrozenSet s (R + d') ) (y, u))
        (frozenBlockExitKernel s (measurableSet_ballFrozenSet s (R + d')) y) (min δ₁ δ₂) (min δ₁ δ₂) :=
    hclose_theta_of_hdiag (S.mult (e n) ω) (vertexPoint (e n) (S.η ω)) zero_le_one hs
      (measurableSet_ballFrozenSet s (R + d')) (lt_min hδ₁ hδ₂).le hθδ hdn
  have hm1 : IsLocallyFiniteMult (S.mult (e n) ω) := hlf (e n) (he n)
  have hm2 : ∀ k : ℤ, S.mult (e n) ω k (k + 1) ≠ 0 := fun k => S.mult_succ_ne_zero (he n).le ω k
  obtain ⟨hP, -⟩ := H₁ (min δ₁ δ₂) (lt_min hδ₁ hδ₂) (min_le_left _ _) (S.mult (e n) ω) hm1 hm2 (e n) (he n)
    (S.η ω) hcont hcoc 1 one_pos x hxF θ hθ0.le hθs hE hclose
  obtain ⟨-, hA⟩ := H₂ (min δ₁ δ₂) (lt_min hδ₁ hδ₂) (min_le_right _ _) (S.mult (e n) ω) hm1 hm2 (e n)
    (he n) (S.η ω) hcont hcoc 1 one_pos x hxF θ hθ0.le hθs hE hclose
  refine ⟨prokhorovLE_mono hP le_rfl (by linarith), ?_⟩
  refine hA.trans' (measure_mono ?_) |>.trans (ENNReal.ofReal_le_ofReal (by linarith))
  intro ξ hξ
  simp only [mem_compl_iff, mem_ofPred_eq, not_exists, not_and] at hξ
  simp only [mem_ofPred_eq]
  intro j hj
  exact hξ j (Nat.lt_succ_iff.1 hj)

end UniformStartGood

end MatedCRT
