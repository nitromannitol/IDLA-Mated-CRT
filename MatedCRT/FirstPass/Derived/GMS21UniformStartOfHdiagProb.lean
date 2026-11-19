import MatedCRT.FirstPass.Derived.UniformStartSubsequence
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfHdiag

/-!
# The uniform-start invariance principle from the diagonal estimate in probability

`gms21UniformStartInput_of_hdiag` asks for the diagonal estimate almost surely, eventually in the mesh, along
every null sequence.  What the planar invariance principle gives is convergence in probability: for a fixed
scale `θ` and tolerance `δ`, the probability (outer measure) that the one-step block-exit kernel of the walk
restarted at some vertex within `θ` of a point off the frozen set fails to be `(δ, δ / 2)`-close to the planar
Brownian exit law tends to `0` with the mesh.  This file derives the uniform-start statement from that form.

For a null sequence `e` the outer measures of the failure events at mesh `e n` tend to `0`; the first
Borel–Cantelli lemma along a subsequence (`hBC`, for arbitrary sets) gives a subsequence along which almost
surely, eventually, the diagonal estimate holds; the almost-sure chain of `gms21UniformStartInput_of_hdiag`
applies along that subsequence, and the reverse Fatou lemma along subsequences (`hL4sub`) replaces the one
along the full sequence.  `hBC` and `hL4sub` are general measure-theory statements, hypotheses here.

## Main results

* `gms21UniformStartInput_of_hdiagProb`: the diagonal estimate in probability implies
  `GMS21UniformStartInput`.
-/

open MeasureTheory Set Metric MarkovProcess Filter ReflectedGMS.GMS
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace UniformStartGood

open LatticeProb MatedCRT.StopAtExitCmp MatedCRT.BlockExit

/-- **The uniform-start invariance principle from the diagonal estimate in probability.** If for every valid
environment, block size `s > 0`, radius `ρ₀` and tolerance `δ > 0` there is a scale `θ ∈ (0, s / 2]` with
`24 θ / s ≤ δ / 2` such that for every `θ' > 0` there is `ε₀ > 0` with the following: for all `ε ∈ (0, ε₀)` the
outer measure of the set of `ω` for which some `y` off the union of closed grid cells missing `ball 0 ρ₀` and
some vertex `u` with `dist (v u) y ≤ θ` have the one-step block-exit kernel of the walk restarted at `u` not
`(δ, δ / 2)`-close to the exit law of planar Brownian motion from `v u` out of the block of the cell of `y`,
is at most `θ'`, then the uniform-start statement holds. -/
theorem gms21UniformStartInput_of_hdiagProb {𝒮 : SpaceFillingSLEModel}
    (hBC : ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (B : ℕ → Set Ω),
      Tendsto (fun n => μ (B n)) atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ B (φ k))
    (hL4sub : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (M : ℝ → Set Ω),
      (∀ ε : ℝ, 0 < ε → MeasurableSet (M ε)) →
      (∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ M (e (φ n))) →
      ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → P (M ε)ᶜ ≤ ENNReal.ofReal θ)
    (hdiagProb : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → ∀ (s ρ₀ δ : ℝ), 0 < s → 0 < δ →
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ s / 2 ∧ 24 * θ / s ≤ δ / 2 ∧
        ∀ θ' : ℝ, 0 < θ' → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.P {ω | ¬ ∀ y ∉ ballFrozenSet s ρ₀, ∀ u : ℤ, dist (vertexPoint ε (S.η ω) u) y ≤ θ →
            ProkhorovLE (walkNextBlockExitKernel (S.mult ε ω) (vertexPoint ε (S.η ω)) zero_le_one s
                (ballFrozenSet s ρ₀) (y, u))
              (blockExitKernel s (cellIndex s y) (vertexPoint ε (S.η ω) u)) δ (δ / 2)} ≤
            ENNReal.ofReal θ') :
    GMS21UniformStartInput 𝒮 := by
  have hN := fun (s ρ₀ κ : ℝ) (hs : 0 < s) (hρ₀ : 0 ≤ ρ₀) (hκ : 0 < κ) =>
    exists_blockExit_frozen_walk_bounds (F := ballFrozenSet s ρ₀) hs (measurableSet_ballFrozenSet s ρ₀)
      (gridLineStable_ballFrozenSet hs ρ₀) (D := 2 * (ρ₀ + 2 * s)) (by linarith)
      (fun y hy z hz => norm_sub_le_of_notMem_ballFrozenSet hs ρ₀ hy hz) hκ
  choose! N₀ hN₀pos hN₀ using hN
  refine gms21UniformStartInput_of_blockExit_sandwich_sub hL4sub
    (fun R κ s d' => N₀ s (R + d') ((κ / 2) / 16)) ?_
  intro γ hγ hγ2 Ω _ S hS R ρ hρ hρR κ hκ e he he0 s d' d₁ δ₀ N hs hd' hd₁ hδ₀ hgN _
  have hgN' : N₀ s (R + d') ((κ / 2) / 16) ≤ N := hgN
  have hρ₀ : 0 ≤ R + d' := by linarith
  have hκf : 0 < (κ / 2) / 16 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hN₀ s (R + d') ((κ / 2) / 16) hs hρ₀ hκf N hgN' δ₀ hδ₀
  obtain ⟨δ₂, hδ₂, H₂⟩ := hN₀ s (R + d') ((κ / 2) / 16) hs hρ₀ hκf (N + 1) (Nat.le_succ_of_le hgN') 1 one_pos
  obtain ⟨θ, hθ0, hθs, hθδ, hdiag'⟩ := hdiagProb γ hγ hγ2 Ω S hS s (R + d') (min δ₁ δ₂) hs
    (lt_min hδ₁ hδ₂)
  set Bad : ℝ → Set Ω := fun ε => {ω | ¬ ∀ y ∉ ballFrozenSet s (R + d'), ∀ u : ℤ,
    dist (vertexPoint ε (S.η ω) u) y ≤ θ →
      ProkhorovLE (walkNextBlockExitKernel (S.mult ε ω) (vertexPoint ε (S.η ω)) zero_le_one s
          (ballFrozenSet s (R + d')) (y, u))
        (blockExitKernel s (cellIndex s y) (vertexPoint ε (S.η ω) u)) (min δ₁ δ₂) (min δ₁ δ₂ / 2)}
    with hBad
  have ht : Tendsto (fun n => S.P (Bad (e n))) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    rcases eq_or_ne c ⊤ with rfl | hct
    · exact Eventually.of_forall fun n => le_top
    · obtain ⟨ε₀, hε₀, hε⟩ := hdiag' c.toReal (ENNReal.toReal_pos hc.ne' hct)
      filter_upwards [he0.eventually (gt_mem_nhds hε₀)] with n hn
      calc S.P (Bad (e n)) ≤ ENNReal.ofReal c.toReal := hε (e n) (he n) hn
        _ = c := ENNReal.ofReal_toReal hct
  obtain ⟨φ, hφ, hae⟩ := hBC S.P (fun n => Bad (e n)) ht
  refine ⟨φ, hφ, ?_⟩
  have he' : ∀ n, 0 < e (φ n) := fun n => he _
  have he0' : Tendsto (fun n => e (φ n)) atTop (𝓝 0) := he0.comp hφ.tendsto_atTop
  have hedges := hS.ae_eventually_edges_le_of_norm_le hγ hγ2 he' he0' ((R + d' + 2 * s) + 4 * s)
  filter_upwards [hae, hedges, TraceInputs68.ae_continuous_eta hS, hS.ae_tendsto_cocompact,
    hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hdω hedω hcont hcoc hlf
  filter_upwards [hdω, hedω θ hθ0] with n hdn' hen
  have hdn : ∀ y ∉ ballFrozenSet s (R + d'), ∀ u : ℤ, dist (vertexPoint (e (φ n)) (S.η ω) u) y ≤ θ →
      ProkhorovLE (walkNextBlockExitKernel (S.mult (e (φ n)) ω) (vertexPoint (e (φ n)) (S.η ω))
          zero_le_one s (ballFrozenSet s (R + d') ) (y, u))
        (blockExitKernel s (cellIndex s y) (vertexPoint (e (φ n)) (S.η ω) u)) (min δ₁ δ₂)
        (min δ₁ δ₂ / 2) := by
    by_contra hcon
    exact hdn' hcon
  intro x hx
  have hxF : vertexPoint (e (φ n)) (S.η ω) x ∉ ballFrozenSet s (R + d') := by
    refine notMem_ballFrozenSet_of_mem_ball ?_
    rw [mem_ball_zero_iff]
    rw [mem_closedBall_zero_iff] at hx
    linarith
  have hE : ExitEdgesShort (S.mult (e (φ n)) ω) (vertexPoint (e (φ n)) (S.η ω)) zero_le_one s
      (ballFrozenSet s (R + d')) θ :=
    exitEdgesShort_of_localEdges one_pos hs (fun y hy => norm_le_of_notMem_ballFrozenSet hs (R + d') hy)
      (fun b b' hb hnb _ => hen b b' hb hnb)
  have hclose : ∀ y ∉ ballFrozenSet s (R + d'), ∀ u : ℤ, dist (vertexPoint (e (φ n)) (S.η ω) u) y ≤ θ →
      ProkhorovLE (walkNextBlockExitKernel (S.mult (e (φ n)) ω) (vertexPoint (e (φ n)) (S.η ω)) zero_le_one s
        (ballFrozenSet s (R + d') ) (y, u))
        (frozenBlockExitKernel s (measurableSet_ballFrozenSet s (R + d')) y) (min δ₁ δ₂) (min δ₁ δ₂) :=
    hclose_theta_of_hdiag (S.mult (e (φ n)) ω) (vertexPoint (e (φ n)) (S.η ω)) zero_le_one hs
      (measurableSet_ballFrozenSet s (R + d')) (lt_min hδ₁ hδ₂).le hθδ hdn
  have hm1 : IsLocallyFiniteMult (S.mult (e (φ n)) ω) := hlf (e (φ n)) (he (φ n))
  have hm2 : ∀ k : ℤ, S.mult (e (φ n)) ω k (k + 1) ≠ 0 := fun k => S.mult_succ_ne_zero (he (φ n)).le ω k
  obtain ⟨hP, -⟩ := H₁ (min δ₁ δ₂) (lt_min hδ₁ hδ₂) (min_le_left _ _) (S.mult (e (φ n)) ω) hm1 hm2 (e (φ n)) (he (φ n))
    (S.η ω) hcont hcoc 1 one_pos x hxF θ hθ0.le hθs hE hclose
  obtain ⟨-, hA⟩ := H₂ (min δ₁ δ₂) (lt_min hδ₁ hδ₂) (min_le_right _ _) (S.mult (e (φ n)) ω) hm1 hm2 (e (φ n))
    (he (φ n)) (S.η ω) hcont hcoc 1 one_pos x hxF θ hθ0.le hθs hE hclose
  refine ⟨prokhorovLE_mono hP le_rfl (by linarith), ?_⟩
  refine hA.trans' (measure_mono ?_) |>.trans (ENNReal.ofReal_le_ofReal (by linarith))
  intro ξ hξ
  simp only [mem_compl_iff, mem_ofPred_eq, not_exists, not_and] at hξ
  simp only [mem_ofPred_eq]
  intro j hj
  exact hξ j (Nat.lt_succ_iff.1 hj)


end UniformStartGood

end MatedCRT
