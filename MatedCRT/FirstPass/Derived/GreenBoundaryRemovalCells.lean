import MatedCRT.FirstPass.Derived.GreenBoundaryRemoval
import MatedCRT.FirstPass.S3c.ExitTimeBridge

/-!
# The Green kernel bound near the pole gives the bound of the statement (cell level)

Deterministic part of the passage from [BG20, Lem. 5.5] to [BG20, Lem. 5.4], for the cells of a
continuous curve. The Green kernel of the walk killed on the vertices of `V^ε(B_{ρ₀})` whose cells
avoid `∂B_{ρ₀}` is bounded by `C log (1/|η(a) - η(b)|)` when `ε^β ≤ |η(a) - η(b)|` is at most a third of
the distance of `η(b)` to `∂B_{ρ₀}`. If cells of vertices of `V^ε(B_{ρ₀})` have diameter at most `δ_c`
and intersecting cells are those of adjacent vertices, the bound holds for the walk killed on exiting
`V^ε(B_ρ)`, `ρ + 4 δ₀ ≤ ρ₀`, for all pairs of vertices with `|η(a) - η(b)| ≥ ε^β`, with the
constant `4 C (1 + log (4/δ₀))`.

## Main statements

* `MatedCRT.greenKernel_interiorCellVertices_le_log`: the cell level boundary removal.
-/

namespace MatedCRT

open Set Metric

variable {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε : ℝ}

/-- A cell which meets `B_ρ` and avoids `∂B_ρ` lies in `B_ρ`. -/
theorem cell_subset_ball_zero_of_mem_interiorCellVertices (hη : Continuous η) {ρ : ℝ} {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball 0 ρ)) : cell ε η k ⊆ ball 0 ρ := by
  obtain ⟨⟨x₀, hx₀c, hx₀D⟩, hk2⟩ := hk
  have hcf : ∀ x ∈ cell ε η k, x ∉ frontier (ball (0 : ℂ) ρ) := fun x hx hxf =>
    hk2 ⟨x, hx, hxf⟩
  have := S3cBridge.subset_interior_of_not_frontier (S3cBridge.cell_isPreconnected' hη k)
    hx₀c hx₀D hcf
  rwa [isOpen_ball.interior_eq] at this

/-- The point `η(a)` of a vertex whose cell meets `B_ρ` and has diameter at most `d` has norm
less than `ρ + d`. -/
theorem norm_vertexPoint_lt_of_mem_cellVertices (hη : Continuous η) (hε : 0 ≤ ε) {ρ d : ℝ} {k : ℤ}
    (hk : k ∈ cellVertices ε η (ball 0 ρ)) (hd : diam (cell ε η k) ≤ d) :
    ‖vertexPoint ε η k‖ < ρ + d := by
  obtain ⟨w, hwc, hwb⟩ := hk
  have hb : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  have hpk : vertexPoint ε η k ∈ cell ε η k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  have h1 := dist_le_diam_of_mem hb hpk hwc
  have h2 : ‖w‖ < ρ := mem_ball_zero_iff.1 hwb
  have h3 : ‖vertexPoint ε η k‖ ≤ ‖vertexPoint ε η k - w‖ + ‖w‖ := by
    simpa using norm_add_le (vertexPoint ε η k - w) w
  rw [dist_eq_norm] at h1
  linarith

/-- **Boundary removal for the cells of a continuous curve** ([BG20, proof of Lem. 5.4]).
Let `ρ + 4 δ₀ ≤ ρ₀ ≤ 1`, `4 δ_c ≤ δ₀ ≤ 1`, `0 < r₀ ≤ δ₀/2`; let the cells of the vertices of
`V^ε(B_{ρ₀})` have diameter at most `δ_c`, intersecting cells be those of adjacent vertices and
`V^ε(B_{ρ₀})` be finite. If `g_B(a, b) ≤ C log (1/|η(a) - η(b)|)` for the walk killed outside
`B = V^ε(B_{ρ₀}) \ V^ε(∂B_{ρ₀})` whenever `a ∈ B`, `b ∈ V^ε(B_ρ)` and `r₀ ≤ |η(a) - η(b)| ≤ δ₀`, then for the walk
killed outside `V^ε(B_ρ) \ V^ε(∂B_ρ)`, for all vertices `a, b` of `V^ε(B_ρ)` with `|η(a) - η(b)| ≥ r₀`,
`g(a, b) ≤ C' log (1/|η(a) - η(b)|) + C'` with `C' = 4 C (1 + log (4/δ₀))`. -/
theorem greenKernel_interiorCellVertices_le_log (hη : Continuous η) (hε : 0 < ε)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ j k, m k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ ρ₀ δ₀ dc r₀ C : ℝ} (hfin : (cellVertices ε η (ball 0 ρ₀)).Finite)
    (hρρ₀ : ρ + 4 * δ₀ ≤ ρ₀) (hρ₀ : ρ₀ ≤ 1) (hC : 0 ≤ C) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hdc : 4 * dc ≤ δ₀) (hr₀0 : 0 < r₀) (hr₀ : r₀ ≤ δ₀ / 2)
    (hdiam : ∀ k ∈ cellVertices ε η (ball 0 ρ₀), diam (cell ε η k) ≤ dc)
    (hmain : ∀ a ∈ interiorCellVertices ε η (ball 0 ρ₀), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      r₀ ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ δ₀ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ₀)) a b ≤
        C * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖)) :
    ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ b ∈ cellVertices ε η (ball 0 ρ),
      r₀ ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b ≤
        4 * C * (1 + Real.log (4 / δ₀)) * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) +
          4 * C * (1 + Real.log (4 / δ₀)) := by
  intro a ha b hb hr
  set B := interiorCellVertices ε η (ball 0 ρ₀) with hB
  set K := Real.log (4 / δ₀) with hK
  have hK0 : 0 ≤ K := Real.log_nonneg (by rw [le_div_iff₀ hδ₀]; linarith)
  have hρρ : cellVertices ε η (ball 0 ρ) ⊆ cellVertices ε η (ball 0 ρ₀) := fun k ⟨w, hwc, hwb⟩ =>
    ⟨w, hwc, ball_subset_ball (by linarith) hwb⟩
  have hBsub : B ⊆ cellVertices ε η (ball 0 ρ₀) := fun k hk => hk.1
  have hBfin : B.Finite := hfin.subset hBsub
  have hI : interiorCellVertices ε η (ball 0 ρ) ⊆ B :=
    S3cBridge.interiorCellVertices_mono_of_subset hη (ball_subset_ball (by linarith))
  have hIfin : (interiorCellVertices ε η (ball 0 ρ)).Finite := hBfin.subset hI
  have hnorm : ∀ k ∈ cellVertices ε η (ball 0 ρ), ‖vertexPoint ε η k‖ < ρ + dc := fun k hk =>
    norm_vertexPoint_lt_of_mem_cellVertices hη hε.le hk (hdiam k (hρρ hk))
  have hr2 : ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ 2 := by
    have := norm_sub_le (vertexPoint ε η a) (vertexPoint ε η b)
    linarith [hnorm a ha, hnorm b hb]
  have hrpos : 0 < ‖vertexPoint ε η a - vertexPoint ε η b‖ := hr₀0.trans_le hr
  set L := Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) with hL
  have hL1 : -(3 / 4 : ℝ) ≤ L := by
    have h1 : Real.log (1 / 2) ≤ L := Real.log_le_log (by norm_num) (by
      rw [div_le_div_iff₀ (by norm_num) hrpos]; linarith)
    have h2 : Real.log (1 / 2) = - Real.log 2 := by
      rw [one_div, Real.log_inv]
    have := Real.log_two_lt_d9
    linarith
  have hfinal : ∀ g : ℝ, g ≤ C * L + C * K →
      g ≤ 4 * C * (1 + K) * L + 4 * C * (1 + K) := by
    intro g hg
    have h := mul_nonneg hC (mul_nonneg (by linarith : 0 ≤ 3 + 4 * K) (by linarith : 0 ≤ L + 1 - 1 / 4))
    nlinarith [h, hC]
  by_cases haI : a ∈ interiorCellVertices ε η (ball 0 ρ)
  · have haB : a ∈ B := hI haI
    have hmono := greenKernel_mono_of_finite hlf hcons hIfin hBfin hI a b
    have hstep : ∀ y ∈ B, ∀ y', m y y' ≠ 0 →
        ‖vertexPoint ε η y - vertexPoint ε η y'‖ ≤ 2 * dc := by
      intro y hy y' hyy'
      obtain ⟨w, hw1, hw2⟩ := hadj y' y hyy'
      have hyc : y ∈ cellVertices ε η (ball 0 ρ₀) := hBsub hy
      have hcy := cell_subset_ball_zero_of_mem_interiorCellVertices hη hy
      have hy'c : y' ∈ cellVertices ε η (ball 0 ρ₀) := ⟨w, hw1, hcy hw2⟩
      have hb1 : Bornology.IsBounded (cell ε η y) := (isCompact_Icc.image hη).isBounded
      have hb2 : Bornology.IsBounded (cell ε η y') := (isCompact_Icc.image hη).isBounded
      have hpy : vertexPoint ε η y ∈ cell ε η y :=
        ⟨ε * y, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
      have hpy' : vertexPoint ε η y' ∈ cell ε η y' :=
        ⟨ε * y', ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
      have h1 := dist_le_diam_of_mem hb1 hpy hw2
      have h2 := dist_le_diam_of_mem hb2 hpy' hw1
      have h3 := hdiam y hyc
      have h4 := hdiam y' hy'c
      rw [dist_eq_norm] at h1 h2
      have := norm_sub_le_norm_sub_add_norm_sub (vertexPoint ε η y) w (vertexPoint ε η y')
      rw [norm_sub_rev w] at this
      linarith
    have key := greenKernel_le_log_of_nearRange hlf hcons hBfin
      (fun k => vertexPoint ε η k) hC hδ₀ hδ₀1 hr₀ hdc hstep hmain a haB b hb hr hr2
    exact hfinal _ (hmono.trans key)
  · have h0 : greenKernel m (interiorCellVertices ε η (ball 0 ρ)) a b = 0 := by
      unfold greenKernel
      rw [greenFn_eq_zero_of_not_mem m haI b]
      simp
    rw [h0]
    have := hfinal 0
    have h5 : (0 : ℝ) ≤ 4 * C * (1 + K) * L + 4 * C * (1 + K) := by
      have : 0 ≤ 4 * C * (1 + K) * (L + 1) := mul_nonneg (by positivity) (by linarith)
      linarith
    exact h5

end MatedCRT
