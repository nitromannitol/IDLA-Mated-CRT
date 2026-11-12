import MatedCRT.FirstPass.Derived.GreenSegmentFlowBoundAE
import MatedCRT.FirstPass.Derived.GreenBoundaryRemovalCells

/-!
# The logarithmic Green kernel bound near the pole from a Harnack inequality and a cell sum

Deterministic assembly of [BG20, Lem. 5.5]: if the Green kernel `g_B(·, b)` of the walk killed on
`B = V^ε(B_{ρ₀}) \ V^ε(∂B_{ρ₀})` satisfies a Harnack inequality `g(a) ≤ C₁ g(y)` between the
vertices whose cells meet a circle `∂B_s(η(b))`, and the weighted sum of `(diam H_a / dist(η(b), H_a))²`
over the cells outside `B_s(η(b))` is at most `C₂ log (1/s)`, then `g_B(a, b) ≤ C₁ C₂ log (1/s)` for
the vertices `a` with `|η(a) - η(b)| = s`. The unit flow is the expected flow of the segment paths
of almost every direction; some vertex `y` of the inner boundary of `V^ε(B_s(η(b)))`, which meets the
circle, has `g_B(y, b)` at most the cell sum.

## Main statement

* `MatedCRT.greenKernel_le_log_of_harnack_of_cellSum`.
-/

namespace MatedCRT

open Finset Metric Set LatticeProb

variable {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε : ℝ}

open Classical in
/-- **Assembly of [BG20, Lem. 5.5].** See the module docstring. -/
theorem greenKernel_le_log_of_harnack_of_cellSum (hη : Continuous η) (hε : 0 < ε)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a)
    (hadj : ∀ j k, m k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    {ρ ρ₀ δ₀ dc r₀ C₁ C₂ : ℝ} (hfin : (cellVertices ε η (ball 0 ρ₀)).Finite)
    (hρρ₀ : ρ + 4 * δ₀ ≤ ρ₀) (hδ₀ : 0 < δ₀) (hdc : 4 * dc ≤ δ₀) (hr₀0 : 0 < r₀) (hC₁ : 0 ≤ C₁)
    (hdiam : ∀ k ∈ cellVertices ε η (ball 0 ρ₀), diam (cell ε η k) ≤ dc)
    (hHarn : ∀ b ∈ cellVertices ε η (ball 0 ρ), ∀ s : ℝ, r₀ ≤ s → s ≤ δ₀ →
      ∀ a ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
      ∀ y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
      greenKernel m (interiorCellVertices ε η (ball 0 ρ₀)) a b ≤
        C₁ * greenKernel m (interiorCellVertices ε η (ball 0 ρ₀)) y b)
    (hpath : ∀ b ∈ interiorCellVertices ε η (ball 0 ρ₀),
      ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
      (∀ᵐ θ ∂uniformDirection, (segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ).Nodup) ∧
      (∀ᵐ θ ∂uniformDirection, (segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ).IsChain
        fun a c => m a c ≠ 0) ∧
      (∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ = b :: p ∧
        (∀ v ∈ b :: p, v ∈ cellVertices ε η (ball 0 ρ₀)) ∧
        (b :: p).getLast (List.cons_ne_nil b p) ∉ interiorCellVertices ε η (ball 0 ρ₀)))
    (hsum : ∀ b ∈ cellVertices ε η (ball 0 ρ), ∀ s : ℝ, r₀ ≤ s → s ≤ δ₀ →
      ∑ k ∈ hfin.toFinset with k ∉ cellVertices ε η (ball (vertexPoint ε η b) s),
        (mdeg m k : ℝ) * (diam (cell ε η k) / infDist (vertexPoint ε η b) (cell ε η k)) ^ 2 ≤
          C₂ * Real.log (1 / s)) :
    ∀ b ∈ cellVertices ε η (ball 0 ρ), ∀ a ∈ interiorCellVertices ε η (ball 0 ρ₀),
      r₀ ≤ ‖vertexPoint ε η a - vertexPoint ε η b‖ → ‖vertexPoint ε η a - vertexPoint ε η b‖ ≤ δ₀ →
      greenKernel m (interiorCellVertices ε η (ball 0 ρ₀)) a b ≤
        C₁ * C₂ * Real.log (1 / ‖vertexPoint ε η a - vertexPoint ε η b‖) := by
  intro b hb a haB hr hrδ
  have hcl : ∀ k, IsClosed (cell ε η k) := fun k => (isCompact_Icc.image hη).isClosed
  have hbdd : ∀ k, Bornology.IsBounded (cell ε η k) := fun k => (isCompact_Icc.image hη).isBounded
  have hmem : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  set z := vertexPoint ε η b with hz
  set s := ‖vertexPoint ε η a - z‖ with hs
  have hs0 : 0 < s := hr₀0.trans_le hr
  set B := interiorCellVertices ε η (ball 0 ρ₀) with hB
  have hρρ : cellVertices ε η (ball 0 ρ) ⊆ cellVertices ε η (ball 0 ρ₀) :=
    fun k ⟨w, hwc, hwb⟩ => ⟨w, hwc, ball_subset_ball (by linarith) hwb⟩
  have hbS := hρρ hb
  have hBsub : B ⊆ cellVertices ε η (ball 0 ρ₀) := fun k hk => hk.1
  have hBfin : B.Finite := hfin.subset hBsub
  have hzn : ‖z‖ < ρ + dc := norm_vertexPoint_lt_of_mem_cellVertices hη hε.le hb (hdiam b hbS)
  set A : Set ℤ := cellVertices ε η (ball z s) with hA
  have hAB : A ⊆ B := by
    intro v hv
    obtain ⟨w, hwv, hwb⟩ := hv
    have hwn : ‖w - z‖ < s := mem_ball_iff_norm.1 hwb
    have hwz : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
    have hwρ : ‖w‖ < ρ₀ := by linarith
    have hρ₀pos : 0 < ρ₀ := (norm_nonneg w).trans_lt hwρ
    refine ⟨⟨w, hwv, mem_ball_zero_iff.2 hwρ⟩, ?_⟩
    rintro ⟨u, huv, huf⟩
    have hd : dist u w ≤ diam (cell ε η v) :=
      dist_le_diam_of_mem (hbdd v) huv hwv
    have hdv := hdiam v ⟨w, hwv, mem_ball_zero_iff.2 hwρ⟩
    rw [dist_eq_norm] at hd
    have huw : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by simpa using norm_add_le (u - w) w
    rw [frontier_ball 0 hρ₀pos.ne', mem_sphere_zero_iff_norm] at huf
    linarith
  have hbA : b ∈ A := ⟨z, hmem b, mem_ball_self hs0⟩
  have hAfin : A.Finite := hBfin.subset hAB
  obtain ⟨ℓ, Y, F, hF, hnd, hchain, hpt⟩ := hpath b (hAB hbA)
  have hBS : hBfin.toFinset ⊆ hfin.toFinset := fun k hk =>
    hfin.mem_toFinset.2 (hBsub (hBfin.mem_toFinset.1 hk))
  have hAB' : hAfin.toFinset ⊆ hBfin.toFinset := fun k hk =>
    hBfin.mem_toFinset.2 (hAB (hAfin.mem_toFinset.1 hk))
  have hS : ∀ k ∈ hBfin.toFinset, ∀ k', m k k' ≠ 0 → k' ∈ hfin.toFinset := by
    intro k hk k' hkk'
    have hkB := hBfin.mem_toFinset.1 hk
    obtain ⟨w, hw1, hw2⟩ := hadj k' k hkk'
    exact hfin.mem_toFinset.2 ⟨w, hw1, cell_subset_ball_zero_of_mem_interiorCellVertices hη hkB hw2⟩
  have hpath' : ∀ᵐ θ ∂uniformDirection, ∃ p, segmentPath z ℓ (cell ε η) Y F θ = b :: p ∧
      (∀ v ∈ b :: p, v ∈ hfin.toFinset) ∧
      (b :: p).getLast (List.cons_ne_nil b p) ∉ hBfin.toFinset := by
    filter_upwards [hpt] with θ ⟨p, hp, hv, hl⟩
    exact ⟨p, hp, fun v hv' => hfin.mem_toFinset.2 (hv v hv'),
      fun h => hl (hBfin.mem_toFinset.1 h)⟩
  have hpos : ∀ k ∈ hfin.toFinset, k ∉ hAfin.toFinset → 0 < infDist z (cell ε η k) := by
    intro k _ hkA
    have hzk : z ∉ cell ε η k := fun h =>
      hkA (hAfin.mem_toFinset.2 ⟨z, h, mem_ball_self hs0⟩)
    exact (hcl k).notMem_iff_infDist_pos ⟨_, hmem k⟩ |>.1 hzk
  obtain ⟨y, hyA, ⟨w, hwA, hyw⟩, -, hyle⟩ :=
    exists_mem_innerBoundary_greenKernel_le_segmentPaths_ae hlf hcons hsymm hBS hAB' hS
      (hAfin.mem_toFinset.2 hbA) hF (fun k _ => hcl k) hnd hchain hpath'
      (fun k _ _ => hbdd k) hpos
  rw [Set.Finite.coe_toFinset] at hyle
  have hyA' : y ∈ A := hAfin.mem_toFinset.1 hyA
  have hwA' : w ∉ A := fun h => hwA (hAfin.mem_toFinset.2 h)
  -- the cell of `y` meets the circle
  have hyf : y ∈ cellVertices ε η (frontier (ball z s)) := by
    obtain ⟨t0, ht0y, ht0b⟩ := hyA'
    obtain ⟨t, htw, hty⟩ := hadj w y hyw
    have htb : t ∉ ball z s := fun h => hwA' ⟨t, htw, h⟩
    by_contra hne
    have hcf : ∀ x ∈ cell ε η y, x ∉ frontier (ball z s) := fun x hx hxf => hne ⟨x, hx, hxf⟩
    have := S3cBridge.subset_interior_of_not_frontier (S3cBridge.cell_isPreconnected' hη y)
      ht0y ht0b hcf
    rw [isOpen_ball.interior_eq] at this
    exact htb (this hty)
  have haf : a ∈ cellVertices ε η (frontier (ball z s)) := by
    refine ⟨vertexPoint ε η a, hmem a, ?_⟩
    rw [frontier_ball z hs0.ne', mem_sphere, dist_eq_norm]
  have hsumeq : ∑ k ∈ hfin.toFinset with k ∉ hAfin.toFinset,
      (mdeg m k : ℝ) * (diam (cell ε η k) / infDist z (cell ε η k)) ^ 2 =
      ∑ k ∈ hfin.toFinset with k ∉ A,
      (mdeg m k : ℝ) * (diam (cell ε η k) / infDist z (cell ε η k)) ^ 2 := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp [Set.Finite.mem_toFinset]
  calc greenKernel m B a b ≤ C₁ * greenKernel m B y b := hHarn b hb s hr hrδ a haf y hyf
    _ ≤ C₁ * (C₂ * Real.log (1 / s)) := by
        refine mul_le_mul_of_nonneg_left (hyle.trans ?_) hC₁
        rw [hsumeq]
        exact hsum b hb s hr hrδ
    _ = C₁ * C₂ * Real.log (1 / s) := by ring

end MatedCRT
