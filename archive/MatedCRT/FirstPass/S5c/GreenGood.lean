import MatedCRT.FirstPass.S5c.GreenUpper

/-!
# FIRST PASS, GAP 2: target (4) with the Draft lower bound and the vertex-in-cell fact derived

`green_ratio_target_of_crude` (GreenUpper.lean) still takes `hGlow` (the pathwise lower bound of the Green kernel at
radius `r/2`) and `hvert` (the vertex lies in its own cell) as hypotheses. Here both are discharged:
* `hvert`: `vertexPoint ε η k = η (ε k) ∈ η '' Icc (ε (k-1)) (ε k) = cell ε η k`, for `ε > 0`;
* `hGlow`: the second conjunct of the event body of Draft `GreenKernelLowerBoundStmt` (Lemma 2.16, Draft/Section2.lean:212),
  specialised to the radius `r/2`; the hypothesis `hbody` is that conjunct on the event, for the constant `C` and the
  exponent `ω₀` of the Draft statement, with the cells of `B_{ρd - ε^{ω₀}}` and the radii `ε^{ω₀} ≤ r' ≤ dist(η(a), ∂B_{ρd})`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- The vertex point of `k` lies in its own cell (`ε > 0`). -/
theorem vertexPoint_mem_cell_of_pos {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- **hGlow from the Draft lower bound** (second conjunct of the event body of `GreenKernelLowerBoundStmt`, at radius
`r/2`, under the side conditions `ε^{ω₀} ≤ r/2` and `r/2 ≤ dist(η(a), ∂B_{ρd})`). -/
theorem hGlow_of_draft_body {ε ω0 ρd C r : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {a : ℤ}
    (hbody : ∀ a' ∈ cellVertices ε η (ball 0 (ρd - ε ^ ω0)), ∀ r' : ℝ, ε ^ ω0 ≤ r' →
      r' ≤ infDist (vertexPoint ε η a') (sphere 0 ρd) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a') (r' / 3)),
        C⁻¹ * Real.log (if vertexPoint ε η a' = vertexPoint ε η b then ε⁻¹
            else min (r' / ‖vertexPoint ε η a' - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a') r')) a' b)
    (ha : a ∈ cellVertices ε η (ball 0 (ρd - ε ^ ω0))) (hε0 : ε ^ ω0 ≤ r / 2)
    (hfar : r / 2 ≤ infDist (vertexPoint ε η a) (sphere 0 ρd)) :
    ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 2 / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min ((r / 2) / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (r / 2))) a b' :=
  hbody a ha (r / 2) hε0 hfar

/-- **Target (4) of GAP 2 from the Draft inputs**: `green_ratio_target_of_crude` with `hvert` and `hGlow` derived. The
remaining hypotheses are the Draft events at `ω` (`hbody`, `hcrude`), the cell-diameter bound `hdiam`, the ball inclusion
`hball`, the constants of the statement, and the net mass `mr` (with `hmr`, `hmrε`, from `MassEvent.lean`). -/
theorem green_ratio_target_draft {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ}
    {ε d C c r mr ρ ρd ω0 : ℝ} {a : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hε : 0 < ε) (hρ : 0 < ρ) (hc6 : c ≤ 1 / 6) (hd : d ≤ c * r) (hC : 0 < C)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hsymm : ∀ x y, m x y = m y x)
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hball : ball (vertexPoint ε η a) r ⊆ ball 0 ρ)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η a) (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (hbody : ∀ a' ∈ cellVertices ε η (ball 0 (ρd - ε ^ ω0)), ∀ r' : ℝ, ε ^ ω0 ≤ r' →
      r' ≤ infDist (vertexPoint ε η a') (sphere 0 ρd) →
      ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a') (r' / 3)),
        C⁻¹ * Real.log (if vertexPoint ε η a' = vertexPoint ε η b then ε⁻¹
            else min (r' / ‖vertexPoint ε η a' - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
          greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a') r')) a' b)
    (ha : a ∈ cellVertices ε η (ball 0 (ρd - ε ^ ω0))) (hε0 : ε ^ ω0 ≤ r / 2)
    (hfar : r / 2 ≤ infDist (vertexPoint ε η a) (sphere 0 ρd))
    (hmr : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η a) (c * r)))
    (hmrε : ε ^ (1 / 4 : ℝ) ≤ mr)
    (hcrude : ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) b b ≤ ε ^ (-(1 / 2 : ℝ))) :
    ε ^ (-(1 / 4) : ℝ) ≤
      (∑' b : interiorCellVertices ε η (ball (vertexPoint ε η a) r),
          greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) b a) /
        greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a a :=
  green_ratio_target_of_crude hap hη hp hr hε hρ hc6 hd hC h4c hεC hsymm hlf hcons hball hdiam
    (fun k => vertexPoint_mem_cell_of_pos hε k) (hGlow_of_draft_body hbody ha hε0 hfar) hmr hmrε hcrude

/-- **hdiam from the Draft cell-size estimate** (Lemma 2.8, `CellSizeEstimateStmt`, upper conjunct): if every cell meeting
`B_ρ` has diameter at most `D`, then every cell meeting `B_{r/2}(z)` has diameter at most `D` (cells are bounded, being
images of compact intervals), provided `B_{r/2}(z) ⊆ B_ρ`. -/
theorem hdiam_of_cell_size {ε ρ D r : ℝ} {η : ℝ → ℂ} {z : ℂ} (hη : Continuous η) (hsub : ball z (r / 2) ⊆ ball 0 ρ)
    (hcs : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ D) :
    ∀ k : ℤ, (cell ε η k ∩ ball z (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ D := by
  intro k hk x hx y hy
  have hmeet : (cell ε η k ∩ ball 0 ρ).Nonempty := by
    obtain ⟨w, hw, hwz⟩ := hk
    exact ⟨w, hw, hsub hwz⟩
  have hbdd : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  exact (dist_le_diam_of_mem hbdd hx hy).trans (hcs k hmeet)

end MatedCRT.S5c
