import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Bound
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Geometry
import MatedCRT.Proofs.Sec6.AnnulusHit.Geometry

/-!
# Lemma 6.8: Steps 2-4 at a vertex of `V^ε(∂B_{(4/3)𝐫_z}(z)) ∩ A`, given the map (lines 2537-2620)

`stay_le_at_frontier_vertex`: deterministic given `(m, η, μ)` and the conclusions at `ε` of Lemmas 2.16
(`GreenLowerAt`), 2.9 (`CountingAt`), 2.18 in its log-loss form (`LogLossAt`, route (b)), 2.8 (cell diameters), the
good annulus event `E_{𝐫_z}(z; C)` and Lemma 2.7 at the dyadic scales `≤ 2^{-N}`. For `b` with cell meeting
`∂B_{(4/3)R}(z)` and `B_{2R}(z)` inside the safe region of `(Θ̄ + B_r) \ cl Θ̄`, the walk from `b` stays in `A` until
it exits `U = V^ε(Θ̄ + B_r) \ Θ` with probability at most `1 - s₂/(1 + |log r|)²`.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

namespace ConstantOrderDiv

/-- The conclusion of Lemma 2.16 at `ε` (the event of `GreenKernelLowerBoundStmt`). -/
def GreenLowerAt (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ ω₂ C₂ : ℝ) : Prop :=
  ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₂)), ∀ r : ℝ,
    ε ^ ω₂ ≤ r → r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) →
    ∀ b ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b ≤
        greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b ∧
      C₂⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b then ε⁻¹
          else min (r / ‖vertexPoint ε η a - vertexPoint ε η b‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b

/-- The conclusion of `ExitTimeLogLossStep` at `ε`. -/
def LogLossAt (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (μ : Measure ℂ) (ρ α₁ C₁ : ℝ) : Prop :=
  ∀ (y : ℂ) (s : ℝ), 0 < s → ball y s ⊆ ball 0 ρ →
    ENNReal.ofReal (ε ^ α₁) ≤ μ (ball y s) →
    ∀ a ∈ cellVertices ε η (ball y s), ∀ N : ℕ,
      exitTimeMoment m (interiorCellVertices ε η (ball y s)) a N ≤
        ENNReal.ofReal (N.factorial * C₁ ^ N * ε ^ (-(N : ℝ))) *
          ((⨆ v ∈ ball y s, ∫⁻ u in thickening (ε ^ α₁) (ball y s),
              ENNReal.ofReal (Real.log (s / ‖u - v‖) + 1) ∂μ) +
            ENNReal.ofReal (Real.log (1 / s)) * μ (thickening (ε ^ α₁) (ball y s))) ^ N

/-- The conclusion of Lemma 2.9 at `ε` (the event of `CountingMeasureConvergenceStmt`). -/
def CountingAt (ε : ℝ) (η : ℝ → ℂ) (μ : Measure ℂ) (ρ α₉ β₉ : ℝ) : Prop :=
  ∀ (D : Set ℂ) (f : ℂ → ℝ) (w : ℤ → ℂ), D ⊆ ball 0 ρ →
    (∀ x ∈ thickening (ε ^ α₉) D, 0 ≤ f x ∧ |f x| ≤ ε ^ (-β₉)) →
    (∀ x ∈ thickening (ε ^ α₉) D, ∀ y ∈ thickening (ε ^ α₉) D, |f x - f y| ≤ ε ^ (-β₉) * ‖x - y‖) →
    (∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k ∩ closure D) →
    ε⁻¹ * ∫ x in D, f x ∂μ - ε ^ (-1 + α₉) ≤ ∑' k : cellVertices ε η D, f (w k) ∧
    ∑' k : cellVertices ε η D, f (w k) ≤ ε⁻¹ * ∫ x in thickening (ε ^ α₉) D, f x ∂μ + ε ^ (-1 + α₉)

theorem cellVertices_mono' {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ ⟨p, hp1, hp2⟩ => ⟨p, hp1, h hp2⟩

theorem tsum_one_eq_ncard {s : Set ℤ} (hs : s.Finite) : ∑' _ : s, (1 : ℝ) = s.ncard := by
  have := hs.fintype
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card' s,
    Set.toFinset_card]

theorem le_infDist_sphere {y : ℂ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (h : ‖y‖ + t ≤ ρ) : t ≤ infDist y (sphere 0 ρ) := by
  rw [infDist_eq_iInf]
  have : Nonempty (sphere (0 : ℂ) ρ) := (NormedSpace.sphere_nonempty.2 hρ).to_subtype
  refine le_ciInf fun q => ?_
  have hq : ‖(q : ℂ)‖ = ρ := mem_sphere_zero_iff_norm.1 q.2
  rw [dist_eq_norm]
  have h1 := norm_sub_norm_le (q : ℂ) y
  rw [norm_sub_rev] at h1
  linarith

theorem ge_of_half_pow_lt {n N : ℕ} (h : (1 / 2 : ℝ) ^ n < (1 / 2) ^ N) : N ≤ n := by
  by_contra hn
  push Not at hn
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hn.le
  linarith

/-- Points of a cell meeting `B_ρ` are within its diameter bound of each other. -/
theorem norm_sub_le_of_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {ρ d : ℝ}
    (hdiam : ∀ k, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ d) {k : ℤ} {w w' : ℂ}
    (hw : w ∈ cell ε η k) (hwρ : w ∈ ball (0 : ℂ) ρ) (hw' : w' ∈ cell ε η k) : ‖w' - w‖ ≤ d := by
  rw [← dist_eq_norm]
  exact dist_le_of_mem_cell hη (hdiam k ⟨w, hw, hwρ⟩) hw' hw

end ConstantOrderDiv

end MatedCRT
