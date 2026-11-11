import MatedCRT.FirstPass.S4S6c.Uniform68Events
import MatedCRT.FirstPass.S4S6c.GreenTest68
import MatedCRT.FirstPass.S4S6c.Uniform68Selector

/-!
# Event inputs of the local test `hloc` (file `Uniform68Local.lean`)

`Uniform68Events.hloc_point` (the local test of Lemma 6.8 at one start vertex `b` and radius `R`) takes two probabilistic
inputs, `hGreenLow` and `hdraft`. This file extracts them, at one fixed environment `ω` and one fixed `ε`, from the
event forms of the cited Draft statements:

* `hGreenLow` from the lower Green bound of Lemma 2.16 (`GreenKernelLowerBoundStmt`, BG20 Lemma 4.4), at the radius
  `r = R/8`: `greenLow_of_event`;
* `hdraft` from the exit-time moment bound of Lemma 2.18 (`ExitTimeUpperBoundStmt`, BG20 Proposition 5.1) with `N = 2`
  on `D = B_{R/4}(η(b))`: `exitMoment_of_event`;
* `prob_le_min_q0`: the constant `q₀` of the walk-level Lemma 6.8 is `min 1 X`, which weakens the bound of `hloc_point`.

The event hypotheses are stated in the pointwise form that holds on the polynomially-high-probability event of the Draft
statement. Terminology: Green kernel of the walk killed on leaving the window (Berestycki-Gwynne, Armitage-Gardiner),
exit-time moments of the killed walk (Norris, discrete Markov chains).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT
namespace Uniform68Local

/-- Monotonicity of the cell vertices in the set: `V^ε(D) ⊆ V^ε(D')` when `D ⊆ D'`. -/
theorem cellVertices_mono_local {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') {k : ℤ}
    (hk : k ∈ cellVertices ε η D) : k ∈ cellVertices ε η D' :=
  (show (cell ε η k ∩ D).Nonempty from hk).mono (Set.inter_subset_inter_right _ h)

/-- **The lower Green bound of `hloc_point` from Lemma 2.16 at one `ω`.** At a start vertex `b` in `V^ε(B_{ρ-ε^{ω₀}})`
with `ε^{ω₀} ≤ R/8 ≤ dist(η(b), ∂B_ρ)` (the radius `r = R/8` of the event), the Green kernel of `B_{R/8}(η(b))` is at least
`C⁻¹ log(...) - 1` at every target `b'` in `V^ε(B_{c₀R}(η(b)))`, because `c₀ ≤ 1/24` puts those targets in
`B_{r/3}(η(b))`. -/
theorem greenLow_of_event {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε ρ ω₀ C c0 R : ℝ} {b : ℤ}
    (hR : 0 ≤ R) (hc0 : c0 ≤ 1 / 24)
    (hG : ∀ a ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀)), ∀ r : ℝ, ε ^ ω₀ ≤ r →
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) →
      ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min (r / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b')
    (hb : b ∈ cellVertices ε η (ball 0 (ρ - ε ^ ω₀))) (hlo : ε ^ ω₀ ≤ R / 8)
    (hup : R / 8 ≤ infDist (vertexPoint ε η b) (sphere 0 ρ)) :
    ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η b) (c0 * R)),
      C⁻¹ * Real.log (if vertexPoint ε η b = vertexPoint ε η b' then ε⁻¹
          else min (R / 8 / ‖vertexPoint ε η b - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 8))) b b' := by
  intro b' hb'
  have hsub : ball (vertexPoint ε η b) (c0 * R) ⊆ ball (vertexPoint ε η b) (R / 8 / 3) := by
    apply Metric.ball_subset_ball
    have := mul_le_mul_of_nonneg_right hc0 hR
    linarith
  exact hG b hb (R / 8) hlo hup b' (cellVertices_mono_local hsub hb')

/-- **The exit-time moment of `hloc_point` from Lemma 2.18 at one `ω`.** For the ball `D = B_{R/4}(η(b))` of the event,
with `μ(D) ≥ ε^α`, the second exit-time moment of the killed walk from `b` is bounded by `2! C² ε⁻²` times the squared
supremum of the logarithmic potential of `D` over its `ε^α`-thickening. -/
theorem exitMoment_of_event {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε ρ α C R : ℝ} {b : ℤ}
    (hD : ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z ∈ D, ∫⁻ w in thickening (ε ^ α) D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ^ N)
    (hsub : ball (vertexPoint ε η b) (R / 4) ⊆ ball 0 ρ)
    (hmass : ENNReal.ofReal (ε ^ α) ≤ μ (ball (vertexPoint ε η b) (R / 4)))
    (hb : b ∈ cellVertices ε η (ball (vertexPoint ε η b) (R / 4))) :
    exitTimeMoment m (interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4))) b 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) *
        (⨆ v ∈ ball (vertexPoint ε η b) (R / 4),
          ∫⁻ u in thickening (ε ^ α) (ball (vertexPoint ε η b) (R / 4)),
            ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ^ (2 : ℕ) :=
  hD _ measurableSet_ball hsub hmass b hb 2

/-- **Weakening the constant of `hloc_point` to `q₀ = min 1 X`.** A bound `1 - X / L²` implies the bound `1 - min 1 X / L²`
(the walk-level Lemma 6.8 needs `0 < q₀ ≤ 1`). -/
theorem prob_le_min_q0 {P : ℝ≥0∞} {X L : ℝ} (h : P ≤ ENNReal.ofReal (1 - X / L ^ 2)) :
    P ≤ ENNReal.ofReal (1 - min 1 X / L ^ 2) := by
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have := div_le_div_of_nonneg_right (min_le_right 1 X) (sq_nonneg L)
  linarith

/-- **The selected radius is a good seven-adic radius.** If some candidate exponent `n ∈ [n₋, n₊]` is good at the centre,
then the selector `Uniform68Selector.selectRadius` returns `7^{-n}` for a good candidate `n` (the least one), so the radius
`R_j` of the test is good (the good-annulus property `IsGoodAnnulusEvent` of the cover event holds at `R_j`). -/
theorem selectRadius_good {δ : ℝ} (good : ℤ → Prop) (h : ∃ n ∈ Uniform68Selector.candidates δ, good n) :
    ∃ n : ℤ, n ∈ Uniform68Selector.candidates δ ∧ good n ∧
      Uniform68Selector.selectRadius δ good = (1 / 7 : ℝ) ^ n := by
  classical
  have hne : ((Uniform68Selector.candidates δ).filter good).Nonempty := by
    obtain ⟨n, hn, hg⟩ := h
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hg⟩⟩
  have hmem := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hmem
  refine ⟨_, hmem.1, hmem.2, ?_⟩
  unfold Uniform68Selector.selectRadius
  simp [hne]

end Uniform68Local

#print axioms MatedCRT.Uniform68Local.greenLow_of_event
#print axioms MatedCRT.Uniform68Local.exitMoment_of_event
#print axioms MatedCRT.Uniform68Local.prob_le_min_q0
#print axioms MatedCRT.Uniform68Local.selectRadius_good

end MatedCRT
