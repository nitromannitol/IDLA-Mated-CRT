import MatedCRT.FirstPass.Derived.SrwHarnackPair

/-!
# Harnack inequality for the Green function from the grid estimates

The consequence of `srwLaw_pairSep_lower` for the Green function of simple random walk on the mated-CRT map killed
outside `B = V(B_{ρ''}) \ V(∂B_{ρ''})`, `ρ'' = (1 + ρ)/2`: for a vertex `b` whose cell meets `B_ρ`, a scale `s` and two
vertices `a, y` whose cells meet `∂B_s(z)`, `z` the point of `b`,
`p₀ p₁ g_B(y, b) ≤ g_B(a, b)`  (Berestycki–Gwynne (2020), Lemma 3.9 with the separation event (3.21)).
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

section Green

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- **Harnack inequality for the Green function on a sphere** (see the module documentation). -/
theorem mul_greenKernel_le_of_pairEvents (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {η : ℝ → ℂ} (hHc : H.cell = cell ε η) {ρ δ h₀ s₀ s₁ s₂ s : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ x' ∈ cell ε η k, dist x x' ≤ δ)
    (hs₀ : 300 * h₀ ≤ s₀) (hs₁ : s₁ + 3 * h₀ ≤ s₀) (hs₂ : 5 * s₂ ≤ s₀) (hs : s₀ ≤ s) (hsρ : s ≤ (1 - ρ) / 8)
    {p₀ p₁ : ℝ} (hp₀ : 0 ≤ p₀) (hp₁ : 0 ≤ p₁)
    (hItin : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l → ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (sphere (latticePt h₀ m' n') (h₀ * l)),
        ENNReal.ofReal p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | PolarTemplateItinerary H (latticePt h₀ m' n') (h₀ * l)
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (h311 : ∀ (w : ℂ) (r : ℝ), s₂ ≤ r → r ≤ (1 + ρ) / 2 → ball w (2 * r) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (ball w r),
        ENNReal.ofReal p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (hB : (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))).Finite)
    {b : ℤ} (hb : (cell ε η b ∩ ball (0 : ℂ) ρ).Nonempty)
    {a y : ℤ} (ha : a ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)))
    (hy : y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s))) :
    p₀ * p₁ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) y b ≤
      greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2))) a b := by
  have hs0 : 0 < s := by linarith
  have hbB : b ∈ interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)) := by
    obtain ⟨x0, hx0c, hx0b⟩ := hb
    have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg x0) (mem_ball_zero_iff.1 hx0b)
    exact mem_interiorCellVertices_of_diam η (by linarith) (by linarith) (by linarith) ⟨x0, hx0c, hx0b⟩
      (fun x hx x' hx' => hdiam b ⟨x0, hx0c, ball_subset_ball (by linarith : ρ ≤ (1 + ρ) / 2) hx0b⟩ x hx x' hx')
  refine mul_greenKernel_le_of_separation hlf hcons hB hbB (mul_nonneg hp₀ hp₁) ?_
  rw [ENNReal.ofReal_mul hp₀]
  exact srwLaw_pairSep_lower h hε H hlf hcons hHc hh hδ hδh hdiam hs₀ hs₁ hs₂ hs hsρ hItin h311 hb ha hy

end Green

end MatedCRT

#print axioms MatedCRT.mul_greenKernel_le_of_pairEvents
