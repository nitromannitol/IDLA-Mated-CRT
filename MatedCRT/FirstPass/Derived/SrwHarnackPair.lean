import MatedCRT.FirstPass.Derived.SrwRingSphere
import MatedCRT.FirstPass.Derived.HarnackAssembly

/-!
# The separation event of the Harnack inequality from the grid estimates

Berestycki–Gwynne (2020), Lemma 3.10 in the form (3.21) at the pole `b` of the Green function.  Fix `ρ ∈ (0, 1)`,
the killing domain `B = V(B_{ρ''}) \ V(∂B_{ρ''})`, `ρ'' = (1 + ρ)/2`, a vertex `b` whose cell meets `B_ρ`, and a scale
`s ∈ [s₀, (1 - ρ)/8]`, with `300 h ≤ s₀`, where all cells meeting `B_{ρ''}` have diameter at most `δ ≤ h`.  Suppose the
edge-end walk follows a polar template itinerary with probability at least `p₀` from the vertices meeting every grid
circle of radius `h ℓ ≥ s₁` about a lattice point of mesh `h` whose double ball lies in `B_{ρ''}`, and satisfies the event
of Lemma 3.11 with probability at least `p₁` from the vertices meeting every ball of radius `r ≥ s₂`, `B_{2r}(w) ⊂ B_{ρ''}`.
Then for any two vertices whose cells meet `∂B_s(z)`, `z` the point of `b`, simple random walk from the first one
separates the second from `{b} ∪ Bᶜ` through the trace before the first visit to `{b} ∪ Bᶜ`, with probability at least
`p₀ p₁`.  This is the separation hypothesis of `mul_greenKernel_le_of_separation`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

section Pair

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- **The separation event of the Harnack inequality at the pole `b`** (see the module documentation). -/
theorem srwLaw_pairSep_lower (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {η : ℝ → ℂ} (hHc : H.cell = cell ε η) {ρ δ h₀ s₀ s₁ s₂ s : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ x' ∈ cell ε η k, dist x x' ≤ δ)
    (hs₀ : 300 * h₀ ≤ s₀) (hs₁ : s₁ + 3 * h₀ ≤ s₀) (hs₂ : 5 * s₂ ≤ s₀) (hs : s₀ ≤ s) (hsρ : s ≤ (1 - ρ) / 8)
    {p₀ p₁ : ℝ≥0∞}
    (hItin : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l → ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (sphere (latticePt h₀ m' n') (h₀ * l)),
        p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | PolarTemplateItinerary H (latticePt h₀ m' n') (h₀ * l)
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    (h311 : ∀ (w : ℂ) (r : ℝ), s₂ ≤ r → r ≤ (1 + ρ) / 2 → ball w (2 * r) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (ball w r),
        p₁ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε ω h) H.cell w r
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)})
    {b : ℤ} (hb : (cell ε η b ∩ ball (0 : ℂ) ρ).Nonempty)
    {x y : ℤ} (hx : x ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)))
    (hy : y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s))) :
    p₀ * p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | GraphSeparates (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (traceBefore (id : ℤ → ℤ)
          ({b} ∪ (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)))ᶜ) ξ) {y}
        ({b} ∪ (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)))ᶜ)} := by
  have hHc' : ∀ k, H.cell k = cell ε η k := fun k => congrFun hHc k
  have hs0 : 0 < s := by linarith
  have hρ1 : ρ < 1 := by linarith
  obtain ⟨x0, hx0c, hx0b⟩ := hb
  have hx0n : ‖x0‖ < ρ := mem_ball_zero_iff.1 hx0b
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg x0) hx0n
  have hzc : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell hε η b
  generalize vertexPoint ε η b = z at hzc hx hy
  have hz_norm : ‖z‖ ≤ ρ + δ := by
    have h1 := hdiam b ⟨x0, hx0c, ball_subset_ball (by linarith : ρ ≤ (1 + ρ) / 2) hx0b⟩ z hzc x0 hx0c
    have h2 := norm_sub_norm_le z x0
    rw [dist_eq_norm] at h1
    linarith
  obtain ⟨m', n', la, lb, hzz, ha1, ha2, hb1, hb2⟩ := exists_ringGrid hh z s
  have hz'n : ‖latticePt h₀ m' n'‖ ≤ ρ + δ + h₀ := by
    have h1 := norm_sub_norm_le (latticePt h₀ m' n') z
    rw [← dist_eq_norm, dist_comm] at h1
    linarith
  have hsph : ∀ k ∈ cellVertices ε η (frontier (ball z s)), ∃ q ∈ H.cell k, dist q z = s := by
    intro k hk
    obtain ⟨q, hq1, hq2⟩ := exists_mem_cell_dist_eq_of_mem_cellVertices_frontier hs0.ne' hk
    exact ⟨q, by rw [hHc' k]; exact hq1, hq2⟩
  have hballc : ∀ c : ℝ, c ≤ s + 3 * h₀ → ball (latticePt h₀ m' n') (2 * c) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) := by
    intro c hc q hq
    rw [mem_ball] at hq
    rw [mem_ball_zero_iff]
    have h1 := norm_sub_norm_le q (latticePt h₀ m' n')
    rw [← dist_eq_norm] at h1
    linarith
  refine srwLaw_ringPair_lower_sphere h hε H hlf hcons (z := z) (z' := latticePt h₀ m' n') (s := s)
    (h₀ := h₀) (δ := δ) (T := 3 * s) (a := h₀ * la) (b := h₀ * lb) hh hδ hδh (by linarith) ha1 ha2 hb1 hb2 hzz
    ?_ (P := {b}) (O := (interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)))ᶜ) ?_ ?_ ?_ ?_ ?_ ?_
    (hsph x hx) (hsph y hy)
  · intro k hk x hxk x' hxk'
    rw [hHc' k] at hk hxk hxk'
    obtain ⟨q, hq, hqb⟩ := hk
    refine hdiam k ⟨q, hq, ?_⟩ x hxk x' hxk'
    rw [mem_ball] at hqb
    rw [mem_ball_zero_iff]
    have h1 := norm_sub_norm_le q (latticePt h₀ m' n')
    rw [← dist_eq_norm] at h1
    linarith
  · intro k hk q hq
    rw [Set.mem_singleton_iff] at hk
    rw [hk, hHc' b] at hq
    have h1 := hdiam b ⟨x0, hx0c, ball_subset_ball (by linarith : ρ ≤ (1 + ρ) / 2) hx0b⟩ q hq z hzc
    have h2 := dist_triangle q z (latticePt h₀ m' n')
    linarith
  · intro k hk
    obtain ⟨q, hqc, hqn⟩ := exists_mem_cell_le_norm_of_not_mem_interior hε η
      (R := (1 + ρ) / 2) (by linarith) hk
    refine ⟨q, by rw [hHc' k]; exact hqc, ?_⟩
    have h1 := norm_sub_norm_le q (latticePt h₀ m' n')
    rw [← dist_eq_norm] at h1
    linarith
  · linarith
  · linarith
  · intro c hc
    rcases hc with rfl | rfl
    · exact hItin m' n' la (by linarith) (hballc _ (by linarith))
    · exact hItin m' n' lb (by linarith) (hballc _ (by linarith))
  · intro w hw
    have hwz : dist w z = s := mem_sphere.1 hw
    refine h311 w (s / 5) (by linarith) (by linarith) ?_
    intro q hq
    rw [mem_ball] at hq
    rw [mem_ball_zero_iff]
    have h1 := norm_sub_norm_le q w
    have h2 := norm_sub_norm_le w z
    rw [← dist_eq_norm] at h1 h2
    linarith

end Pair

end MatedCRT

#print axioms MatedCRT.srwLaw_pairSep_lower
