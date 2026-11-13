import MatedCRT.FirstPass.Derived.HarnackPairUnionBound
import MatedCRT.FirstPass.Derived.HarnackRingBall

/-!
# Harnack inequality on circles for the Green kernel of a disk centred at the pole, from the pair events

Berestycki–Gwynne (2020), (4.13) in the proof of Lemma 4.4: for a vertex `b`, a radius `r` with
`B_r(η(b)) ⊂ B_{(1+ρ)/2}(0)` and a scale `s` with `4 s ≤ r`, the Green kernel of the disk
`B = V(B_r(η(b))) \ V(∂B_r(η(b)))` with pole `b` is comparable at any two vertices whose cells meet `∂B_s(η(b))`.

The input is the pair of events of Lemma 3.9 ((3.21), the polar template itinerary at the grid circles, and (3.35), the
disconnection event of Lemma 3.11), in the same form as for the fixed domain `B_{(1+ρ)/2}(0)`: the barrier built from
these events around `∂B_s(η(b))` lies in `B_{2s}(η(b))`, so it separates the circle from `{b}` and from the complement
of `B` as soon as `4 s ≤ r`.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity MatedCRTHarmonic.Markov MatedCRTHarmonic.CellFamily
open MatedCRTHarmonic.GMSMain.T15A

section PairBall

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)

/-- **The separation event of the Harnack inequality for the disk `B_r(η(b))`** (Berestycki–Gwynne (2020), Lemma 3.10
in the form (3.21), used in (4.13)).  With the pair events at the grid circles and balls inside `B_{(1+ρ)/2}(0)`,
`B_r(η(b)) ⊂ B_{(1+ρ)/2}(0)` and `4 s ≤ r`, simple random walk from a vertex whose cell meets `∂B_s(η(b))` separates any
other such vertex from `{b} ∪ Bᶜ`, `B = V(B_r(η(b))) \ V(∂B_r(η(b)))`, before reaching that set, with probability at
least `p₀ p₁`. -/
theorem srwLaw_pairSep_lower_ball (hε : 0 ≤ ε) {o : ℤ}
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω h) o)
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {η : ℝ → ℂ} (hHc : H.cell = cell ε η) {ρ δ h₀ s₀ s₁ s₂ s r : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ x' ∈ cell ε η k, dist x x' ≤ δ)
    (hs₀ : 300 * h₀ ≤ s₀) (hs₁ : s₁ + 3 * h₀ ≤ s₀) (hs₂ : 5 * s₂ ≤ s₀) (hs : s₀ ≤ s) (hsr : 4 * s ≤ r)
    {b : ℤ} (hbr : ball (vertexPoint ε η b) r ⊆ ball (0 : ℂ) ((1 + ρ) / 2))
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
    {x y : ℤ} (hx : x ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)))
    (hy : y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s))) :
    p₀ * p₁ ≤ srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | GraphSeparates (srwGraph (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
        (traceBefore (id : ℤ → ℤ)
          ({b} ∪ (interiorCellVertices ε η (ball (vertexPoint ε η b) r))ᶜ) ξ) {y}
        ({b} ∪ (interiorCellVertices ε η (ball (vertexPoint ε η b) r))ᶜ)} := by
  have hHc' : ∀ k, H.cell k = cell ε η k := fun k => congrFun hHc k
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := by linarith
  have hRr : r ≤ (1 + ρ) / 2 := radius_le_of_ball_subset_ball_zero hr0 hbr
  have hzc : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell hε η b
  have hdb : ∀ q ∈ cell ε η b, dist q (vertexPoint ε η b) ≤ δ := fun q hq =>
    hdiam b ⟨_, hzc, hbr (mem_ball_self hr0)⟩ q hq _ hzc
  set z := vertexPoint ε η b with hzdef
  obtain ⟨m', n', la, lb, hzz, ha1, ha2, hb1, hb2⟩ := exists_ringGrid hh z s
  have hsub : ∀ (c : ℝ) (w : ℂ), dist w z + c ≤ r → ball w c ⊆ ball (0 : ℂ) ((1 + ρ) / 2) := by
    intro c w hc q hq
    apply hbr
    rw [mem_ball] at hq ⊢
    have := dist_triangle q w z
    linarith
  have hz'z : dist (latticePt h₀ m' n') z ≤ h₀ := by
    rw [dist_comm]
    exact hzz
  have hsph : ∀ k ∈ cellVertices ε η (frontier (ball z s)), ∃ q ∈ H.cell k, dist q z = s := by
    intro k hk
    obtain ⟨q, hq1, hq2⟩ := exists_mem_cell_dist_eq_of_mem_cellVertices_frontier hs0.ne' hk
    exact ⟨q, by rw [hHc' k]; exact hq1, hq2⟩
  refine srwLaw_ringPair_lower_sphere h hε H hlf hcons (z := z) (z' := latticePt h₀ m' n') (s := s)
    (h₀ := h₀) (δ := δ) (T := 3 * s) (a := h₀ * la) (b := h₀ * lb) hh hδ hδh (by linarith) ha1 ha2 hb1 hb2 hzz
    ?_ (P := {b}) (O := (interiorCellVertices ε η (ball z r))ᶜ) ?_ ?_ ?_ ?_ ?_ ?_
    (hsph x hx) (hsph y hy)
  · intro k hk x hxk x' hxk'
    rw [hHc' k] at hk hxk hxk'
    obtain ⟨q, hq, hqb⟩ := hk
    exact hdiam k ⟨q, hq, hsub (6 * (h₀ * lb) / 5) (latticePt h₀ m' n') (by linarith) hqb⟩ x hxk x' hxk'
  · intro k hk q hq
    rw [Set.mem_singleton_iff] at hk
    rw [hk, hHc' b] at hq
    have h1 := hdb q hq
    have h2 := dist_triangle q z (latticePt h₀ m' n')
    linarith
  · intro k hk
    obtain ⟨q, hqc, hqd⟩ := exists_mem_cell_dist_ge_of_not_mem_interior_ball hε η hr0.ne' hk
    refine ⟨q, by rw [hHc' k]; exact hqc, ?_⟩
    have h1 := dist_triangle q (latticePt h₀ m' n') z
    linarith
  · linarith
  · linarith
  · intro c hc
    rcases hc with rfl | rfl
    · exact hItin m' n' la (by linarith) (hsub _ _ (by linarith))
    · exact hItin m' n' lb (by linarith) (hsub _ _ (by linarith))
  · intro w hw
    have hwz : dist w z = s := mem_sphere.1 hw
    exact h311 w (s / 5) (by linarith) (by linarith) (hsub _ _ (by linarith))

end PairBall

section GreenBall

/-- **Quenched Harnack inequality on circles for the Green kernel of a disk centred at the pole, from the pair events**
(Berestycki–Gwynne (2020), (4.13) in the proof of Lemma 4.4, with the events (3.21) and (3.35) of Lemma 3.9).  The
itinerary events hold at all lattice circles of mesh `h₀` with radius `h₀ l ≥ s₁` whose double ball lies in
`B_{(1+ρ)/2}(0)`, the disconnection event holds for the radii `≥ s₂` in `B_{(1+ρ)/2}(0)`, and the cells meeting
`B_{(1+ρ)/2}(0)` have diameter `≤ δ ≤ h₀`.  Then for every vertex `b`, every disk `B_r(η(b)) ⊂ B_{(1+ρ)/2}(0)` with a
finite interior vertex set `B`, and every `s ≥ s₀` with `4 s ≤ r`, `g_B(a, b) ≤ (p₀ p₁)⁻¹ g_B(y, b)` for any two
vertices `a, y` whose cells meet `∂B_s(η(b))`. -/
theorem greenKernel_le_inv_mul_of_pairEvents_ball {ε : ℝ} (hε : 0 ≤ ε) {ω : MatedCRTHarmonic.MatedCRT.Path2}
    {η : ℝ → ℂ}
    (hlf : IsLocallyFiniteMult (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)))
    (hcons : ∀ k : ℤ, bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k (k + 1) ≠ 0)
    {ρ δ h₀ s₀ s₁ s₂ p₀ p₁ : ℝ} (hh : 0 < h₀) (hδ : 0 ≤ δ) (hδh : δ ≤ h₀)
    (hdiam : ∀ k, (cell ε η k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ x' ∈ cell ε η k, dist x x' ≤ δ)
    (hs₀ : 300 * h₀ ≤ s₀) (hs₁ : s₁ + 3 * h₀ ≤ s₀) (hs₂ : 5 * s₂ ≤ s₀)
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hItin : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l → ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      PairItinGood ε ω η p₀ (latticePt h₀ m' n') (h₀ * l))
    (h311 : PairL311Good ε ω η ((1 + ρ) / 2) s₂ p₁) :
    ∀ (b : ℤ) (r : ℝ), ball (vertexPoint ε η b) r ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      (interiorCellVertices ε η (ball (vertexPoint ε η b) r)).Finite →
      ∀ s : ℝ, s₀ ≤ s → 4 * s ≤ r →
      ∀ a ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
      ∀ y ∈ cellVertices ε η (frontier (ball (vertexPoint ε η b) s)),
        greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
            (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) a b ≤
          (p₀ * p₁)⁻¹ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
            (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y b := by
  obtain ⟨h, H, hHc, h311'⟩ := h311
  have hItin' : ∀ m' n' l : ℤ, s₁ ≤ h₀ * l →
      ball (latticePt h₀ m' n') (2 * (h₀ * l)) ⊆ ball (0 : ℂ) ((1 + ρ) / 2) →
      ∀ y ∈ verticesMeeting H.cell (sphere (latticePt h₀ m' n') (h₀ * l)),
        ENNReal.ofReal p₀ ≤ (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw y
          {ξ | PolarTemplateItinerary H (latticePt h₀ m' n') (h₀ * l)
            ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ξ)} := by
    intro m' n' l hl hball y hy
    obtain ⟨h', H', hH'c, hit⟩ := hItin m' n' l hl hball
    have hHH : H' = H := cellularEmbedding_eq_of_cell_eq (hH'c.trans hHc.symm)
    subst hHH
    exact hit y hy
  intro b r hbr hB s hs0 hsr a ha y hy
  have hr0 : 0 < r := by linarith
  have hzc : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell hε η b
  have hbB : b ∈ interiorCellVertices ε η (ball (vertexPoint ε η b) r) := by
    refine ⟨⟨vertexPoint ε η b, hzc, mem_ball_self hr0⟩, ?_⟩
    rintro ⟨x, hx, hxf⟩
    rw [frontier_ball _ hr0.ne', mem_sphere] at hxf
    have := hdiam b ⟨_, hzc, hbr (mem_ball_self hr0)⟩ x hx _ hzc
    linarith
  have hp : 0 < p₀ * p₁ := mul_pos hp₀ hp₁
  have key : p₀ * p₁ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) a b ≤
      greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y b := by
    refine mul_greenKernel_le_of_separation hlf hcons hB hbB hp.le ?_
    rw [ENNReal.ofReal_mul hp₀.le]
    exact srwLaw_pairSep_lower_ball h hε H hlf hcons hHc hh hδ hδh hdiam hs₀ hs₁ hs₂ hs0 hsr hbr hItin' h311' hy ha
  calc greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) a b
      = (p₀ * p₁)⁻¹ * ((p₀ * p₁) * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) a b) := by
        field_simp
    _ ≤ (p₀ * p₁)⁻¹ * greenKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2))
        (interiorCellVertices ε η (ball (vertexPoint ε η b) r)) y b :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hp.le)

end GreenBall

end MatedCRT
