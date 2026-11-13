import MatedCRT.FirstPass.Derived.HarnackPairUnionBound
import MatedCRT.FirstPass.Derived.HarnackRingBall
import MatedCRT.FirstPass.Derived.GreenKernelLowerOnCells

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


section PairGlue

open Filter Topology _root_.HarmonicBalls _root_.LatticeProb
open _root_.LatticeProb.LQG.LQGMeasureNonatomicMass

/-- If `r ≤ dist(x, ∂B_ρ)` then `|x| + r ≤ ρ` or `ρ + r ≤ |x|` (compare with the radial point `ρ x/|x|` of the
circle, or with `ρ` when `x = 0`). -/
private theorem norm_add_le_or_add_le_norm_of_le_infDist_sphere' {x : ℂ} {ρ r : ℝ} (hρ : 0 < ρ)
    (hr : r ≤ infDist x (sphere 0 ρ)) : ‖x‖ + r ≤ ρ ∨ ρ + r ≤ ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | h0
  · have hw : ((ρ : ℝ) : ℂ) ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    have h1 : infDist (0 : ℂ) (sphere 0 ρ) ≤ ρ := by
      calc infDist 0 (sphere 0 ρ) ≤ dist (0 : ℂ) (ρ : ℂ) := infDist_le_dist_of_mem hw
        _ = ρ := by rw [dist_comm, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    left
    rw [norm_zero]
    linarith
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    have hw : ((ρ / ‖x‖ : ℝ) : ℂ) * x ∈ sphere (0 : ℂ) ρ := by
      rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg hρ.le hxpos.le), div_mul_cancel₀ _ hxpos.ne']
    have e : (1 - ρ / ‖x‖) * ‖x‖ = ‖x‖ - ρ := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hxpos.ne']
    have h1 : infDist x (sphere 0 ρ) ≤ |‖x‖ - ρ| := by
      calc infDist x (sphere 0 ρ) ≤ dist x (((ρ / ‖x‖ : ℝ) : ℂ) * x) := infDist_le_dist_of_mem hw
        _ = |1 - ρ / ‖x‖| * ‖x‖ := by
          rw [dist_eq_norm, show x - ((ρ / ‖x‖ : ℝ) : ℂ) * x = ((1 - ρ / ‖x‖ : ℝ) : ℂ) * x by
            push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = |1 - ρ / ‖x‖| * |‖x‖| := by rw [abs_of_pos hxpos]
        _ = |‖x‖ - ρ| := by rw [← abs_mul, e]
    rcases le_total ‖x‖ ρ with h | h
    · left
      rw [abs_of_nonpos (sub_nonpos.2 h)] at h1
      linarith
    · right
      rw [abs_of_nonneg (sub_nonneg.2 h)] at h1
      linarith

/-- **The Harnack bound (4.13) for the Green kernel of `B_r(η(a))` from the pair events** (Berestycki–Gwynne 2020,
proof of Lemma 4.4, with the events (3.21) and (3.35) of Lemma 3.9 in place of the ring events of Lemma 3.10): the
hypothesis `hHarn` of `greenKernelLowerBoundStmt_of_inputs` from the cell size estimate and the per-circle failure
bounds `hPair` of the itinerary and disconnection events, with `β = min(β₀/2, (2+γ)^{-2}/2, α₀/14)` and
`C₁ = max(1, (p₀ p₁)⁻¹)`. -/
theorem hHarn_ball_of_pair {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hPair : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∀ y ∈ cellVertices ε (S.η ω) (sphere (vertexPoint ε (S.η ω) a) s),
        ∀ y' ∈ cellVertices ε (S.η ω) (sphere (vertexPoint ε (S.η ω) a) s),
          greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a y ≤
            C₁ * greenKernel (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)) a y'} := by
  intro γ hγ hγ2
  obtain ⟨β₀, α₀, hβ₀, hα₀, hpair⟩ := hPair γ hγ hγ2
  set e : ℝ := 1 / (2 + γ) ^ 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he, div_lt_one (by positivity)]
    nlinarith
  have h2e : 2 / (2 + γ) ^ 2 - e = e := by
    rw [he]
    ring
  set β : ℝ := min (β₀ / 2) (min (e / 2) (α₀ / 14)) with hβdef
  have hβ0 : 0 < β := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hββ₀ : 2 * β ≤ β₀ := by
    have : β ≤ β₀ / 2 := min_le_left _ _
    linarith
  have hβe : β ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβα : β ≤ α₀ / 14 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨β, hβ0, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨p₀, p₁, hp₀, hp₁, hpairp⟩ := hpair ((1 + ρ) / 2) (by linarith) (by linarith)
  refine ⟨max 1 (p₀ * p₁)⁻¹, le_max_left _ _, fun Ω _ S hS => ?_⟩
  obtain ⟨C, hC⟩ := hpairp Ω S hS
  have hU : Gauss.PolyHighProb S.P _ := polyHighProb_pairItin (P := S.P) S.bm S.η (ρ'' := (1 + ρ) / 2)
    (p₀ := p₀) (C := max C 0) hβ0 (by linarith) (le_max_right _ _)
    (fun ε hε hε1 z r hr hball => ((hC ε hε hε1).1 z r hr hball).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _))))
  have hV : Gauss.PolyHighProb S.P fun ε => {ω | PairL311Good ε (S.bm ω) (S.η ω) ((1 + ρ) / 2) (ε ^ β₀) p₁} :=
    ⟨α₀, hα₀, C, 1, one_pos, fun r hr hr1 => (hC r hr hr1).2⟩
  have hsz : Gauss.PolyHighProb S.P _ :=
    hsize γ hγ hγ2 e ((1 + ρ) / 2) he0 he1 (by linarith) (by linarith) Ω S hS
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | HarnackQual S ω ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)} := by
    filter_upwards [hS.ae_harnack_inputs hγ hγ2, hS.ae_tendsto_cocompact] with ω h1 h2
    exact ⟨h1, h2⟩
  have h2 := polyHighProb_inter_ae (polyHighProb_inter (polyHighProb_inter hU hV) hsz) hW
  obtain ⟨r₁, hr₁, hr₁t⟩ := exists_rpow_le_of_small hβ0 (show (0 : ℝ) < 1 / 300 by norm_num)
  refine polyHighProb_mono_of_eventually h2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r₁ 1 from lt_min hr₁ one_pos)] with ε hε
  rintro ω ⟨⟨⟨hUω, hVω⟩, hSzω⟩, ⟨hηc, hall⟩, hprop⟩
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hεr : ε < r₁ := lt_of_lt_of_le hε.2 (min_le_left _ _)
  obtain ⟨hlf, hcons, -, -⟩ := hall ε hε0
  have ht : ε ^ β ≤ 1 / 300 := hr₁t ε hε0 hεr
  have ht0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have ht2 : ε ^ (2 * β) = (ε ^ β) ^ 2 := by
    rw [show 2 * β = β * 2 by ring, Real.rpow_mul hε0.le, Real.rpow_two]
  have hδ : ε ^ e ≤ (ε ^ β) ^ 2 := by
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
  have hβ₀le : ε ^ β₀ ≤ (ε ^ β) ^ 2 := by
    rw [← ht2]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hββ₀
  have hh0 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  have hsq : (ε ^ β) ^ 2 ≤ ε ^ β / 300 := by nlinarith
  have hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε (S.η ω) k) := fun k =>
    (isCompact_Icc.image hηc).isBounded
  have hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball (0 : ℂ) ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε (S.η ω) k, ∀ x' ∈ cell ε (S.η ω) k, dist x x' ≤ ε ^ e := by
    intro k hk x hx x' hx'
    have hd := (hSzω k hk).2
    rw [h2e] at hd
    exact (Metric.dist_le_diam_of_mem (hbdd k) hx hx').trans hd
  have hG := greenKernel_le_inv_mul_of_pairEvents_ball (ρ := ρ) (δ := ε ^ e) (h₀ := ε ^ (2 * β))
    (s₀ := ε ^ β) (s₁ := ε ^ β₀) (s₂ := ε ^ β₀) (p₀ := p₀) (p₁ := p₁) hε0.le (ω := S.bm ω) (η := S.η ω)
    hlf hcons hh0 (Real.rpow_pos_of_pos hε0 _).le (by rw [ht2]; exact hδ) hdiam (by rw [ht2]; nlinarith)
    (by rw [ht2]; nlinarith) (by nlinarith) hp₀ hp₁
    (fun m' n' l hl hball => hUω (m', n', l)
      (mem_latticeTripleBox hh0 (Real.rpow_pos_of_pos hε0 _) (by linarith) ⟨hl, hball⟩) ⟨hl, hball⟩) hVω
  intro a ha r hr s hs hsr y hy y' hy'
  have hs0 : 0 < s := lt_of_lt_of_le ht0 hs
  have hBfin : (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).Finite :=
    (cellVertices_finite_of_isCompact hηc hprop hε0
      (isCompact_closedBall (vertexPoint ε (S.η ω) a) r)).subset fun k hk => by
        obtain ⟨x, hx1, hx2⟩ := interiorCellVertices_subset _ _ _ hk
        exact ⟨x, hx1, ball_subset_closedBall hx2⟩
  obtain ⟨x₀, hx₀c, hx₀b⟩ := ha
  have h5 : ‖x₀‖ < ρ := mem_ball_zero_iff.1 hx₀b
  have hva : ‖vertexPoint ε (S.η ω) a‖ ≤ ρ + ε ^ e := by
    have h3 := norm_sub_norm_le (vertexPoint ε (S.η ω) a) x₀
    rw [← dist_eq_norm] at h3
    have h4 := hdiam a ⟨x₀, hx₀c, ball_subset_ball (by linarith : ρ ≤ (1 + ρ) / 2) hx₀b⟩ _
      (vertexPoint_mem_cell hε0.le _ a) _ hx₀c
    linarith
  have hnr : ‖vertexPoint ε (S.η ω) a‖ + r ≤ ρ := by
    rcases norm_add_le_or_add_le_norm_of_le_infDist_sphere' hρ hr with h1 | h1
    · exact h1
    · exfalso
      linarith
  have hbr : ball (vertexPoint ε (S.η ω) a) r ⊆ ball (0 : ℂ) ((1 + ρ) / 2) := by
    intro q hq
    rw [mem_ball] at hq
    rw [mem_ball_zero_iff]
    have h1 := norm_sub_norm_le q (vertexPoint ε (S.η ω) a)
    rw [← dist_eq_norm] at h1
    linarith
  rw [← frontier_ball (vertexPoint ε (S.η ω) a) hs0.ne'] at hy hy'
  have key := hG a r hbr hBfin s hs (by linarith) y hy y' hy'
  rw [greenKernel_symm_pole (S.mult_symm ε ω) hlf hcons hBfin a y,
    greenKernel_symm_pole (S.mult_symm ε ω) hlf hcons hBfin a y']
  exact key.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (greenKernel_nonneg_pole _ _ _ _))

/-- **Lemma 2.16** (Berestycki–Gwynne 2020, Lemma 4.4) from the cell size estimate, the pair events of ibid.
Lemma 3.9 (`hPair`: the itinerary events (3.21) and the disconnection events (3.35) of Lemma 3.11, giving the
Harnack bound (4.13) by `hHarn_ball_of_pair`) and the resistance bound (4.15) for the annuli
`B_{3r/4}(η(a)) \ B̄_s(η(a))` (`hres`). -/
theorem greenKernelLowerBoundStmt_of_pair {𝒮 : SpaceFillingSLEModel} (hsize : CellSizeEstimateStmt 𝒮)
    (hPair : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ z : ℂ, ∀ r : ℝ, ε ^ β₀ ≤ r → ball z (2 * r) ⊆ ball (0 : ℂ) ρ' →
          S.P {ω | ¬ PairItinGood ε (S.bm ω) (S.η ω) p₀ z r} ≤ ENNReal.ofReal (C * ε ^ α₀)) ∧
        S.P {ω | ¬ PairL311Good ε (S.bm ω) (S.η ω) ρ' (ε ^ β₀) p₁} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hres : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S.η ω) (closedBall (vertexPoint ε (S.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂}) :
    GreenKernelLowerBoundStmt 𝒮 :=
  greenKernelLowerBoundStmt_of_inputs hsize (hHarn_ball_of_pair hsize hPair) hres

end PairGlue

end MatedCRT
