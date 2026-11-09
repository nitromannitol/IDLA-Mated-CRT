import MatedCRT.FirstPass.S5c.DepthBound
import MatedCRT.FirstPass.S5c.DepthCore

/-!
# FIRST PASS, 5.1 stopped clause: the interior estimate on `V^ε(Λ_t)` (E-c1-5; StoppedSurplusInteriorStep)

The interior step of `Proofs/Sec5/StoppedSurplusSteps.lean` asks for `c ε⁻¹ ≤ w̃^ε_t(a) + (t ε⁻¹) g^ε_{B_ρ}(0, a)` for
`a ∈ V^ε(Λ_t) = cellVertices (Λ_t)` at `δ`-depth from the frontier of `fillCells (V^ε(Λ_t))`. Pathwise this is the depth
argument of `PathwiseSurplus.lean` with the discrete cluster replaced by `V^ε(Λ_t)`: the depth-to-core step needs only the
exterior mass of `fillCells (V^ε(Λ_t))` relative to `Λ_t` to be below the threshold `τ` (no cover by the surplus is needed).
That exterior mass is bounded by the thickening of `Λ_t` at the maximal cell diameter minus `Λ_t`, which vanishes as the
radius decreases because `μ (frontier Λ_t) = 0` (`SatisfiesHarmonicBallConditions.measure_frontier`). Deterministic.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open _root_.HarmonicBalls

/-- **Stopped interior bound, pathwise** (E-c1-5; `StoppedSurplusInteriorStep`): the depth vertices of `V^ε(Λ_t)` satisfy
`c ε⁻¹ ≤ V_t(a)` with `c = κ b / (2 C_m)`, given the exterior-mass threshold of the filled stopped cluster. -/
theorem stopped_interior_bound_of_threshold {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {ρ t s mε κ e b Cm δ : ℝ} {τ : ℝ≥0∞} {L Q : Set ℂ} {a : ℤ}
    (hmε : 0 < mε) (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b) (hCm : 0 < Cm)
    (hCmε : 1 ≤ mε * ε * Cm) (he : e * (1 + t / s) ≤ κ * b / 2) (hδ : 0 < δ)
    (hLball : L ⊆ closedBall (0 : ℂ) ρ)
    (hτ : ∀ U : Set ℂ, IsCompact U → U ⊆ Q → μ (U \ L) < τ → ∀ z ∈ U,
      3 * δ / 4 < infDist z (frontier U) → 3 * (3 * δ / 4) / 4 ≤ infDist z Lᶜ)
    (hU : IsCompact (fillCells ε η (cellVertices ε η L)))
    (hUQ : fillCells ε η (cellVertices ε η L) ⊆ Q)
    (hμU : μ (fillCells ε η (cellVertices ε η L) \ L) < τ)
    (haA : a ∈ cellVertices ε η L) (hbdd : Bornology.IsBounded (cell ε η a))
    (hdiam : diam (cell ε η a) < δ / 4)
    (hdepth : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η (cellVertices ε η L))))
    (hx : ∃ x ∈ cell ε η a, vertexOf ε η x = a)
    (hfloor : ∀ x ∈ compactCore L ρ δ, b ≤ leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 s x) / s))
    (hEt : ∀ x ∈ compactCore L ρ δ, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x -
      κ * leastSupersolution μ ρ 0 t x| ≤ e)
    (hEs : ∀ x ∈ compactCore L ρ δ, |rescale mε ε η (matedLeastSupersolution m ε η ρ s) x -
      κ * leastSupersolution μ ρ 0 s x| ≤ e) :
    κ * b / (2 * Cm) / ε ≤
      matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
  obtain ⟨x, hxK, hxcell, hxa⟩ :=
    exists_core_point_of_depth hδ hε hLball τ hτ hU hUQ hμU haA hbdd hdiam hdepth hx
  exact depth_bound_of_floor_and_errors (μ := μ) hmε hε ht hs hκ hb hCm hCmε he (fun y hy => hy.1)
    hfloor hEt hEs ⟨x, hxK, hxcell, hxa⟩

/-- **Cells meeting `Λ` lie in its thickening** (boundary layer): if every cell meeting `L` has diameter below `r`, the
exterior part of the filled cluster `fillCells (cellVertices L)` lies in the `r`-thickening of `L` minus `L`. -/
theorem fillCells_cellVertices_sdiff_subset {ε : ℝ} {η : ℝ → ℂ} {L : Set ℂ} {r : ℝ}
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ L).Nonempty → diam (cell ε η k) < r)
    (hbdd : ∀ k : ℤ, (cell ε η k ∩ L).Nonempty → Bornology.IsBounded (cell ε η k)) :
    fillCells ε η (cellVertices ε η L) \ L ⊆ thickening r L \ L := by
  rintro x ⟨hx, hxL⟩
  obtain ⟨k, hkmem, hxk⟩ := mem_iUnion₂.1 hx
  obtain ⟨y, hyk, hyL⟩ := hkmem
  refine ⟨?_, hxL⟩
  rw [mem_thickening_iff]
  exact ⟨y, hyL, lt_of_le_of_lt (dist_le_diam_of_mem (hbdd k ⟨y, hyk, hyL⟩) hxk hyk)
    (hdiam k ⟨y, hyk, hyL⟩)⟩

/-- **Boundary layer vanishes** (G-stopped boundary layer, measure part): for an open `L` of finite measure with
`μ (frontier L) = 0`, the exterior thickening mass `μ (thickening r L \ L)` tends to zero as `r ↓ 0`. -/
theorem tendsto_measure_thickening_sdiff {μ : Measure ℂ} {L : Set ℂ} (hLo : IsOpen L)
    (hfr : μ (frontier L) = 0) (hfin : μ (thickening 1 L) ≠ ⊤) :
    Tendsto (fun r => μ (thickening r L \ L)) (𝓝[>] 0) (𝓝 0) := by
  have hLfin : μ L ≠ ⊤ := ne_top_of_le_ne_top hfin
    (measure_mono (self_subset_thickening zero_lt_one L))
  have hsplit : closure L = L ∪ frontier L := by
    rw [hLo.frontier_eq, union_sdiff_cancel subset_closure]
  have hcl : μ (closure L) = μ L := by
    apply le_antisymm
    · calc μ (closure L) = μ (L ∪ frontier L) := by rw [hsplit]
        _ ≤ μ L + μ (frontier L) := measure_union_le _ _
        _ = μ L := by rw [hfr, add_zero]
    · exact measure_mono subset_closure
  have hfinC : ∃ R : ℝ, 0 < R ∧ μ (thickening R (closure L)) ≠ ⊤ :=
    ⟨1, one_pos, by rwa [thickening_closure]⟩
  have hT := tendsto_measure_thickening_of_isClosed hfinC isClosed_closure
  simp only [thickening_closure] at hT
  rw [hcl] at hT
  have hT' : Tendsto (fun r => μ (thickening r L) - μ L) (𝓝[>] 0) (𝓝 (μ L - μ L)) :=
    ENNReal.Tendsto.sub hT tendsto_const_nhds (Or.inl hLfin)
  rw [tsub_self] at hT'
  refine Tendsto.congr' ?_ hT'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  exact (measure_sdiff (self_subset_thickening hr' L) hLo.measurableSet.nullMeasurableSet hLfin).symm

end MatedCRT.S5c
