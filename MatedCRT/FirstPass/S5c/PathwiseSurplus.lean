import MatedCRT.FirstPass.S5c.DepthBound
import MatedCRT.FirstPass.S5c.DepthCore

/-!
# FIRST PASS, Lemma 5.3: pathwise surplus bound on a good realization (G-5-3 Sections 2-3, eqs. (7)-(12))

On one realization and one mesh, with `L = Λ_t` (regular open, bounded, `Lᶜ` nonempty, `μ L = t`):
the filled discrete cluster `U = fillCells D` has `μ U ≤ t` (eq. (7)); if the compact core `K₁` of the harmonic ball lies in
`U` and has exterior mass `μ(L \ K₁) < τ` for a threshold `τ` of the quantitative eq. (9), then the exterior mass of `U`
is below `τ` (`μ(U \ L) ≤ μ(L \ U) ≤ μ(L \ K₁)`), so a depth vertex has a cell point in the depth core (eq. (10)), and the
floor on that core gives `c ε⁻¹ ≤ V_t(a)` with `c = κ b/(2 C_m)` (eqs. (11)-(12)). Deterministic: the random quantities
(the threshold `τ`, the floor `b`) enter only as hypotheses; their measurability is the open gate B1/B2 of reports/q3.md.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open scoped ENNReal
open _root_.HarmonicBalls

/-- **Pathwise surplus bound** (G-5-3, eqs. (7)-(12)): see the module docstring. -/
theorem surplus_bound_of_threshold {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {ρ t s mε κ e b Cm δ δ1 : ℝ} {τ : ℝ≥0∞} {L Q : Set ℂ} {a : ℤ}
    (hmε : 0 < mε) (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b) (hCm : 0 < Cm)
    (hCmε : 1 ≤ mε * ε * Cm) (he : e * (1 + t / s) ≤ κ * b / 2) (hδ : 0 < δ)
    (hL : interior (closure L) = L) (hLball : L ⊆ closedBall (0 : ℂ) ρ)
    (hμL : μ L = ENNReal.ofReal t)
    (hτ : ∀ U : Set ℂ, IsCompact U → U ⊆ Q → μ (U \ L) < τ → ∀ z ∈ U,
      3 * δ / 4 < infDist z (frontier U) → 3 * (3 * δ / 4) / 4 ≤ infDist z Lᶜ)
    (hU : IsCompact (fillCells ε η (matedDiscreteCluster m ε η ρ t)))
    (hUQ : fillCells ε η (matedDiscreteCluster m ε η ρ t) ⊆ Q)
    (hUmass : μ (fillCells ε η (matedDiscreteCluster m ε η ρ t)) ≤ ENNReal.ofReal t)
    (hcov : compactCore L ρ δ1 ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t))
    (hK1 : μ (L \ compactCore L ρ δ1) < τ)
    (haD : a ∈ matedDiscreteCluster m ε η ρ t) (hbdd : Bornology.IsBounded (cell ε η a))
    (hdiam : diam (cell ε η a) < δ / 4)
    (hdepth : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η (matedDiscreteCluster m ε η ρ t))))
    (hx : ∃ x ∈ cell ε η a, vertexOf ε η x = a)
    (hfloor : ∀ x ∈ compactCore L ρ δ, b ≤ leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 s x) / s))
    (hEt : ∀ x ∈ compactCore L ρ δ, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x -
      κ * leastSupersolution μ ρ 0 t x| ≤ e)
    (hEs : ∀ x ∈ compactCore L ρ δ, |rescale mε ε η (matedLeastSupersolution m ε η ρ s) x -
      κ * leastSupersolution μ ρ 0 s x| ≤ e) :
    κ * b / (2 * Cm) / ε ≤
      matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
  have hLo : IsOpen L := hL ▸ isOpen_interior
  set U := fillCells ε η (matedDiscreteCluster m ε η ρ t) with hUdef
  have hX : μ (L ∩ U) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by rw [← hμL]; exact measure_mono Set.inter_subset_left)
  have hsplit : μ (U \ L) ≤ μ (L \ U) := by
    have hadd : μ (U ∩ L) + μ (U \ L) = μ U := measure_inter_add_sdiff U hLo.measurableSet
    have hcover : μ L ≤ μ (L ∩ U) + μ (L \ U) := by
      calc μ L ≤ μ ((L ∩ U) ∪ (L \ U)) := by
            apply measure_mono
            intro x hx
            by_cases h : x ∈ U
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr ⟨hx, h⟩
        _ ≤ _ := measure_union_le _ _
    have hle : μ (L ∩ U) + μ (U \ L) ≤ μ (L ∩ U) + μ (L \ U) := by
      calc μ (L ∩ U) + μ (U \ L) = μ (U ∩ L) + μ (U \ L) := by rw [Set.inter_comm]
        _ = μ U := hadd
        _ ≤ μ L := by rw [hμL]; exact hUmass
        _ ≤ _ := hcover
    exact ENNReal.le_of_add_le_add_left hX hle
  have hsub : L \ U ⊆ L \ compactCore L ρ δ1 := fun x hx => ⟨hx.1, fun h => hx.2 (hcov h)⟩
  have hμU : μ (U \ L) < τ := lt_of_le_of_lt (hsplit.trans (measure_mono hsub)) hK1
  obtain ⟨x, hxK, hxcell, hxa⟩ :=
    exists_core_point_of_depth hδ hε hLball τ hτ hU hUQ hμU haD hbdd hdiam hdepth hx
  exact depth_bound_of_floor_and_errors (μ := μ) hmε hε ht hs hκ hb hCm hCmε he (fun y hy => hy.1)
    hfloor hEt hEs ⟨x, hxK, hxcell, hxa⟩

end MatedCRT.S5c
