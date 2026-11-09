import MatedCRT.FirstPass.S5c.PathwiseSurplus

/-!
# FIRST PASS, Lemma 5.3 (B2 outcome): the pathwise surplus bound holds eventually along the mesh sequence

Along a mesh sequence `ε_k → 0` (the B2 subsequence), the pathwise surplus bound `surplus_bound_of_threshold`
(PathwiseSurplus.lean:22) holds for every depth vertex of the discrete cluster, for all large `k`. The fixed hypotheses are the
continuum data `L = Λ_t`, `Q`, `δ`, `δ1`, the threshold `τ` of the mass-threshold lemma and the floor `b` at one scale `s`. The
mesh-dependent hypotheses of the pathwise bound are supplied eventually in `k`: the mesh scalings (MeshScale.lean), the error
bound `e_k (1 + t/s) ≤ κ b/2` and the errors (B2Bad.lean), the mass bound (eq. (7)), the cover of the compact core
(CoverEventually.lean), the cell diameters (B2Bad.lean). The per-vertex facts `bounded cell` and the existence of a cell point
with smallest vertex `a` (`exists_vertexOf_eq_of_area_parametrized`) are stated for all `k`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open _root_.HarmonicBalls

/-- **Eventual pathwise surplus bound** (B2 outcome): see the module docstring. -/
theorem surplus_eventually_of_threshold {μ : Measure ℂ} {L Q : Set ℂ} {ρ t s κ b Cm δ δ1 : ℝ} {τ : ℝ≥0∞}
    {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ} {e : ℕ → ℝ}
    (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b) (hCm : 0 < Cm) (hδ : 0 < δ)
    (hL : interior (closure L) = L) (hLball : L ⊆ closedBall (0 : ℂ) ρ) (hμL : μ L = ENNReal.ofReal t)
    (hτ : ∀ U : Set ℂ, IsCompact U → U ⊆ Q → μ (U \ L) < τ → ∀ z ∈ U,
      3 * δ / 4 < infDist z (frontier U) → 3 * (3 * δ / 4) / 4 ≤ infDist z Lᶜ)
    (hK1 : μ (L \ compactCore L ρ δ1) < τ)
    (hfloor : ∀ x ∈ compactCore L ρ δ,
      b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s))
    (hbdd : ∀ (k : ℕ) (a : ℤ), Bornology.IsBounded (cell (ε k) η a))
    (hx : ∀ (k : ℕ) (a : ℤ), ∃ x ∈ cell (ε k) η a, vertexOf (ε k) η x = a)
    (hmε : ∀ᶠ k in atTop, 0 < mε k) (hε : ∀ᶠ k in atTop, 0 < ε k)
    (hCmε : ∀ᶠ k in atTop, 1 ≤ mε k * ε k * Cm)
    (he : ∀ᶠ k in atTop, e k * (1 + t / s) ≤ κ * b / 2)
    (hU : ∀ᶠ k in atTop, IsCompact (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t)))
    (hUQ : ∀ᶠ k in atTop, fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t) ⊆ Q)
    (hUmass : ∀ᶠ k in atTop, μ (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t)) ≤ ENNReal.ofReal t)
    (hcov : ∀ᶠ k in atTop, compactCore L ρ δ1 ⊆ fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t))
    (hdiam : ∀ᶠ k in atTop, ∀ a ∈ matedDiscreteCluster (m k) (ε k) η ρ t, diam (cell (ε k) η a) < δ / 4)
    (hEt : ∀ᶠ k in atTop, ∀ x ∈ compactCore L ρ δ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ t) x -
        κ * leastSupersolution μ ρ 0 t x| ≤ e k)
    (hEs : ∀ᶠ k in atTop, ∀ x ∈ compactCore L ρ δ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ s) x -
        κ * leastSupersolution μ ρ 0 s x| ≤ e k) :
    ∀ᶠ k in atTop, ∀ a ∈ matedDiscreteCluster (m k) (ε k) η ρ t,
      δ < infDist (vertexPoint (ε k) η a) (frontier (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t))) →
      κ * b / (2 * Cm) / ε k ≤
        matedLeastSupersolution (m k) (ε k) η ρ t a + t / ε k * greenKernel (m k) (ballInterior (ε k) η ρ) 0 a := by
  filter_upwards [hmε, hε, hCmε, he, hU, hUQ, hUmass, hcov, hEt, hEs, hdiam] with k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  intro a ha hdep
  exact surplus_bound_of_threshold h1 h2 ht hs hκ hb hCm h3 h4 hδ hL hLball hμL hτ h5 h6 h7 h8 hK1 ha
    (hbdd k a) (h11 a ha) hdep (hx k a) hfloor h9 h10

end MatedCRT.S5c
