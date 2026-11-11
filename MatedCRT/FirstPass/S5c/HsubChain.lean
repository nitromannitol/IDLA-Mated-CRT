import MatedCRT.FirstPass.S5c.SurplusEventually
import MatedCRT.FirstPass.S5c.CoverEventually
import MatedCRT.FirstPass.S5c.MassThreshold
import MatedCRT.FirstPass.S5c.ExteriorMass

/-!
# Outcome chain for `MeanValueSurplusLowerStep`

Deterministic chain at one outcome.
* The final floor `b0` is taken at the fixed target depth `δ` (Step 9); only `b0` enters the output constant.
* The auxiliary cover uses margins `bj j` at the deterministic depths `coverDepth j = 1/(j+1)` (Steps 2, 6).
* The auxiliary depth index `n` is chosen pathwise from the mass threshold (Steps 4-5); it is an ordinary
  natural number inside the outcome proof, so no measurable choice of depth is needed.
* The mass threshold is `exists_mass_threshold_of_deep_points` at depth `3δ/4`, which gives the
  engine's `hτ` (Step 4).
The engine is `surplus_eventually_of_threshold` (SurplusEventually.lean); the cover is
`core_subset_fillCells_eventually` (CoverEventually.lean).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open _root_.HarmonicBalls

/-- The deterministic auxiliary depths `d_j = 1/(j+1)` used for the cover (route note Steps 2 and 5). -/
noncomputable def coverDepth (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma coverDepth_pos (j : ℕ) : 0 < coverDepth j := by
  unfold coverDepth
  positivity

/-- **Outcome chain (deterministic).** At one outcome `ω`, with `L = Λ_t(ω)`, `μ = S.μ ω`, `s = t/2`:
the target floor `b0` on `compactCore L ρ δ`, the cover floors `bj j` on `compactCore L ρ (coverDepth j)`,
and the engine's eventual cell and convergence hypotheses give the surplus bound on the deep cluster points
with constant `κ * b0 / (2 * Cm)`. The auxiliary index is chosen pathwise (Step 5). -/
theorem hsub_outcome
    {μ : Measure ℂ} {L : Set ℂ} {ρ t δ κ Cm b0 : ℝ} {bj e : ℕ → ℝ}
    {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {η : ℝ → ℂ}
    (ht : 0 < t) (hκ : 0 < κ) (hCm : 0 < Cm) (hδ : 0 < δ) (hb0 : 0 < b0) (hbj : ∀ j, 0 < bj j)
    (hL : interior (closure L) = L) (hLc : Lᶜ.Nonempty) (hLball : L ⊆ ball (0 : ℂ) ρ)
    (hμL : μ L = ENNReal.ofReal t)
    (hfull : ∀ x : ℂ, ∀ r : ℝ, 0 < r → 0 < μ (ball x r))
    (hfloor0 : ∀ x ∈ compactCore L ρ δ,
      b0 ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 (t / 2) x) / (t / 2)))
    (hfloorj : ∀ j : ℕ, ∀ x ∈ compactCore L ρ (coverDepth j),
      bj j ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 (t / 2) x) / (t / 2)))
    (hEt : ∀ᶠ k in atTop, ∀ x ∈ ball (0 : ℂ) ρ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ t) x -
        κ * leastSupersolution μ ρ 0 t x| ≤ e k)
    (hEs : ∀ᶠ k in atTop, ∀ x ∈ ball (0 : ℂ) ρ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ (t / 2)) x -
        κ * leastSupersolution μ ρ 0 (t / 2) x| ≤ e k)
    (he : Tendsto e atTop (𝓝 0))
    (hbdd : ∀ (k : ℕ) (a : ℤ), Bornology.IsBounded (cell (ε k) η a))
    (hx : ∀ (k : ℕ) (a : ℤ), ∃ x ∈ cell (ε k) η a, vertexOf (ε k) η x = a)
    (hmε : ∀ᶠ k in atTop, 0 < mε k) (hε : ∀ᶠ k in atTop, 0 < ε k)
    (hCmε : ∀ᶠ k in atTop, 1 ≤ mε k * ε k * Cm)
    (hU : ∀ᶠ k in atTop, IsCompact (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t)))
    (hUQ : ∀ᶠ k in atTop,
      fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t) ⊆ closedBall (0 : ℂ) (ρ + 1))
    (hUmass : ∀ᶠ k in atTop,
      μ (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t)) ≤ ENNReal.ofReal t)
    (hmemcell : ∀ᶠ k in atTop, ∀ x ∈ L, x ∈ cell (ε k) η (vertexOf (ε k) η x))
    (hdiam : ∀ᶠ k in atTop, ∀ a ∈ matedDiscreteCluster (m k) (ε k) η ρ t,
      diam (cell (ε k) η a) < δ / 4) :
    ∀ᶠ k in atTop, ∀ a ∈ matedDiscreteCluster (m k) (ε k) η ρ t,
      δ < infDist (vertexPoint (ε k) η a)
        (frontier (fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t))) →
      κ * b0 / (2 * Cm) / ε k ≤
        matedLeastSupersolution (m k) (ε k) η ρ t a +
          t / ε k * greenKernel (m k) (ballInterior (ε k) η ρ) 0 a := by
  classical
  have hs : (0 : ℝ) < t / 2 := by positivity
  have hLopen : IsOpen L := by
    rw [← hL]
    exact isOpen_interior
  have hLball' : L ⊆ closedBall (0 : ℂ) ρ := hLball.trans ball_subset_closedBall
  have hμne : μ L ≠ ⊤ := by
    rw [hμL]
    exact ENNReal.ofReal_ne_top
  -- Step 4: mass threshold at depth 3δ/4 (gives the engine's hτ with 3(3δ/4)/4 = 9δ/16).
  obtain ⟨τ, hτ0, hτ⟩ := exists_mass_threshold_of_deep_points (μ := μ) (L := L)
    (Q := closedBall (0 : ℂ) (ρ + 1)) (δ := 3 * δ / 4) (by positivity) hL hLc
    (isCompact_closedBall (0 : ℂ) (ρ + 1)) hfull
  -- Step 5: a pathwise auxiliary depth index with small excess mass.
  have hT := measure_core_compl_tendsto (μ := μ) hLopen hLc hLball' hμne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, μ (L \ compactCore L ρ (coverDepth n)) < τ :=
    ((tendsto_order.1 hT).2 τ hτ0).exists
  -- Step 6: the auxiliary cover with the margin bj n.
  have hKL : compactCore L ρ (coverDepth n) ⊆ L := compactCore_subset (coverDepth_pos n)
  have hKball : compactCore L ρ (coverDepth n) ⊆ ball (0 : ℂ) ρ := hKL.trans hLball
  have hcov : ∀ᶠ k in atTop,
      compactCore L ρ (coverDepth n) ⊆
        fillCells (ε k) η (matedDiscreteCluster (m k) (ε k) η ρ t) :=
    core_subset_fillCells_eventually (μ := μ) (K := compactCore L ρ (coverDepth n)) (ρ := ρ)
      (t := t) (s := t / 2) (κ := κ) (b := bj n) (ε := ε) (mε := mε) (η := fun _ => η)
      (m := m) (e := e) hKball ht hs hκ (hbj n) (hfloorj n) he hmε hε
      (by
        filter_upwards [hEt] with k hk
        intro x hx
        exact hk x (hKball hx))
      (by
        filter_upwards [hEs] with k hk
        intro x hx
        exact hk x (hKball hx))
      (by
        filter_upwards [hmemcell] with k hk
        intro x hx
        exact hk x (hKL hx))
  -- Target floor and the engine's remaining hypotheses.
  have hcompact_ball : compactCore L ρ δ ⊆ ball (0 : ℂ) ρ := (compactCore_subset hδ).trans hLball
  have hEtδ : ∀ᶠ k in atTop, ∀ x ∈ compactCore L ρ δ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ t) x -
        κ * leastSupersolution μ ρ 0 t x| ≤ e k := by
    filter_upwards [hEt] with k hk
    intro x hx
    exact hk x (hcompact_ball hx)
  have hEsδ : ∀ᶠ k in atTop, ∀ x ∈ compactCore L ρ δ,
      |rescale (mε k) (ε k) η (matedLeastSupersolution (m k) (ε k) η ρ (t / 2)) x -
        κ * leastSupersolution μ ρ 0 (t / 2) x| ≤ e k := by
    filter_upwards [hEs] with k hk
    intro x hx
    exact hk x (hcompact_ball hx)
  have hb0e : ∀ᶠ k in atTop, e k * (1 + t / (t / 2)) ≤ κ * b0 / 2 := by
    have hc : (0 : ℝ) < 1 + t / (t / 2) := by positivity
    have hX : (0 : ℝ) < κ * b0 / 2 / (1 + t / (t / 2)) := by positivity
    filter_upwards [he.eventually (gt_mem_nhds hX)] with k hk
    exact ((lt_div_iff₀ hc).1 hk).le
  -- Step 9: the engine applied with the target floor b0 and the auxiliary depth δ1 = d n.
  exact surplus_eventually_of_threshold (μ := μ) (L := L) (Q := closedBall (0 : ℂ) (ρ + 1))
    (ρ := ρ) (t := t) (s := t / 2) (κ := κ) (b := b0) (Cm := Cm) (δ := δ)
    (δ1 := coverDepth n) (τ := τ) (m := m) (ε := ε) (mε := mε) (η := η) (e := e)
    ht hs hκ hb0 hCm hδ hL hLball' hμL hτ hn hfloor0 hbdd hx hmε hε hCmε hb0e hU hUQ hUmass
    hcov hdiam hEtδ hEsδ

end MatedCRT.S5c
