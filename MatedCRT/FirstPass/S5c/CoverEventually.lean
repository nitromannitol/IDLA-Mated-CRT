import MatedCRT.FirstPass.S5c.CoverCore

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: the filled discrete cluster eventually covers a compact core (B2 cover, pathwise)

Along a sequence of meshes `ε_k` (the deterministic subsequence of CHATGPT-5-1-B2-Ec15.md §1), if a compact set `K` lies in
`{surplus floor}` at one scale `s` with level `b > 0` (Floor.lean, eventually in the index), and the rescaled discrete least
supersolutions at the levels `t` and `s` are within `e_k → 0` of `κ w_t`, `κ w_s` uniformly on `K`, then `K` lies in the
filled discrete cluster for all large `k`. This is `mem_fillCells_of_floor` (CoverCore.lean) along the sequence: the
condition `e_k (1 + t/s) ≤ κ b/2` holds eventually because `e_k → 0`. Deterministic; the errors are the pathwise inputs
that the Borel-Cantelli step of SubseqBorelCantelli.lean supplies almost surely.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open _root_.HarmonicBalls

/-- **Eventual cover of a compact floor set** (B2, CHATGPT-5-1-B2-Ec15.md §1): see the module docstring. -/
theorem core_subset_fillCells_eventually {μ : Measure ℂ} {ρ t s κ b : ℝ} {K : Set ℂ}
    {ε mε : ℕ → ℝ} {η : ℕ → ℝ → ℂ} {m : ℕ → ℤ → ℤ → ℕ} {e : ℕ → ℝ}
    (hK : K ⊆ ball (0 : ℂ) ρ) (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b)
    (hfloor : ∀ x ∈ K, b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s))
    (he : Tendsto e atTop (𝓝 0))
    (hmε : ∀ᶠ k in atTop, 0 < mε k) (hε : ∀ᶠ k in atTop, 0 < ε k)
    (hEt : ∀ᶠ k in atTop, ∀ x ∈ K,
      |rescale (mε k) (ε k) (η k) (matedLeastSupersolution (m k) (ε k) (η k) ρ t) x -
        κ * leastSupersolution μ ρ 0 t x| ≤ e k)
    (hEs : ∀ᶠ k in atTop, ∀ x ∈ K,
      |rescale (mε k) (ε k) (η k) (matedLeastSupersolution (m k) (ε k) (η k) ρ s) x -
        κ * leastSupersolution μ ρ 0 s x| ≤ e k)
    (hmemcell : ∀ k, ∀ x ∈ K, x ∈ cell (ε k) (η k) (vertexOf (ε k) (η k) x)) :
    ∀ᶠ k in atTop, K ⊆ fillCells (ε k) (η k) (matedDiscreteCluster (m k) (ε k) (η k) ρ t) := by
  have hc0 : (0 : ℝ) < 1 + t / s := add_pos_of_pos_of_nonneg one_pos (div_nonneg ht.le hs.le)
  have hX : (0 : ℝ) < κ * b / 2 / (1 + t / s) := div_pos (div_pos (mul_pos hκ hb) two_pos) hc0
  have he' : ∀ᶠ k in atTop, e k * (1 + t / s) ≤ κ * b / 2 := by
    filter_upwards [he.eventually (gt_mem_nhds hX)] with k hk
    exact ((lt_div_iff₀ hc0).1 hk).le
  filter_upwards [hmε, hε, hEt, hEs, he'] with k hm hε' hEt' hEs' he''
  intro x hx
  exact mem_fillCells_of_floor (μ := μ) hm hε' ht hs hκ hb hK he'' hfloor hEt' hEs' (hmemcell k) hx

end MatedCRT.S5c
