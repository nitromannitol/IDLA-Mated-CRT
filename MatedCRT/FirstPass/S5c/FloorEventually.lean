import MatedCRT.FirstPass.S5c.FloorMono

/-!
# FIRST PASS, Lemma 5.3: the surplus floor holds eventually in the scale index (B1c, deterministic)

Floor.lean (`surplus_floor_on_compact`) gives, for a compact set `K ⊆ Λ_t`, some index `n` and a level `b > 0` with
`b ≤ w_t + t(-w_{s_n}/s_n)` on `K`. FloorMono.lean shows that this floor term is nondecreasing in the index `n`, so the
same bound holds at every later index, uniformly on `K`. Hence the floor holds eventually in the scale index, with no Dini
argument and no separate treatment of the pole: the pole is inside the existential floor already. This closes the
index-selection gap of B1c (reports/q3.md); the random-index measurability is a separate step.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology HarmonicBalls

/-- **Eventual floor** (B1c, deterministic): a floor at one index `n` on `K` persists at every index `m ≥ n`, uniformly on `K`. -/
theorem floor_eventually_of_exists {μ : Measure ℂ} {ρ t : ℝ} (ht : 0 < t) {K : Set ℂ} {b : ℝ} {n : ℕ}
    (hb : ∀ x ∈ K, ∀ τ : ℝ, 0 ≤ τ → BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ ρ 0 τ))
    (hn : ∀ x ∈ K, b ≤ leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) / (t * (1 / 2) ^ n))) :
    ∀ᶠ m in atTop, ∀ x ∈ K, b ≤ leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ m) x) / (t * (1 / 2) ^ m)) := by
  filter_upwards [eventually_ge_atTop n] with m hm x hx
  exact (hn x hx).trans (floorTerm_monotone ht x (hb x hx) hm)

end MatedCRT.S5c
