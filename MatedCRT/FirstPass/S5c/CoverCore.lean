import MatedCRT.FirstPass.S5c.DiscreteSix

/-!
# FIRST PASS, Lemma 5.3: the compact core is covered by the discrete cluster (G-5-3 Section 2, eq. (8) input)

On one realization and one mesh: if the continuum floor is at least `b > 0` on a set `K ⊆ B_ρ` and the rescaled discrete
least supersolutions at masses `t` and `s` are within `e` of `κ w_t`, `κ w_s` on `K` with `e (1 + t/s) ≤ κ b / 2`, then every
point `x ∈ K` lies in the filled discrete cluster `fillCells ε η (matedDiscreteCluster ...)`. The point `x` lies in the cell
of its own vertex `vertexOf x` (the cell-representative fact, hypothesis `hmemcell`), and the discrete surplus there is
positive, so the vertex belongs to the discrete cluster. Deterministic.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- **Compact cores lie in the filled cluster** (G-5-3 Section 2): see the module docstring. -/
theorem mem_fillCells_of_floor {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {ρ t s mε κ e b : ℝ} {K : Set ℂ}
    (hmε : 0 < mε) (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b)
    (hK : K ⊆ ball (0 : ℂ) ρ) (he : e * (1 + t / s) ≤ κ * b / 2)
    (hfloor : ∀ x ∈ K, b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s))
    (hEt : ∀ x ∈ K, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - κ * leastSupersolution μ ρ 0 t x| ≤ e)
    (hEs : ∀ x ∈ K, |rescale mε ε η (matedLeastSupersolution m ε η ρ s) x - κ * leastSupersolution μ ρ 0 s x| ≤ e)
    (hmemcell : ∀ x ∈ K, x ∈ cell ε η (vertexOf ε η x)) {x : ℂ} (hxK : x ∈ K) :
    x ∈ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  have hxcell := hmemcell x hxK
  have hW : vertexOf ε η x ∈ cellVertices ε η (closedBall 0 ρ) :=
    ⟨x, hxcell, ball_subset_closedBall (hK hxK)⟩
  have key := surplus_div_ge_of_rescaled_errors (μ := μ) (m := m) (ρ := ρ) (t := t) (s := s) hmε hε ht hs
    hW (hEt x hxK) (hEs x hxK)
  have hfl := hfloor x hxK
  have hkb : κ * b ≤ κ * (leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s)) :=
    mul_le_mul_of_nonneg_left hfl hκ.le
  have hkbpos : 0 < κ * b / 2 := half_pos (mul_pos hκ hb)
  have hpos : 0 < (matedLeastSupersolution m ε η ρ t (vertexOf ε η x) +
      t / ε * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x)) / mε := by
    linarith
  have hV : 0 < matedLeastSupersolution m ε η ρ t (vertexOf ε η x) +
      t / ε * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x) :=
    (div_pos_iff_of_pos_right hmε).mp hpos
  have haD : vertexOf ε η x ∈ matedDiscreteCluster m ε η ρ t := by
    show vertexOf ε η x ∈ cellVertices ε η (ball 0 ρ) ∧
      matedObstacle m ε η ρ t (vertexOf ε η x) < matedLeastSupersolution m ε η ρ t (vertexOf ε η x)
    refine ⟨⟨x, hxcell, hK hxK⟩, ?_⟩
    unfold matedObstacle
    linarith
  exact mem_iUnion₂.2 ⟨vertexOf ε η x, haD, hxcell⟩

end MatedCRT.S5c
