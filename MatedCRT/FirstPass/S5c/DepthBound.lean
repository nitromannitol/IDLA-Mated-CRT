import MatedCRT.FirstPass.S5c.DiscreteSix

/-!
# FIRST PASS, Lemma 5.3: pathwise depth bound (G-5-3 Section 1 and eqs. (10)-(12))

On one realization and one mesh `ε`: if the continuum floor `A_n = w_t + t R_n` is at least `b > 0` on a compact set
`K` of the disk, and the rescaled discrete least supersolutions at masses `t` and `s` are within `e` of `κ w_t` and
`κ w_s` on `K` (uniform convergence), with `e (1 + t/s) ≤ κ b / 2`, then every vertex `a` of the cluster having a cell
point `x ∈ K` with `vertexOf x = a` satisfies `c ε⁻¹ ≤ V_t(a)` with `c = κ b / (2 C_m)`, provided `ε m_ε C_m ≥ 1`
(`MepsScalingInput`, External/SLE.lean:63). Deterministic: the probabilistic assembly is the remaining S5 step.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- **Pathwise depth bound** (G-5-3 eqs. (10)-(12)). -/
theorem depth_bound_of_floor_and_errors {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ}
    {ρ t s mε κ e b Cm : ℝ} {K : Set ℂ} {a : ℤ}
    (hmε : 0 < mε) (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) (hκ : 0 < κ) (hb : 0 < b) (hCm : 0 < Cm)
    (hCmε : 1 ≤ mε * ε * Cm) (he : e * (1 + t / s) ≤ κ * b / 2)
    (hK : K ⊆ closedBall 0 ρ)
    (hfloor : ∀ x ∈ K, b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s))
    (hEt : ∀ x ∈ K, |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - κ * leastSupersolution μ ρ 0 t x| ≤ e)
    (hEs : ∀ x ∈ K, |rescale mε ε η (matedLeastSupersolution m ε η ρ s) x - κ * leastSupersolution μ ρ 0 s x| ≤ e)
    (haK : ∃ x ∈ K, x ∈ cell ε η a ∧ vertexOf ε η x = a) :
    κ * b / (2 * Cm) / ε ≤
      matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
  obtain ⟨x, hxK, hxcell, hxa⟩ := haK
  have hA : a ∈ cellVertices ε η (closedBall 0 ρ) := ⟨x, hxcell, hK hxK⟩
  have key := surplus_div_ge_of_rescaled_errors (μ := μ) (m := m) (ρ := ρ) (t := t) (s := s) hmε hε ht hs
    (x := x) (by rw [hxa]; exact hA) (hEt x hxK) (hEs x hxK)
  rw [hxa] at key
  have hfl := hfloor x hxK
  have h1 : κ * b ≤ κ * (leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s)) :=
    mul_le_mul_of_nonneg_left hfl hκ.le
  have h2 : κ * b / 2 ≤
      (matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a) / mε := by
    linarith
  have h3 : κ * b / 2 * mε ≤ matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a :=
    (le_div_iff₀ hmε).1 h2
  have hq : 1 / Cm ≤ mε * ε := by
    rw [div_le_iff₀ hCm]
    linarith
  have h4 : κ * b / (2 * Cm) / ε ≤ κ * b / 2 * mε := by
    rw [div_le_iff₀ hε]
    have e1 : κ * b / (2 * Cm) = κ * b / 2 * (1 / Cm) := by
      field_simp
    rw [e1]
    have hkb : 0 ≤ κ * b / 2 := by positivity
    calc κ * b / 2 * (1 / Cm) ≤ κ * b / 2 * (mε * ε) := mul_le_mul_of_nonneg_left hq hkb
      _ = κ * b / 2 * mε * ε := by ring
  linarith

end MatedCRT.S5c
