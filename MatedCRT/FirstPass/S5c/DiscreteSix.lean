import MatedCRT.Defs.Sandpile
import HarmonicBalls.Defs.Obstacle

/-!
# FIRST PASS, Lemma 5.3: discrete obstacle comparison (G-5-3 Section 1, eq. (6))

The discrete least supersolution `w̃^ε_s` dominates the obstacle `-(s ε⁻¹) g^ε_{B_ρ}(0, ·)` on the comparison set
`V^ε(cl B_ρ)` (the admissible set contains `0`, and the constraint is `u ≥ φ` there). Consequently, for `0 < s`,
`V^ε_t(a) = w̃^ε_t(a) + (t ε⁻¹) g^ε(0, a) ≥ w̃^ε_t(a) - (t / s) w̃^ε_s(a)` at every vertex `a` of the comparison set.
This is the discrete inequality (6) of the proof of Lemma 5.3; it is purely algebraic in the Green kernel and needs
no probability. Discrete potential theory of the mated-CRT map (Armitage-Gardiner; Levine-Peres least action).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- The Green kernel `g_A(a, b) = G_A(a, b) / deg(b)` is nonnegative (expected visits divided by a degree). -/
lemma greenKernel_nonneg' (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b := by
  unfold greenKernel greenFn
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- **Discrete obstacle bound** (G-5-3 Section 1): the least supersolution at mass `s` is at least the obstacle
`-(s ε⁻¹) g^ε_{B_ρ}(0, a)` at every vertex `a` of the comparison set `V^ε(cl B_ρ)`. -/
lemma matedObstacle_le_matedLeastSupersolution {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) {a : ℤ} (ha : a ∈ cellVertices ε η (closedBall 0 ρ)) :
    matedObstacle m ε η ρ s a ≤ matedLeastSupersolution m ε η ρ s a := by
  unfold matedLeastSupersolution discreteLeastSupersolution
  have hzero : ∀ b ∈ ballInterior ε η ρ, mLaplacian m (0 : ℤ → ℝ) b ≤ ((matedDeg m b : ℕ) : ℝ)⁻¹ := by
    intro b _
    simp [mLaplacian]
  have hobs : ∀ b ∈ cellVertices ε η (closedBall 0 ρ), matedObstacle m ε η ρ s b ≤ 0 := by
    intro b _
    unfold matedObstacle
    have hg := greenKernel_nonneg' m (ballInterior ε η ρ) 0 b
    have hc : 0 ≤ s / ε := div_nonneg hs hε.le
    have : -(s / ε) * greenKernel m (ballInterior ε η ρ) 0 b ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hc) hg
    simpa [neg_div] using this
  have hne : ((fun u : ℤ → ℝ => u a) '' {u | (∀ b ∈ ballInterior ε η ρ, mLaplacian m u b ≤
      ((matedDeg m b : ℕ) : ℝ)⁻¹) ∧ ∀ b ∈ cellVertices ε η (closedBall 0 ρ), matedObstacle m ε η ρ s b ≤ u b}).Nonempty := by
    refine ⟨(fun u : ℤ → ℝ => u a) 0, Set.mem_image_of_mem _ ⟨fun b hb => hzero b hb, fun b hb => ?_⟩⟩
    exact le_trans (hobs b hb) (le_refl _)
  refine le_csInf hne ?_
  rintro _ ⟨u, ⟨_, hu⟩, rfl⟩
  exact hu a ha

/-- **Discrete inequality (6)** (G-5-3 Section 1): for `0 < s`, `0 < t` and a vertex `a` of the comparison set,
`w̃_t(a) + (t ε⁻¹) g(0,a) ≥ w̃_t(a) - (t/s) w̃_s(a)`, i.e. the discrete surplus dominates the rescaled difference
of least supersolutions at masses `t` and `s`. -/
lemma matedSurplus_ge_discrete_six {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t s : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) {a : ℤ} (ha : a ∈ cellVertices ε η (closedBall 0 ρ)) :
    matedLeastSupersolution m ε η ρ t a - t / s * matedLeastSupersolution m ε η ρ s a ≤
      matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
  have h := matedObstacle_le_matedLeastSupersolution (m := m) hε hs.le ha
  unfold matedObstacle at h
  have hc : 0 ≤ t / s := div_nonneg ht.le hs.le
  have h2 := mul_le_mul_of_nonneg_left h hc
  have e : t / s * (-(s / ε) * greenKernel m (ballInterior ε η ρ) 0 a) =
      -(t / ε * greenKernel m (ballInterior ε η ρ) 0 a) := by
    field_simp
  rw [e] at h2
  linarith

/-- **Surplus at a rescaled point** (G-5-3 Section 1, eqs. (6) and (12)): if the rescaled discrete least
supersolutions at masses `t` and `s` are within `e` of `κ w_t` and `κ w_s` at a point `x` (the uniform convergence of
`ConvergenceDivisibleStmt`), then the discrete surplus at the vertex `vertexOf x` satisfies
`V_t(a)/m_ε ≥ κ (w_t(x) + t (-w_s(x)/s)) - e (1 + t/s)`, with `a = vertexOf x`. -/
lemma surplus_div_ge_of_rescaled_errors {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t s mε κ e : ℝ}
    (hmε : 0 < mε) (hε : 0 < ε) (ht : 0 < t) (hs : 0 < s) {x : ℂ}
    (hx : vertexOf ε η x ∈ cellVertices ε η (closedBall 0 ρ))
    (hEt : |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - κ * leastSupersolution μ ρ 0 t x| ≤ e)
    (hEs : |rescale mε ε η (matedLeastSupersolution m ε η ρ s) x - κ * leastSupersolution μ ρ 0 s x| ≤ e) :
    κ * (leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s)) - e * (1 + t / s) ≤
      (matedLeastSupersolution m ε η ρ t (vertexOf ε η x) + t / ε * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x)) / mε := by
  have h6 := matedSurplus_ge_discrete_six (m := m) (ρ := ρ) (t := t) (s := s) hε ht hs hx
  obtain ⟨hEt1, hEt2⟩ := abs_le.1 hEt
  obtain ⟨hEs1, hEs2⟩ := abs_le.1 hEs
  unfold rescale at hEt1 hEt2 hEs1 hEs2
  set a := vertexOf ε η x with ha
  set Wt := matedLeastSupersolution m ε η ρ t a with hWt_def
  set Ws := matedLeastSupersolution m ε η ρ s a with hWs_def
  set Xt := mε⁻¹ * Wt with hXt
  set Xs := mε⁻¹ * Ws with hXs
  have hWt : Wt = mε * Xt := by
    rw [hXt, ← mul_assoc, mul_inv_cancel₀ hmε.ne', one_mul]
  have hWs : Ws = mε * Xs := by
    rw [hXs, ← mul_assoc, mul_inv_cancel₀ hmε.ne', one_mul]
  have hts : 0 ≤ t / s := div_nonneg ht.le hs.le
  have hXs' : Xs ≤ κ * leastSupersolution μ ρ 0 s x + e := by linarith
  have hXt' : κ * leastSupersolution μ ρ 0 t x - e ≤ Xt := by linarith
  have hkey : κ * (leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s)) - e * (1 + t / s) ≤
      Xt - t / s * Xs := by
    have e1 : t * (-(leastSupersolution μ ρ 0 s x) / s) = -(t / s * leastSupersolution μ ρ 0 s x) := by
      ring
    have h7 := mul_le_mul_of_nonneg_left hXs' hts
    rw [e1]
    nlinarith [h7, hXt']
  rw [le_div_iff₀ hmε]
  have h8 : mε * (κ * (leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 s x) / s)) -
      e * (1 + t / s)) ≤ mε * (Xt - t / s * Xs) := mul_le_mul_of_nonneg_left hkey hmε.le
  have h9 : mε * (Xt - t / s * Xs) = Wt - t / s * Ws := by
    rw [hWt, hWs]
    ring
  nlinarith [h8, h9, h6]

end MatedCRT.S5c
