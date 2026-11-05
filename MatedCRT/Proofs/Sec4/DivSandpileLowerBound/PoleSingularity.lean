import HarmonicBalls.Proofs.Potential.GreenPositivity
import HarmonicBalls.Proofs.Potential.GreenBall
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.PoleBarrier

/-! # The continuum Green function near the pole -/

namespace MatedCRT

open Set Metric Filter Topology HarmonicBalls

/-- The Green function of a disc tends uniformly to infinity on punctured
balls shrinking to its centre. The pole itself is excluded because its value
in the real-valued Green-function definition is a junk value. -/
theorem exists_greenFunction_lower_bound_near_zero {ρ : ℝ} (hρ : 0 < ρ) (M : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r < ρ / 2 ∧ ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ r →
      M < greenFunction (ball 0 ρ) 0 x := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((tendsto_atTop.1 Real.tendsto_log_atTop) (2 * Real.pi * M + 1))
  let N := max N₀ 2
  have hN : 1 < N := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlog : 2 * Real.pi * M + 1 ≤ Real.log N := hN₀ N (le_max_left _ _)
  let r := (ρ / 2) / N
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hrρ : r < ρ / 2 := by
    dsimp [r]
    exact div_lt_self (by linarith) hN
  refine ⟨r, hr, hrρ, ?_⟩
  intro x hx0 hx
  have hxρ : ‖x‖ < ρ / 2 := lt_of_le_of_lt hx hrρ
  have hR : 0 < ρ / 2 := by linarith
  have hsubset : closedBall (0 : ℂ) (ρ / 2) ⊆ ball 0 ρ := by
    intro y hy
    change dist y 0 < ρ
    have hy' : dist y 0 ≤ ρ / 2 := hy
    linarith
  have hG := log_div_le_greenFunction (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) ρ))
    hR hsubset (by simpa using hx0) (by simpa using hxρ)
  rw [greenFunction_ball_comm ρ x 0] at hG
  have hNle : N ≤ (ρ / 2) / ‖x‖ := by
    apply (le_div_iff₀ hx0).2
    have hmul : ‖x‖ * N ≤ ρ / 2 := by
      have := mul_le_mul_of_nonneg_right hx (show 0 ≤ N by linarith)
      dsimp [r] at this
      have hNne : N ≠ 0 := by linarith
      rw [div_mul_cancel₀ _ hNne] at this
      exact this
    nlinarith
  have hlogle : Real.log N ≤ Real.log ((ρ / 2) / ‖x‖) :=
    Real.log_le_log (by linarith) hNle
  have hfac : 0 < 2 * Real.pi := by positivity
  have hcomp : M < (2 * Real.pi)⁻¹ * Real.log ((ρ / 2) / ‖x‖) := by
    rw [inv_mul_eq_div, lt_div_iff₀ hfac]
    linarith
  exact hcomp.trans_le (by simpa using hG)

/-- The singularity supplies an arbitrarily low continuum obstacle on a
punctured neighbourhood, with a prescribed error margin. -/
theorem exists_scaled_green_barrier_near_zero {ρ t c δ L : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ 2 * r < ρ ∧ ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ 2 * r →
      -t * c * greenFunction (ball 0 ρ) 0 x + 2 * δ < L := by
  obtain ⟨R, hR, hRρ, hG⟩ := exists_greenFunction_lower_bound_near_zero hρ ((2 * δ - L) / (t * c))
  refine ⟨R / 4, by linarith, by linarith, ?_⟩
  intro x hx0 hx
  have hg := hG x hx0 (by linarith)
  have htc : 0 < t * c := mul_pos ht hc
  have hmul : 2 * δ - L < (t * c) * greenFunction (ball 0 ρ) 0 x := by
    have := (div_lt_iff₀ htc).mp hg
    linarith
  nlinarith

/-- Rescaled annular and inner bounds imply coverage of the ball. This form
matches the convergence statements for the obstacle and least supersolution. -/
theorem ball_subset_fillCells_of_rescaled_annular_barrier
    {μ : MeasureTheory.Measure ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t L r d mε : ℝ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (ht : 0 ≤ t) (hr : 0 < r) (hd : 0 ≤ d) (hρ : r + d < ρ)
    (hmε : 0 < mε) (hsource : vertexOf ε η 0 = 0)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 (r + d)),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x 0 → dist x 0 < r + 2 * d →
      rescale mε ε η (matedObstacle m ε η ρ t) x ≤ L)
    (hw : ∀ x ∈ ball (0 : ℂ) (r + d),
      L < rescale mε ε η (matedLeastSupersolution m ε η ρ t) x) :
    ball (0 : ℂ) r ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  apply ball_subset_fillCells_of_small_cells_and_annular_barrier hη hp hε ht hr hd hρ hsource
    hsymm hlf hcons hcell hdiam
  · intro x hxlo hxhi
    have h := mul_le_mul_of_nonneg_left (hbound x hxlo hxhi) hmε.le
    simpa [rescale, ← mul_assoc, hmε.ne'] using h
  · intro a ha
    obtain ⟨y, hya, hy⟩ := ha
    have ha' : a ∈ cellVertices ε η (ball 0 (r + d)) := by
      refine ⟨y, hya, ?_⟩
      have hy' : dist y 0 < r := hy
      change dist y 0 < r + d
      linarith
    obtain ⟨x, hxa, hvertex⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε a
    have hxy := hdiam a ha' x hxa y hya
    have htri := dist_triangle x y (0 : ℂ)
    have hy' : dist y 0 < r := hy
    have hxball : x ∈ ball (0 : ℂ) (r + d) := by
      change dist x 0 < r + d
      linarith
    have h := mul_lt_mul_of_pos_left (hw x hxball) hmε
    simpa [rescale, hvertex, ← mul_assoc, hmε.ne'] using h

/-- A negative annular bound forces the nonnegative normalization to be
positive, so no separate positivity assumption on the median is needed. -/
theorem ball_subset_fillCells_of_negative_rescaled_annular_barrier
    {μ : MeasureTheory.Measure ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t L r d mε : ℝ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (ht : 0 ≤ t) (hr : 0 < r) (hd : 0 < d) (hρ : r + d < ρ)
    (hmε : 0 ≤ mε) (hL : L < 0) (hsource : vertexOf ε η 0 = 0)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 (r + d)),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x 0 → dist x 0 < r + 2 * d →
      rescale mε ε η (matedObstacle m ε η ρ t) x ≤ L)
    (hw : ∀ x ∈ ball (0 : ℂ) (r + d),
      L < rescale mε ε η (matedLeastSupersolution m ε η ρ t) x) :
    ball (0 : ℂ) r ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  have hlo : r - d ≤ dist (r : ℂ) 0 := by
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    linarith
  have hhi : dist (r : ℂ) 0 < r + 2 * d := by
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    linarith
  have hmpos : 0 < mε := by
    by_contra h
    have hmzero : mε = 0 := le_antisymm (le_of_not_gt h) hmε
    have h := hbound (r : ℂ) hlo hhi
    simp only [rescale, hmzero, inv_zero, zero_mul] at h
    linarith
  exact ball_subset_fillCells_of_rescaled_annular_barrier hη hp hε ht hr hd.le hρ hmpos
    hsource hsymm hlf hcons hcell hdiam hbound hw

/-- Uniform approximation of the continuum obstacle and least supersolution,
together with the Green singularity margin, gives deterministic inner-ball
coverage on the event of a continuum lower bound. -/
theorem ball_subset_fillCells_of_continuum_pole_bounds
    {μ : MeasureTheory.Measure ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t L r δ mε c : ℝ} {η : ℝ → ℂ}
    {w : ℂ → ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (ht : 0 ≤ t) (hr : 0 < r) (hδ : 0 < δ) (hρ : 2 * r < ρ)
    (hmε : 0 ≤ mε) (hL : L < 0) (hsource : vertexOf ε η 0 = 0)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 (r + r / 4)),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ r / 4)
    (hgreen : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ ≤ 2 * r →
      -t * c * greenFunction (ball 0 ρ) 0 x + 2 * δ < L)
    (hlower : ∀ x ∈ ball (0 : ℂ) ρ, L + 2 * δ ≤ w x)
    (hw : ∀ x ∈ ball (0 : ℂ) ρ,
      |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - w x| ≤ δ)
    (hφ : ∀ x : ℂ, r / 2 ≤ ‖x‖ → ‖x‖ ≤ 2 * r →
      |rescale mε ε η (matedObstacle m ε η ρ t) x -
        (-t * c * greenFunction (ball 0 ρ) 0 x)| ≤ δ) :
    ball (0 : ℂ) r ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  apply ball_subset_fillCells_of_negative_rescaled_annular_barrier hη hp hε ht hr
    (show 0 < r / 4 by positivity) (show r + r / 4 < ρ by linarith) hmε hL hsource
    hsymm hlf hcons hcell hdiam
  · intro x hlo hhi
    have hlo' : r / 2 ≤ ‖x‖ := by simpa only [dist_zero_right] using (show r / 2 ≤ dist x 0 by linarith)
    have hhi' : ‖x‖ ≤ 2 * r := by simpa only [dist_zero_right] using (show dist x 0 ≤ 2 * r by linarith)
    have hxpos : 0 < ‖x‖ := by linarith
    have hg := hgreen x hxpos hhi'
    have hp' := (abs_le.mp (hφ x hlo' hhi')).2
    linarith
  · intro x hx
    have hxρ : x ∈ ball (0 : ℂ) ρ := by
      change dist x 0 < ρ
      have hx' : dist x 0 < r + r / 4 := hx
      linarith
    have hw' := (abs_le.mp (hw x hxρ)).1
    have hlower' := hlower x hxρ
    linarith

end MatedCRT
