import MatedCRT.FirstPass.S1c.Countable
import MatedCRT.FirstPass.S1c.Cluster

/-!
# The analytic set of moment vectors of supersolutions (Lemma 1 analytic layer)

For a locally finite `ν` with `ν(B̄_R) < ∞`, the least-supersolution sublevel sets of `HarmonicBalls.supersolutions`
are described through countably many pairings: a supersolution `w` is the continuous extension of its restriction
`g ∈ C(B̄_R)`, and the `LaplacianLE` inequality holds iff the pairings `∫ extendCM g · Δφs k` are dominated by the
moments `∫ φs k dν` (`laplacianLE_extend_of_countable`, `integral_mul_laplacian_eq_extend`). The pairs
`(moment vector, g)` with the countable domination, the Green obstacle off the pole and `g(z₀) < q` form a Borel set in
the Polish space `(ℕ → ℝ) × C(B̄_R, ℝ)`; its projection to the moment vector is analytic (Lusin; Kechris 14.3).
No paper-specific input enters here beyond the definitions of `supersolutions` and `greenFunction`.
-/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory HarmonicBalls

variable {R : ℝ}

/-- The pairing of `g ∈ C(B̄_R)` with the `k`-th test function: `∫ extendCM g · Δφs k`. -/
noncomputable def momentCM (hR : 0 ≤ R) (φs : ℕ → ℂ → ℝ) (k : ℕ) (g : C(closedBall (0 : ℂ) R, ℝ)) : ℝ :=
  ∫ x, extendCM R hR g x * Laplacian.laplacian (φs k) x

theorem dist_extendCM_le (hR : 0 ≤ R) (g h : C(closedBall (0 : ℂ) R, ℝ)) (x : ℂ) :
    dist (extendCM R hR g x) (extendCM R hR h x) ≤ dist g h :=
  ContinuousMap.dist_apply_le_dist _

/-- The pairing depends Lipschitz-continuously on `g` in the sup norm. -/
theorem dist_momentCM_le (hR : 0 ≤ R) {φs : ℕ → ℂ → ℝ} {k : ℕ}
    (hφ : IsTestFunction (ball (0 : ℂ) R) (φs k)) (g h : C(closedBall (0 : ℂ) R, ℝ)) :
    dist (momentCM hR φs k g) (momentCM hR φs k h) ≤
      (∫ x, ‖Laplacian.laplacian (φs k) x‖) * dist g h := by
  have hΔ : Integrable (fun x => Laplacian.laplacian (φs k) x) := by
    simpa using integrable_mul_laplacian (w := fun _ => (1 : ℝ)) continuous_const hφ
  have hIg := integrable_mul_laplacian (w := extendCM R hR g) (continuous_extendCM hR g) hφ
  have hIh := integrable_mul_laplacian (w := extendCM R hR h) (continuous_extendCM hR h) hφ
  have hsub : momentCM hR φs k g - momentCM hR φs k h =
      ∫ x, (extendCM R hR g x - extendCM R hR h x) * Laplacian.laplacian (φs k) x := by
    unfold momentCM
    rw [← integral_sub hIg hIh]
    congr 1
    funext x
    ring
  have hpt : ∀ x, ‖(extendCM R hR g x - extendCM R hR h x) * Laplacian.laplacian (φs k) x‖ ≤
      dist g h * ‖Laplacian.laplacian (φs k) x‖ := by
    intro x
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← dist_eq_norm]
    exact dist_extendCM_le hR g h x
  have hbd := norm_integral_le_of_norm_le (hΔ.norm.const_mul (dist g h)) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hbd
  rw [Real.norm_eq_abs] at hbd
  rw [Real.dist_eq, hsub]
  exact hbd.trans_eq (mul_comm _ _)

/-- The pairing is continuous on `C(B̄_R, ℝ)`. -/
theorem continuous_momentCM (hR : 0 ≤ R) {φs : ℕ → ℂ → ℝ} {k : ℕ}
    (hφ : IsTestFunction (ball (0 : ℂ) R) (φs k)) : Continuous (momentCM hR φs k) := by
  refine Metric.continuous_iff.2 fun g ε hε => ?_
  have hC : 0 ≤ ∫ x, ‖Laplacian.laplacian (φs k) x‖ := integral_nonneg fun x => norm_nonneg _
  have hpos : 0 < (∫ x, ‖Laplacian.laplacian (φs k) x‖) + 1 := by linarith
  refine ⟨ε / ((∫ x, ‖Laplacian.laplacian (φs k) x‖) + 1), div_pos hε hpos, fun h hgh => ?_⟩
  have h1 := dist_momentCM_le hR hφ h g
  have h2 : dist h g * ((∫ x, ‖Laplacian.laplacian (φs k) x‖) + 1) < ε := (lt_div_iff₀ hpos).1 hgh
  have h3 : (∫ x, ‖Laplacian.laplacian (φs k) x‖) * dist h g ≤
      dist h g * ((∫ x, ‖Laplacian.laplacian (φs k) x‖) + 1) := by
    nlinarith [dist_nonneg (x := h) (y := g)]
  linarith [h1, h2, h3]

/-- The Borel-type set of pairs `(m, g)`: the moment vector `m` dominates the pairings of `g`, `g` lies above the
Green obstacle `-u G` on `B̄_R` off the pole, and `g(z₀) < q`. -/
def supersolutionPairs (hR : 0 ≤ R) (φs : ℕ → ℂ → ℝ) (u : ℝ) (G : ℂ → ℝ) (z0 : closedBall (0 : ℂ) R) (q : ℝ) :
    Set ((ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ)) :=
  {p | (∀ k, momentCM hR φs k p.2 ≤ p.1 k) ∧
    (∀ z : closedBall (0 : ℂ) R, (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z) ∧ p.2 z0 < q}

theorem measurableSet_supersolutionPairs (hR : 0 ≤ R) {φs : ℕ → ℂ → ℝ}
    (hφs : ∀ k, IsTestFunction (ball (0 : ℂ) R) (φs k)) (u : ℝ) (G : ℂ → ℝ) (z0 : closedBall (0 : ℂ) R)
    (q : ℝ) : MeasurableSet (supersolutionPairs hR φs u G z0 q) := by
  have h1 : IsClosed {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | ∀ k, momentCM hR φs k p.2 ≤ p.1 k} := by
    have : {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | ∀ k, momentCM hR φs k p.2 ≤ p.1 k} =
        ⋂ k, {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | momentCM hR φs k p.2 ≤ p.1 k} := by
      ext p
      simp
    rw [this]
    exact isClosed_iInter fun k => isClosed_le
      ((continuous_momentCM hR (hφs k)).comp continuous_snd) ((continuous_apply k).comp continuous_fst)
  have h2 : IsClosed {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) |
      ∀ z : closedBall (0 : ℂ) R, (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z} := by
    have : {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | ∀ z : closedBall (0 : ℂ) R, (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z} =
        ⋂ z : closedBall (0 : ℂ) R, {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z} := by
      ext p
      simp
    rw [this]
    refine isClosed_iInter fun z => ?_
    by_cases hz : (z : ℂ) = 0
    · have hu : {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z} = univ := by
        ext p
        simp [hz]
      rw [hu]
      exact isClosed_univ
    · have hu : {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | (z : ℂ) ≠ 0 → -u * G z ≤ p.2 z} =
          {p | -u * G z ≤ p.2 z} := by
        ext p
        simp [hz]
      rw [hu]
      exact isClosed_le continuous_const ((continuous_eval_const z).comp continuous_snd)
  have h3 : IsOpen {p : (ℕ → ℝ) × C(closedBall (0 : ℂ) R, ℝ) | p.2 z0 < q} :=
    isOpen_lt ((continuous_eval_const z0).comp continuous_snd) continuous_const
  exact h1.measurableSet.inter (h2.measurableSet.inter h3.measurableSet)

/-- The moment projection of the supersolution pairs is analytic (Lusin; Kechris 14.3). -/
theorem analyticSet_supersolutionMoments (hR : 0 ≤ R) {φs : ℕ → ℂ → ℝ}
    (hφs : ∀ k, IsTestFunction (ball (0 : ℂ) R) (φs k)) (u : ℝ) (G : ℂ → ℝ) (z0 : closedBall (0 : ℂ) R)
    (q : ℝ) : AnalyticSet (Prod.fst '' supersolutionPairs hR φs u G z0 q) :=
  MeasurableSet.analyticSet_image (measurableSet_supersolutionPairs hR hφs u G z0 q) measurable_fst

end MatedCRT
