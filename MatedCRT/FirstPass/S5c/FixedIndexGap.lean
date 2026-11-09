import MatedCRT.FirstPass.S5c.StrictComparison
import MatedCRT.FirstPass.S5c.CompactMinimum

/-!
# FIRST PASS, Lemma 5.3 (three-inputs section 3, A8 and (a)): the fixed-index gap and full compact margins

Deterministic core, for one outcome. Let `Λ` be a cone family (`IsConeHarmonicBallFamily`) with
`t < T = clusterExitTime Λ ρ` and `0 < t`. The cover hypothesis `hcover : ∀ x ∈ Λ_t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ_s`
is the outcome-wise form of (3.1), `Λ_t = ⋃_{s<t} Λ_s`; its almost-sure proof (A1-A4) is not part of this file.
For `x ∈ Λ_t` put `u = max s (t/2)`. Then `t/2 ≤ u < t` and `x ∈ Λ_u` (monotonicity of `Λ`), and

  w_t x - 2 w_{t/2} x ≥ w_t x - (t/u) w_u x > 0,

by `w_{t/2}/(t/2) ≤ w_u/u` (A5, `leastSupersolution_div_le_of_le_clusterExitTime`, the mass comparison (3.4)) and
the strict comparison `clusterMargin_pos_on_cluster` (A7, from the frozen strong minimum principle). On a compact
`K ⊆ Λ_t` the margin is continuous (A5) and positive, so it has a uniform positive lower bound (A9).

Terminology: Armitage-Gardiner (least superharmonic majorant, Perron), Duplantier-Sheffield and Berestycki-Powell
(the cluster `Λ_t` is the harmonic ball of mass `t`).
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric Laplacian

/-- The cluster lies in the closed ball `B̄_ρ` for `t < clusterExitTime` (A5, `Λ_s ⊆ B_{ρ/3} ⊆ B̄_ρ`). -/
theorem cluster_subset_closedBall_of_lt_clusterExitTime {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ) (ht : 0 < t) :
    Λ t ⊆ closedBall (0 : ℂ) ρ :=
  (subset_ball_of_le_clusterExitTime hfam hT ht le_rfl).trans
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))

/-- Pointwise fixed-index gap on the cluster (three-inputs A8): for every `x ∈ Λ_t`,
`w_t x - 2 w_{t/2} x > 0`, given the outcome-wise cover `hcover` (3.1). -/
theorem fixedIndexMargin_pos_on_cluster (hmin : FPStrongMinimumPrinciple) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ) (ht : 0 < t)
    (hcover : ∀ x ∈ Λ t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ s) :
    ∀ x ∈ Λ t, 0 < leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x := by
  intro x hx
  obtain ⟨s, hs, hst, hxs⟩ := hcover x hx
  have hsu : s ≤ max s (t / 2) := le_max_left _ _
  have ht2u : t / 2 ≤ max s (t / 2) := le_max_right _ _
  have hu : 0 < max s (t / 2) := lt_of_lt_of_le hs hsu
  have hut : max s (t / 2) < t := max_lt hst (by linarith)
  have hsub : Λ s ⊆ Λ (max s (t / 2)) := hfam.2.1.monotoneOn (mem_Ioi.2 hs) (mem_Ioi.2 hu) hsu
  have hxu : x ∈ Λ (max s (t / 2)) := hsub hxs
  have hUρ := cluster_subset_closedBall_of_lt_clusterExitTime hfam hρ hT ht
  -- (3.4): w_{t/2} / (t/2) ≤ w_u / u with u = max s (t/2)
  have hdiv := leastSupersolution_div_le_of_le_clusterExitTime hfam hρ hT (half_pos ht) ht2u hut.le x (hUρ hx)
  set u := max s (t / 2) with hu_def
  set a := leastSupersolution μ ρ 0 (t / 2) x with ha_def
  set b := leastSupersolution μ ρ 0 u x with hb_def
  rw [div_le_div_iff₀ (half_pos ht) hu] at hdiv
  -- hdiv : a * u ≤ b * (t / 2)
  have key : 2 * a ≤ (t / u) * b := by
    have h2 : (2 / u) * (a * u) ≤ (2 / u) * (b * (t / 2)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    have e1 : (2 / u) * (a * u) = 2 * a := by field_simp
    have e2 : (2 / u) * (b * (t / 2)) = (t / u) * b := by ring
    linarith
  -- strict comparison (A7) on the cluster Λ_u
  have hmarg : 0 < leastSupersolution μ ρ 0 t x - (t / u) * leastSupersolution μ ρ 0 u x :=
    clusterMargin_pos_on_cluster hmin hfam hρ hT hu hut x hxu
  linarith

/-- Full compact margins with fixed index (three-inputs (a), with `n = 1`), outcome-wise: on every compact
`K ⊆ Λ_t` the margin `w_t - 2 w_{t/2}` has a uniform positive lower bound (A8 + A9). -/
theorem fixedIndexMargin_lower_bound_on_compact (hmin : FPStrongMinimumPrinciple) {μ : Measure ℂ}
    {Λ : ℝ → Set ℂ} (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ)
    (hT : t < clusterExitTime Λ ρ) (ht : 0 < t)
    (hcover : ∀ x ∈ Λ t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ s)
    {K : Set ℂ} (hK : IsCompact K) (hKΛ : K ⊆ Λ t) :
    ∃ β : ℝ, 0 < β ∧
      ∀ x ∈ K, β ≤ leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x := by
  have hUρ := cluster_subset_closedBall_of_lt_clusterExitTime hfam hρ hT ht
  have h1 : ContinuousOn (leastSupersolution μ ρ 0 t) K :=
    (continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT ht le_rfl).mono (hKΛ.trans hUρ)
  have h2 : ContinuousOn (leastSupersolution μ ρ 0 (t / 2)) K :=
    (continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT (half_pos ht) (by linarith)).mono
      (hKΛ.trans hUρ)
  have hcont : ContinuousOn (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x) K :=
    h1.sub (continuousOn_const.mul h2)
  exact exists_pos_lower_bound_on_compact hK hcont
    (fun x hx => fixedIndexMargin_pos_on_cluster hmin hfam hρ hT ht hcover x (hKΛ hx))

end MatedCRT.S5c
