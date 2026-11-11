import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S5c.Floor
import MatedCRT.FirstPass.S5c.GreenLog
import HarmonicBalls.Steps.SecA.Basic

/-!
# FIRST PASS, Lemma 5.3: realization plumbing of the floor (G-5-3 Section 1)

Discharges the realization hypotheses of `surplus_floor_on_compact` (Floor.lean) from the harmonic-ball family
`IsConeHarmonicBallFamily` (Defs/Setting.lean:266): monotonicity and the intersection `⋂_{t>0} Λ_t = {0}` (Harmonic-Balls
Draft Section 1), the obstacle characterization `Λ_t = interior (closure (cluster))` with continuity of the least
supersolution (Defs/Setting.lean:257), and the logarithmic Green bound (GreenLog.lean). The external facts are named
parameters: cluster openness with the Laplacian (Harmonic-Balls Draft `ClusterOpenLaplacianStmt`, Lemma 3.2), the Green
continuity statement (Harmonic-Balls Draft `GreenFunctionBallStmt`, Prop 2.3), the pole bound (Lemma 3.1 with volume growth),
the fixed-time strict gap (`firstPass_strictObstacleGap`), and the ball bound `Λ_t ⊆ B_{ρ/3}` on `{t < T}`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open _root_.HarmonicBalls
open scoped Real

/-- **Floor on a harmonic-ball family** (G-5-3 Section 1): the realization of `surplus_floor_on_compact`. -/
theorem surplus_floor_of_family {μ : Measure ℂ} {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hsup : FPSuperharmonicOfLaplacianLE) {Λ : ℝ → Set ℂ} (hfam : MatedCRT.IsConeHarmonicBallFamily μ Λ)
    (hC : ∀ s r : ℝ, 0 < s → 0 < r → ∀ z ∈ ball (0 : ℂ) r, IsOpen (cluster μ r z s) ∧
      ∃ ν : Measure ℂ, HasLaplacian (leastSupersolution μ r z s)
        (μ.restrict (cluster μ r z s) + ν.restrict (frontier (cluster μ r z s))) 0 (ball 0 r))
    (hbb : ∀ x ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, 0 ≤ s →
      BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ ρ 0 s))
    (h23 : GreenFunctionBallStmt)
    (hΛc : Λ t ⊆ cluster μ ρ 0 t) (hΛball : Λ t ⊆ ball (0 : ℂ) (ρ / 3))
    {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) (hKΛ : K ⊆ Λ t) :
    ∃ n : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K,
      b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) /
        (t * (1 / 2) ^ n)) := by
  -- the family is contained in the ball `B_{ρ/3}` at every mass below `t`
  have hsub : ∀ s : ℝ, 0 < s → s ≤ t → Λ s ⊆ ball (0 : ℂ) (ρ / 3) := fun s hs hst =>
    (hfam.2.1.monotoneOn (mem_Ioi.2 hs) (mem_Ioi.2 ht) hst).trans hΛball
  have hΛ' : ∀ s : ℝ, 0 < s → s ≤ t → Λ s = interior (closure (cluster μ ρ 0 s)) := fun s hs hst =>
    (hfam.2.2 s (ρ / 3) hs (by linarith) (hsub s hs hst) ρ (by linarith)).1
  have hcont' : ∀ s : ℝ, 0 < s → s ≤ t → ContinuousOn (leastSupersolution μ ρ 0 s) (ball 0 ρ) := fun s hs hst =>
    ((hfam.2.2 s (ρ / 3) hs (by linarith) (hsub s hs hst) ρ (by linarith)).2.1).mono ball_subset_closedBall
  have hmono : ∀ s u : ℝ, 0 < s → s ≤ u → Λ s ⊆ Λ u := fun s u hs hsu =>
    hfam.2.1.monotoneOn (mem_Ioi.2 hs) (mem_Ioi.2 (lt_of_lt_of_le hs hsu)) hsu
  have hint : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 → ∃ s₀ : ℝ, 0 < s₀ ∧ x ∉ Λ s₀ := by
    intro x _ hx0
    have : ∃ s ∈ Ioi (0 : ℝ), x ∉ Λ s := by
      by_contra hc
      apply hx0
      have hall : ∀ s ∈ Ioi (0 : ℝ), x ∈ Λ s := fun s hs => by
        by_contra h
        exact hc ⟨s, hs, h⟩
      have hmem : x ∈ ⋂ s ∈ Ioi (0 : ℝ), Λ s := mem_iInter₂.2 hall
      rw [hfam.2.1.iInter_eq] at hmem
      exact mem_singleton_iff.1 hmem
    obtain ⟨s, hs, hxs⟩ := this
    exact ⟨s, mem_Ioi.1 hs, hxs⟩
  have hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0}) :=
    (continuousOn_greenFunction_ball_of_stmt h23 hρ (mem_ball_self hρ)).mono
      (fun x hx => ⟨ball_subset_closedBall hx.1, hx.2⟩)
  have hGlow : ∀ r : ℝ, 0 < r → r < ρ / 2 → ∀ x ∈ sphere (0 : ℂ) r,
      (2 * π)⁻¹ * Real.log (ρ / 2 / r) ≤ greenFunction (ball 0 ρ) 0 x :=
    fun r hr hrρ x hx => greenFunction_ball_zero_ge_log hr hrρ hx
  exact surplus_floor_on_compact hρ ht hsup
    (fun s hs => (hC s ρ hs hρ 0 (mem_ball_self hρ)).1)
    (fun s hs => by
      obtain ⟨ν, hν⟩ := (hC s ρ hs hρ 0 (mem_ball_self hρ)).2
      exact ⟨_, hν⟩)
    (fun s hs hst => hcont' s hs hst) (fun s hs hst => hΛ' s hs hst) (fun s u hs hsu => hmono s u hs hsu)
    hint hbb hGc hGlow hΛc (hΛball.trans (ball_subset_ball (by linarith))) hK hKne hKΛ

end MatedCRT.S5c
