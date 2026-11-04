import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FixedGreenSum

/-! Measurability of the Green function on a ball, including its pole. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls

/-- Uniform Green convergence away from the pole implies almost-everywhere
strong measurability of the scaled limiting kernel throughout the ball. -/
theorem greenFunction_ae_aestronglyMeasurableOn_ball
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    ∀ᵐ ω ∂S.P, AEStronglyMeasurable
      (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) ((S.μ ω).restrict (ball z r)) := by
  let d : ℕ → ℝ := fun n => min ((r - dist y z) / 2) (1 / ((n : ℝ) + 1))
  let D : ℕ → Set ℂ := fun n => ball z r \ ball y (d n)
  have hy' : dist y z < r := hy
  have hd : ∀ n, 0 < d n := by
    intro n
    exact lt_min (by linarith) (by positivity)
  have hsmall : ∀ n, d n + dist y z < r := by
    intro n
    have h := min_le_left ((r - dist y z) / 2) (1 / ((n : ℝ) + 1))
    dsimp [d] at *
    linarith
  have hD : ∀ n, D n ⊆ closedBall z r \ {y} := by
    intro n x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    intro hxy
    have : x = y := mem_singleton_iff.mp hxy
    subst x
    exact hx.2 (mem_ball_self (hd n))
  have hcover : ball z r ⊆ (⋃ n, D n) ∪ {y} := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inr (mem_singleton_iff.mpr hxy)
    · have hdist : 0 < dist x y := dist_pos.mpr hxy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdist
      apply Or.inl
      apply mem_iUnion.mpr
      refine ⟨n, hx, ?_⟩
      rw [mem_ball]
      have hdle : d n ≤ 1 / ((n : ℝ) + 1) := min_le_right _ _
      exact not_lt.mpr (hdle.trans (le_of_lt hn))
  have haway : ∀ n, ∀ᵐ ω ∂S.P, IntegrableOn
      (fun x => S.c₀ / 6 * greenFunction (ball z r) y x) (D n) (S.μ ω) := by
    intro n
    exact greenFunction_ae_integrableOn_away_from_pole 𝒮 h33 hγ hγ2 hρ hρ1 S hS
      hr hball hy (D n) (hD n) (sdiff_subset.trans hball)
      (infDist_punctured_ball_pos (hd n) (hsmall n))
  filter_upwards [ae_all_iff.mpr haway] with ω hω
  have hu : AEStronglyMeasurable (fun x => S.c₀ / 6 * greenFunction (ball z r) y x)
      ((S.μ ω).restrict (⋃ n, D n)) := AEStronglyMeasurable.iUnion fun n => (hω n).1
  have hs : AEStronglyMeasurable (fun x => S.c₀ / 6 * greenFunction (ball z r) y x)
      ((S.μ ω).restrict {y}) := by
    apply AEStronglyMeasurable.congr (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ℂ => (0 : ℝ)) ((S.μ ω).restrict {y}))
    filter_upwards [ae_restrict_mem (measurableSet_singleton y)] with x hx
    simp [mem_singleton_iff.mp hx, greenFunction_self]
  exact ((aestronglyMeasurable_union_iff).2 ⟨hu, hs⟩).mono_measure
    (Measure.restrict_mono hcover le_rfl)

end MatedCRT
