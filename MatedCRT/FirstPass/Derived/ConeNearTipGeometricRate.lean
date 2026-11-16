import MatedCRT.FirstPass.Derived.ConeReferenceCompactCorrection
import LatticeProb.LQG.SingularApproximantCommonEvent
import MatedCRT.FirstPass.Derived.NormalizedFieldGivenVanishing

/-! # Geometric bounds for cone approximants near the tip -/

noncomputable section

open MeasureTheory Filter Set Topology Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open LatticeProb.LQG LatticeProb.Gauss

/-- On one field event, all cone paths admit a geometric upper bound for
approximant masses of balls contained in a small dyadic ball about the tip.
The bound holds simultaneously at every dyadic regularization scale. -/
theorem ae_coneRef_approximant_near_tip_geometric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, 0 < n ∧ ∃ J₀ : ℕ,
      ∀ w : ContinuousPath ℝ, ∃ B : ℝ, 0 < B ∧ ∀ J k : ℕ,
        dyadicScale J ≤ 1 / 4 → J₀ ≤ J / n → ∀ (z : ℂ) (r : ℝ),
        ‖z‖ + r ≤ dyadicScale J →
        lqgApprox γ (coneRefCircle γ (c ω) w) (dyadicScale k) (ball z r) ≤
          ENNReal.ofReal B *
            max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
              Real.exp (-(Real.log 2) * J)))
              (ENNReal.ofReal (Real.exp (γ * (|γ| * Real.log 2)) *
                (Real.exp (-(γ * (lqgQ γ - γ) * Real.log 2 / 2)) ^ (J / n) /
                  (1 - Real.exp (-(γ * (lqgQ γ - γ) * Real.log 2 / 2)))))) := by
  filter_upwards [ae_exists_singular_approximant_uniform_dyadic_bound hX hG hc heq
    hγ hγ2 (MatedCRT.lt_lqgQ_of_mem_Ioo hγ hγ2)
    (δ := 1) (r := 1 / 4) (ρ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)] with ω hω
  obtain ⟨C, hC, n, hn, J₀, hbound⟩ := hω
  refine ⟨C, hC, n, hn, J₀, fun w => ?_⟩
  have hc0 : ContinuousOn (fun ρ => c ω ρ 0) (Ioi 0) :=
    (hc ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun ρ hρ => ⟨hρ, mem_univ _⟩)
  obtain ⟨B, hB, hcomp⟩ := coneRef_approximant_le_singular_on_compact γ (c ω) w hc0 1
  refine ⟨B, hB, fun J k hJ hJ₀ z r hz => ?_⟩
  have hsub : ball z r ⊆ ball (0 : ℂ) (dyadicScale J) := by
    apply Metric.ball_subset_ball'
    simpa only [dist_zero_right, add_comm] using hz
  have hsub1 : ball z r ⊆ closedBall (0 : ℂ) 1 := by
    apply hsub.trans
    apply (ball_subset_ball _).trans ball_subset_closedBall
    linarith
  have hkpos : 0 < dyadicScale k := by unfold dyadicScale; positivity
  have hkle : dyadicScale k ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine (hcomp _ hkpos hkle _ measurableSet_ball hsub1).trans ?_
  exact mul_le_mul' (le_refl _) ((measure_mono hsub).trans (hbound J k hJ hJ₀))

end MatedCRT.FirstPass.Derived
