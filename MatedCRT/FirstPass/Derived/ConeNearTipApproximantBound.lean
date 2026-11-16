import MatedCRT.FirstPass.Derived.ConeReferenceCompactCorrection
import MatedCRT.FirstPass.Derived.NormalizedFieldGivenVanishing

/-! # Reference-cone approximants on balls near the tip -/

noncomputable section

open MeasureTheory Filter Set Topology Metric MarkovProcess
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open LatticeProb.LQG LatticeProb.Gauss

/-- On one event, approximant masses vanish on moving balls contained in the
shrinking dyadic balls about the cone tip, simultaneously for all paths and
all choices of dyadic regularization scales. -/
theorem ae_tendsto_coneRef_approximant_near_tip
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ (w : ContinuousPath ℝ) (k : ℕ → ℕ)
      (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ J, ‖z J‖ + r J ≤ dyadicScale J) →
      Tendsto (fun J => lqgApprox γ (coneRefCircle γ (c ω) w)
        (dyadicScale (k J)) (ball (z J) (r J))) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_singular_approximant_dyadic_ball hX hG hc heq
    hγ hγ2 (MatedCRT.lt_lqgQ_of_mem_Ioo hγ hγ2)
    (δ := 1) (r := 1 / 4) (ρ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)] with ω hω
  intro w k z r hz
  have hc0 : ContinuousOn (fun ρ => c ω ρ 0) (Ioi 0) :=
    (hc ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun ρ hρ => ⟨hρ, mem_univ _⟩)
  obtain ⟨B, hB, hcomp⟩ := coneRef_approximant_le_singular_on_compact γ (c ω) w hc0 1
  have hlim : Tendsto (fun J => ENNReal.ofReal B *
      lqgApprox γ (fieldCircleAverage γ (c ω)) (dyadicScale (k J))
        (ball 0 (dyadicScale J))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hω k) (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun _ => zero_le
  · refine Eventually.of_forall fun J => ?_
    have hsub : ball (z J) (r J) ⊆ ball (0 : ℂ) (dyadicScale J) := by
      apply Metric.ball_subset_ball'
      simpa only [dist_zero_right, add_comm] using hz J
    have hscale : dyadicScale J ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hsub1 : ball (z J) (r J) ⊆ closedBall (0 : ℂ) 1 :=
      hsub.trans ((ball_subset_ball hscale).trans ball_subset_closedBall)
    have hkpos : 0 < dyadicScale (k J) := by unfold dyadicScale; positivity
    have hkle : dyadicScale (k J) ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    refine (hcomp _ hkpos hkle _ measurableSet_ball hsub1).trans ?_
    gcongr


end MatedCRT.FirstPass.Derived
