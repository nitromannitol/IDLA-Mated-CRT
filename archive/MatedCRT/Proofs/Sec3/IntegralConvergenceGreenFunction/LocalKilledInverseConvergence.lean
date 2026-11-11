import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledInverseConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.KilledClockConvergence
import HarmonicBalls.Proofs.Sec8.OpenBallDensity
import Mathlib.Topology.TietzeExtension

/-! # Localization of killed-clock inverse convergence -/

namespace MatedCRT

open Filter HarmonicBalls MarkovProcess Topology Set MeasureTheory
open scoped ENNReal NNReal

/-- Each field that is continuous on a closed set has a continuous global
extension. The choice is made independently at each regularization scale. -/
theorem exists_continuous_scale_extensions (hε : ℝ → ℂ → ℝ) (K : Set ℂ)
    (hK : IsClosed K) :
    ∃ gε : ℝ → ℂ → ℝ, ∀ ε, Continuous (gε ε) ∧
      (ContinuousOn (hε ε) K → Set.EqOn (hε ε) (gε ε) K) := by
  classical
  have h : ∀ ε, ∃ g : ℂ → ℝ, Continuous g ∧
      (ContinuousOn (hε ε) K → Set.EqOn (hε ε) g K) := by
    intro ε
    by_cases hc : ContinuousOn (hε ε) K
    · let f : C(K, ℝ) := ⟨fun z => hε ε z, continuousOn_iff_continuous_domRestrict.mp hc⟩
      obtain ⟨g, hg⟩ := f.exists_restrict_eq hK
      refine ⟨g, g.continuous, fun _ z hz => ?_⟩
      exact (congrFun (congrArg DFunLike.coe hg) ⟨z, hz⟩).symm
    · exact ⟨fun _ => 0, continuous_const, fun hcont => (hc hcont).elim⟩
  choose g hg using h
  exact ⟨g, hg⟩

/-- Compact containment gives continuity of the Dirichlet circle averages
on the closed killing domain at all sufficiently fine dyadic scales. -/
theorem IsDirichletGFF.ae_continuousOn_dyadic_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsDirichletGFF P D h hcirc) (hD : IsOpen D)
    (hbounded : Bornology.IsBounded U) (hclosure : closure U ⊆ D) :
    ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, ContinuousOn (hcirc ω (dyadicScale n)) (closure U) := by
  obtain ⟨δ, hδ, hsub⟩ := hbounded.isCompact_closure.exists_cthickening_subset_open hD hclosure
  have hscale : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hscale
  filter_upwards [hgff.continuous_circle] with ω hcont
  refine ⟨N, fun n hn => ?_⟩
  apply hcont.comp (continuous_const.prodMk continuous_id).continuousOn
  intro z hz
  refine ⟨dyadicScale_pos n, ?_⟩
  intro w hw
  apply hsub
  apply Metric.mem_cthickening_of_dist_le w z δ (closure U) hz
  exact (Metric.mem_closedBall.mp hw).trans (le_of_lt (hN n hn))

/-- Dyadic killed time-changed paths converge using continuity of the
circle-average field on the closure of the killing domain at sufficiently
small dyadic scales. -/
theorem tendsto_killedGMCClockApprox_path_of_continuousOn
    {D : Set ℂ} {γ : ℝ} {hε : ℝ → ℂ → ℝ} {b : ContinuousPath ℂ}
    {G : ℝ≥0 → ℝ} (hG : IsTimeChangeClock G)
    (hfin : ContinuousPath.exitTime D b < ⊤)
    (N : ℕ) (hfield : ∀ n ≥ N, ContinuousOn (hε (dyadicScale n)) (closure D))
    (hconv : ∀ s ≤ (ContinuousPath.exitTime D b).toNNReal,
      Tendsto (fun n => killedGMCClockApprox D γ hε (dyadicScale n) b s)
        atTop (𝓝 (G s)))
    {t : ℝ≥0} (ht : (t : ℝ) < G (ContinuousPath.exitTime D b).toNNReal) :
    Tendsto (fun n => b ((killedClockInverse
      (killedGMCClockApprox D γ hε (dyadicScale n) b)
        (ContinuousPath.exitTime D b) t).toNNReal)) atTop
      (𝓝 (b ((killedClockInverse G (ContinuousPath.exitTime D b) t).toNNReal))) := by
  obtain ⟨gε, hg⟩ := exists_continuous_scale_extensions hε (closure D) isClosed_closure
  have heq : ∀ n ≥ N, ∀ s, killedGMCClockApprox D γ hε (dyadicScale n) b s =
      killedGMCClockApprox D γ gε (dyadicScale n) b s := by
    intro n hn s
    apply killedGMCClockApprox_eq_of_eqOn
    exact (hg (dyadicScale n)).2 (hfield n hn) |>.mono subset_closure
  have hconv' : ∀ s ≤ (ContinuousPath.exitTime D b).toNNReal,
      Tendsto (fun n => killedGMCClockApprox D γ gε (dyadicScale n) b s)
        atTop (𝓝 (G s)) := by
    intro s hs
    apply (hconv s hs).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact heq n hn s
  have h := tendsto_killedGMCClockApprox_path_of_pointwise hG hfin
    (fun n => (hg (dyadicScale n)).1) hconv' ht
  apply h.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [show killedGMCClockApprox D γ hε (dyadicScale n) b =
    killedGMCClockApprox D γ gε (dyadicScale n) b from funext (heq n hn)]

end MatedCRT

#print axioms MatedCRT.exists_continuous_scale_extensions
#print axioms MatedCRT.IsDirichletGFF.ae_continuousOn_dyadic_tail
#print axioms MatedCRT.tendsto_killedGMCClockApprox_path_of_continuousOn
