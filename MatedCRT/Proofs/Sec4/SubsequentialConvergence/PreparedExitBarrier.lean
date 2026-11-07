import MatedCRT.Proofs.Sec4.SubsequentialConvergence.ExitTimeBarrier
import MatedCRT.Proofs.Sec4.SubsequentialProperties.ObstacleApproximation
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundary

/-! Almost-sure preparation of the odometer exit-time barrier. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Uniform convergence in probability to a random function admits an almost
surely uniformly convergent deterministic subsequence. -/
theorem exists_ae_uniform_subsequence_random
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (K : Set ℂ)
    (F : ℝ → Ω → ℂ → ℝ) (g : Ω → ℂ → ℝ)
    (hconv : TendstoUniformlyOnInProbability P F g K)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun n => F (e (φ n)) ω) (g ω) atTop K := by
  let E : ℕ → ℝ → Set Ω := fun j ε =>
    {ω | ¬ ∃ x ∈ K, 1 / ((j : ℝ) + 1) < |F ε ω x - g ω x|}
  have hE : ∀ j, ProbTendsToOne P (E j) := by
    intro j
    have hp : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    simpa only [ProbTendsToOne, E, compl_ofPred, not_not] using hconv _ hp
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_eventually_mem_all hE he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with ω hω
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hω j] with n hn x hx
  have hb : |F (e (φ n)) ω x - g ω x| ≤ 1 / ((j : ℝ) + 1) :=
    le_of_not_gt (fun h => hn ⟨x, hx, h⟩)
  simpa only [Real.dist_eq, abs_sub_comm] using hb.trans_lt hj

/-- Along a deterministic thinning, the exit-time barrier gives almost-sure
boundary control simultaneously for every positive odometer time. -/
theorem odometer_prepared_boundary_small_of_normalized_exit
    (𝒮 : SpaceFillingSLEModel) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ δ : ℝ, 0 < δ → ∃ r' : ℝ, 0 < r' ∧ r' < ρ ∧ ∀ᶠ n in atTop,
        ∀ t : ℝ, 0 < t → ∀ x ∈ closedBall 0 ρ \ closedBall 0 r',
          |rescaledMatedLeastSupersolution S ρ t (e (φ n)) ω x| < δ := by
  let R := (ρ + 1) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hρR : ρ ≤ R := by dsimp [R]; linarith
  obtain ⟨q, hq, hconv⟩ := h37 γ hγ hγ2 R hR hR1 Ω S hS ρ 0 hρ (ball_subset_ball hρR)
  obtain ⟨φ, hφ, hφae⟩ := exists_ae_uniform_subsequence_random S.P (closedBall 0 ρ)
    (fun ε ω => rescale (S.mε ε) ε (S.η ω)
      (normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ))) q hconv e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hq, hφae, ae_abs_rescaledOdometer_le_rescaled_normExitTime
    𝒮 hγ hγ2 hρ hρ1 S hS] with ω hq hconv hbar
  intro δ hδ
  obtain ⟨r', hr'0, hr'ρ, hsmall⟩ := exists_boundary_layer_of_continuousOn hρ hq.1 hq.2.2
    (show 0 < δ / 2 by linarith)
  refine ⟨r', hr'0, hr'ρ, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) (δ / 2) (by linarith)] with n hn
  intro t ht x hx
  have hd := hn x hx.1
  rw [Real.dist_eq] at hd
  rw [abs_sub_comm] at hd
  have hs := hsmall x hx
  have htri := abs_add_le
    (rescale (S.mε (e (φ n))) (e (φ n)) (S.η ω)
      (normExitTime (S.mult (e (φ n)) ω) (ballInterior (e (φ n)) (S.η ω) ρ)) x - q ω x)
    (q ω x)
  simp only [sub_add_cancel] at htri
  have hbound := hbar t (e (φ n)) ht (he _) x
  linarith

end MatedCRT
