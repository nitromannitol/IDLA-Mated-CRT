import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedExitBarrier
import MatedCRT.Proofs.Sec4.SubsequentialConvergence.PreparedBoundaryReduction

/-! Uniform convergence from local convergence and a vanishing boundary barrier. -/

namespace MatedCRT

open Filter Topology Set Metric

/-- A locally uniform limit extends by zero, with uniform convergence on the
closed ball, when the approximants vanish uniformly near the boundary. -/
theorem tendstoUniformlyOn_closedBall_of_local_boundary
    {ρ : ℝ} (F : ℕ → ℂ → ℝ) (w : ℂ → ℝ)
    (hloc : ∀ r : ℝ, 0 < r → r < ρ →
      TendstoUniformlyOn F w atTop (closedBall 0 r))
    (hb : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < ρ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall 0 ρ \ closedBall 0 r, |F n x| < δ) :
    TendstoUniformlyOn F ((ball 0 ρ).indicator w)
      atTop (closedBall 0 ρ) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  obtain ⟨r, hr0, hrρ, hbar⟩ := hb (δ / 3) (by linarith)
  have hwsmall : ∀ x ∈ ball 0 ρ \ closedBall 0 r, |w x| ≤ δ / 3 := by
    intro x hx
    have hxr : dist x 0 < ρ := mem_ball.mp hx.1
    let s := (dist x 0 + ρ) / 2
    have hs0 : 0 < s := by dsimp [s]; have := dist_nonneg (x := x) (y := (0 : ℂ)); linarith
    have hsρ : s < ρ := by dsimp [s]; linarith
    have hxs : x ∈ closedBall 0 s := by rw [mem_closedBall]; dsimp [s]; linarith
    have ht := (hloc s hs0 hsρ).tendsto_at hxs
    apply le_of_tendsto ht.abs
    filter_upwards [hbar] with n hn
    exact le_of_lt (hn x ⟨ball_subset_closedBall hx.1, hx.2⟩)
  filter_upwards [hbar, (Metric.tendstoUniformlyOn_iff.mp (hloc r hr0 hrρ))
    δ hδ] with n hn hlocal x hx
  by_cases hxr : x ∈ closedBall 0 r
  · have hxin : x ∈ ball 0 ρ := by
      rw [mem_ball]; exact (mem_closedBall.mp hxr).trans_lt hrρ
    simpa [Set.indicator_of_mem hxin] using hlocal x hxr
  · have hF := hn x ⟨hx, hxr⟩
    by_cases hxin : x ∈ ball 0 ρ
    · have hw := hwsmall x ⟨hxin, hxr⟩
      have htri := abs_sub_le (F n x) 0 (w x)
      simp only [sub_zero, zero_sub, abs_neg] at htri
      simp only [Set.indicator_of_mem hxin, Real.dist_eq]
      rw [abs_sub_comm]
      linarith
    · simp only [Set.indicator_of_notMem hxin, Real.dist_eq, zero_sub, abs_neg]
      linarith

/-- The normalized exit-time limit upgrades every local odometer limit along
every further subsequence to uniform convergence on the closed ball. -/
theorem odometer_prepared_uniform_of_normalized_exit
    (𝒮 : SpaceFillingSLEModel) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ∀ t : ℝ, 0 < t → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        OdometerLocalLimit S ρ t (e ∘ φ ∘ ψ) ω w →
        TendstoUniformlyOn
          (fun n => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ n))) ω)
          ((ball 0 ρ).indicator w) atTop (closedBall 0 ρ) := by
  obtain ⟨φ, hφ, hbar⟩ := odometer_prepared_boundary_small_of_normalized_exit
    𝒮 h37 hγ hγ2 hρ hρ1 S hS e he he0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hbar] with ω hbar
  intro t ht ψ hψ w hw
  apply tendstoUniformlyOn_closedBall_of_local_boundary
  · intro r hr0 hrρ
    apply hw.2 (closedBall 0 r) (isCompact_closedBall 0 r)
    rw [isClosed_closedBall.closure_eq]
    exact closedBall_subset_ball hrρ
  · intro δ hδ
    obtain ⟨r, hr0, hrρ, hr⟩ := hbar δ hδ
    refine ⟨r, hr0, hrρ, ?_⟩
    exact (hψ.tendsto_atTop.eventually hr).mono (fun _ hn x hx => hn t ht x hx)

end MatedCRT
