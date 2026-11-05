import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GreenPart
import MatedCRT.Proofs.LBM.DirichletDisc
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit
import MatedCRT.Steps.Sec3.DiscreteDirichletProblem
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# Lemma 3.5: the continuum candidate (`DirichletLimitStep`)

Almost surely, the continuum candidate `f̄ = E_·[φ(X_τ)] - c₀ ∫_{B_r(z)} G_{B_r(z)}(·, y) ψ(y) μ_h(dy)` of Lemma 3.5
(`dirichletLimit`, normalized LBM `X`) is

* the Poisson extension of `φ` minus `c₀` times the Green potential of `ψ μ_h`: LBM and Brownian motion leave
  `B_r(z)` at the same point, and the Brownian exit distribution is harmonic measure (`brownianDirichletDisc`);
* continuous and Hölder continuous on `cl B_r(z)`, equal to `φ` on `∂B_r(z)`, with `Δ f̄ = c₀ ψ μ_h` on `B_r(z)`.

The Green part uses the volume growth condition (Lemma 2.7, `VolumeGrowthStmt`) through the deterministic Green
clause of HB22 Proposition 2.5; the HB statement `GreenPotentialHolderStmt` (whole-plane GFF fields) is not used:
`μ_h` here is the measure of the quantum cone.
-/

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

namespace MatedCRT

/-- Normalized Liouville Brownian motion leaves an open set where the underlying Brownian path does. -/
theorem rescaledLBMExitPosition_eq_brownianExitPosition
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : IsTimeChangeClock (F b)) (h0 : b 0 ∈ U)
    (hfin : ContinuousPath.exitTime U b < ⊤) {m : ℝ} (hm : 0 < m) :
    pathExitPosition U (rescaledLBMPath F m b) = b (ContinuousPath.exitTime U b).toNNReal := by
  have h := rescaledLBMExitTime_eq_clockValue_div hU hF h0 hfin hm
  have hne : Real.toNNReal m ≠ 0 := (Real.toNNReal_pos.2 hm).ne'
  unfold pathExitPosition
  rw [h]
  show liouvilleBrownianPath F b (Real.toNNReal m *
    (Real.toNNReal (F b (ContinuousPath.exitTime U b).toNNReal) / Real.toNNReal m)) = _
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hne]
  change b (clockInverse (F b) (Real.toNNReal (F b (ContinuousPath.exitTime U b).toNNReal))) = _
  exact congrArg b (clockInverse_clockValue hF.map_zero hF.strictMono _)

/-- **The continuum step of Lemma 3.5**, from the volume growth condition (Lemma 2.7). The hypothesis
`GreenPotentialHolderStmt` of `DirichletLimitStep` is not used. -/
theorem dirichletLimitStep_of_volumeGrowth (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) :
    DirichletLimitStep 𝒮 := by
  intro _ γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ
  obtain ⟨M, hM⟩ := hψb
  obtain ⟨Cψ, χψ, hχψ, -, hHψ⟩ := hψh
  have hψc : ContinuousOn ψ (ball z r) := hHψ.continuousOn hχψ
  have hφ' := hφ
  obtain ⟨s, hs, Cφ, χφ, hχφ, -, hHφ⟩ := hφ'
  have hφc : ContinuousOn φ (closedBall z r) :=
    (hHφ.continuousOn hχφ).mono (closedBall_subset_closedBall (by linarith))
  have hφs : ContinuousOn φ (sphere z r) := hφc.mono sphere_subset_closedBall
  obtain ⟨-, -, hu⟩ := brownianDirichletDisc hr hφ
  have hPEh : IsHolderContinuousOn (discPoissonExtension φ z r) (closedBall z r) := by
    convert hu using 1
    funext x
    exact (brownianExitCandidate_eq_discPoissonExtension hr hφc x).symm
  have hPEc : ContinuousOn (discPoissonExtension φ z r) (closedBall z r) :=
    continuousOn_discPoissonExtension hr hφs
  have hm₀ := hS.m₀_pos hγ hγ2
  filter_upwards [hS.isLQGClock, hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1, hS.isLQGMeasure]
    with ω hc hV hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨βm, βp, hVω⟩ := hV
  have hid : dirichletLimit S r z ψ φ ω = fun x => discPoissonExtension φ z r x -
      S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω := by
    funext x
    unfold dirichletLimit
    by_cases hx : x ∈ ball z r
    · rw [ite_eq_left hx, discPoissonExtension_of_mem hx,
        ← integral_pathExitPosition_eq_discPoissonIntegral hr hφc hx]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [(hc x).2, ae_planarBrownianMotion_eval_zero x,
        ae_planarBrownianMotion_exit_any_ball_lt_top x z r] with b hclock hstart hfin
      rw [rescaledLBMExitPosition_eq_brownianExitPosition isOpen_ball hclock
        (by rw [hstart]; exact hx) hfin hm₀, pathExitPosition_eq_eval_exitTime]
    · rw [ite_eq_right hx, discPoissonExtension_of_notMem hx, greenPart_eq_zero_of_notMem hx,
        mul_zero, sub_zero]
  rw [hid]
  have hG := greenPart_integrable_holder hVω hr hball hψc hM
  obtain ⟨CG, tG, htG, -, hHG⟩ := hG.2
  refine ⟨hPEc.sub (continuousOn_const.mul (hHG.continuousOn htG)), ?_, ?_,
    hPEh.sub_const_mul isBounded_closedBall hG.2 S.c₀⟩
  · have h1 := hasLaplacian_zero_of_harmonicOnNhd isOpen_ball
      (harmonicOnNhd_discPoissonExtension (hφs.circleIntegrable hr.le))
    have h2 := greenPart_hasLaplacian hVω hr hball hψc hM S.c₀_nonneg
    have h3 := hasLaplacian_add h1 h2
    rw [zero_add, zero_add] at h3
    have hfun : (fun x => discPoissonExtension φ z r x -
        S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω) =
        fun x => discPoissonExtension φ z r x +
          -(S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω) :=
      funext fun x => sub_eq_add_neg _ _
    rw [hfun]
    exact h3
  · intro x hx
    have hxn := notMem_ball_of_mem_sphere hx
    simp only [discPoissonExtension_of_notMem hxn, greenPart_eq_zero_of_notMem hxn, mul_zero,
      sub_zero]

end MatedCRT
