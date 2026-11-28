import MatedCRT.FirstPass.Derived.ConeApproxBallPower
import MatedCRT.FirstPass.Derived.ConeDilationRatioHolds
import MatedCRT.FirstPass.Derived.ConeGFFCoupling2
import MatedCRT.FirstPass.Derived.ChartTransportRateConvergence
import HarmonicBalls.Proofs.Potential.LQGSingularContinuumBallPower
import LatticeProb.LQG.CircleAverageCorrectionBallPower

/-!
# Proof of the uniform small-ball power bound for the approximations of the cone LQG measure

`coneApproxBallPowerStmt` proves `ConeApproxBallPowerStmt γ` for `0 < γ < 2`: in every valid environment, almost
surely, for every `R > 0` there are `β, t₀ > 0` with `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, `x ∈ B̄(0, R)` and
`t ∈ (0, t₀)`, where `μ_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` are the circle-average approximations of the γ-LQG measure of
the γ-quantum cone field `h`.

The proof follows the transfer on an arbitrary disc of the IDLA paper (Definition 2.1 and (2.3)–(2.4);
Duplantier–Miller–Sheffield, Lemma 4.9 and Definition 4.10): the cone is coupled with an independent standard Brownian
motion `w` (`isWholePlaneGFF_coneGFF`) so that the coupled field `h^ℂ` is a whole-plane GFF under `P ⊗ BM` and
`h = h^ℂ - γ log |·| + D` with a continuous correction `D = coneCouplingRemainder` vanishing on the unit disc
(`coneCircle_eq_addCircleAverage`, `continuous_coneCouplingRemainder`). The whole-plane field with the singularity
`-γ log |·|` satisfies the small-ball bound `C r^κ` at all smoothing radii `0 < ε ≤ 1` and all centers of a bounded
disc (`IsWholePlaneGFF.ae_singular_continuum_small_ball_power_all_disks`, Harmonic-Balls-LQG; Bou-Rabee–Gwynne,
Lemma 2.4), the correction multiplies the approximations on `B̄(0, R + 2)` by at most `e^{γ sup D}`
(`LatticeProb.LQG.lqgApprox_add_circleAverage_le`), and `K r^κ ≤ r^{κ/2}` for small `r` gives the prefactor one. The
Brownian coordinate is then dropped.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

open FirstPass.Derived

/-- The dyadic scales are at most one. -/
theorem dyadicScale_le_one' (n : ℕ) : HarmonicBalls.dyadicScale n ≤ 1 := by
  unfold HarmonicBalls.dyadicScale
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The approximations of the γ-LQG measure of Harmonic-Balls-LQG and of Lattice-Probability agree. -/
theorem harmonicBalls_lqgApprox_eq (γ : ℝ) (h : ℝ → ℂ → ℝ) (ε : ℝ) :
    HarmonicBalls.lqgApprox γ h ε = LatticeProb.LQG.lqgApprox γ h ε := rfl

/-- **The small-ball bound for the cone from the coupled whole-plane field (pathwise).** Let `h` be circle averages
jointly continuous on `(0, ∞) × ℂ`, `w` a continuous path, and assume that the coupled field
`h^ℂ = coneGFFCircle γ h w` with the singularity `-γ log |·|` satisfies on every bounded disc the small-ball bound
`C r^κ` for all smoothing radii `0 < ε ≤ 1`. Then for every `R > 0` there are `β, t₀ > 0` with
`μ_{ε_n}(B(x, t)) ≤ t^β` for the approximations of `h`, all `n`, `x ∈ B̄(0, R)` and `t ∈ (0, t₀)`. -/
theorem exists_lqgApprox_ball_le_rpow_of_coneGFF {γ : ℝ} (hγ0 : 0 < γ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun q : ℝ × ℂ => hcirc q.1 q.2) (Ioi 0 ×ˢ univ)) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (hB : ∀ R : ℝ, ∃ C κ r₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < r₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ 1 →
        HarmonicBalls.lqgApprox γ (HarmonicBalls.fieldCircleAverage γ (coneGFFCircle γ hcirc w)) s (ball z r) ≤
          ENNReal.ofReal (C * r ^ κ)) :
    ∀ R : ℝ, 0 < R → ∃ β > (0 : ℝ), ∃ t₀ > (0 : ℝ), ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R,
      ∀ t : ℝ, 0 < t → t < t₀ →
        HarmonicBalls.lqgApprox γ hcirc (HarmonicBalls.dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β) := by
  intro R _
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ → ℝ, G = HarmonicBalls.fieldCircleAverage γ (coneGFFCircle γ hcirc w) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℝ, D = coneCouplingRemainder γ hcirc w := ⟨_, rfl⟩
  have hc0 : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hrem : Continuous D := by
    rw [hD]
    exact continuous_coneCouplingRemainder γ hc0 hw
  have hfun : hcirc = fun r z => G r z + Real.circleAverage D z r := by
    rw [hG, hD]
    refine (coneCircle_eq_addCircleAverage γ hcirc w).trans ?_
    funext r z
    simp only [LatticeProb.Gauss.addCircleAverage]
    rfl
  obtain ⟨C, κ, r₀, hC, hκ, hr₀, hb⟩ := hB R
  have hbG : ∀ z : ℂ, ‖z‖ ≤ R → ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ 1 →
      HarmonicBalls.lqgApprox γ G s (ball z r) ≤ ENNReal.ofReal (C * r ^ κ) := by
    rw [hG]
    exact hb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (R + 2)).bddAbove_image hrem.continuousOn
  have hM' : ∀ y ∈ closedBall (0 : ℂ) (R + 2), D y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  have hK : 0 ≤ Real.exp (γ * M) * C := by positivity
  obtain ⟨s₂, hs₂, hKs⟩ := exists_forall_mul_rpow_le_rpow_half hK hκ
  refine ⟨κ / 2, half_pos hκ, min (min r₀ 1) s₂, lt_min (lt_min hr₀ one_pos) hs₂, ?_⟩
  intro n x hx t ht htt
  have htr : t < r₀ := htt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ht1 : t < 1 := htt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hts : t < s₂ := htt.trans_le (min_le_right _ _)
  have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
  have hd0 : 0 < HarmonicBalls.dyadicScale n := HarmonicBalls.dyadicScale_pos n
  have hd1 : HarmonicBalls.dyadicScale n ≤ 1 := dyadicScale_le_one' n
  have hSL : ∀ y ∈ ball x t, ‖y‖ + HarmonicBalls.dyadicScale n ≤ R + 2 := by
    intro y hy
    have h1 := norm_sub_norm_le y x
    have h2 : ‖y - x‖ < t := mem_ball_iff_norm.1 hy
    linarith
  have hcorr := LatticeProb.LQG.lqgApprox_add_circleAverage_le hγ0.le G hrem hd0.le measurableSet_ball hM' hSL
  have hsplit : HarmonicBalls.lqgApprox γ hcirc (HarmonicBalls.dyadicScale n) (ball x t) =
      LatticeProb.LQG.lqgApprox γ (fun r z => G r z + Real.circleAverage D z r) (HarmonicBalls.dyadicScale n)
        (ball x t) := by
    rw [hfun, harmonicBalls_lqgApprox_eq]
  calc HarmonicBalls.lqgApprox γ hcirc (HarmonicBalls.dyadicScale n) (ball x t)
      ≤ ENNReal.ofReal (Real.exp (γ * M)) *
          HarmonicBalls.lqgApprox γ G (HarmonicBalls.dyadicScale n) (ball x t) := by
        rw [hsplit, harmonicBalls_lqgApprox_eq]
        exact hcorr
    _ ≤ ENNReal.ofReal (Real.exp (γ * M)) * ENNReal.ofReal (C * t ^ κ) := by
        gcongr
        exact hbG x hx' t ht htr _ hd0 hd1
    _ = ENNReal.ofReal (Real.exp (γ * M) * C * t ^ κ) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    _ ≤ ENNReal.ofReal (t ^ (κ / 2)) := ENNReal.ofReal_le_ofReal (hKs t ht hts)

/-- **`ConeApproxBallPowerStmt` holds** for `0 < γ < 2`: in every valid environment, almost surely, for every `R > 0`
there are `β, t₀ > 0` with `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, `x ∈ B̄(0, R)` and `t ∈ (0, t₀)`. -/
theorem coneApproxBallPowerStmt {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : ConeApproxBallPowerStmt γ := by
  intro 𝒮 Ω _ S hS
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨N, -, hN0, hG⟩ := isWholePlaneGFF_coneGFF hS.isQuantumCone
  have hB := hG.ae_singular_continuum_small_ball_power_all_disks hγ0 hγ2
    (lt_lqgQ_self hγ0 hγ2 : γ < HarmonicBalls.lqgQ γ)
  have hgood : ∀ᵐ ω ∂S.P, ω ∉ N ∧
      ContinuousOn (fun q : ℝ × ℂ => S.hcirc ω q.1 q.2) (Ioi 0 ×ˢ univ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hS.isQuantumCone.ae_continuousOn_circle] with ω h1 h2
    exact ⟨h1, h2⟩
  have hgood' := (Measure.quasiMeasurePreserving_fst (μ := S.P) (ν := brownianMotion (0 : ℝ))).ae hgood
  have hprod : ∀ᵐ p ∂(S.P.prod (brownianMotion 0)), ∀ R : ℝ, 0 < R → ∃ β > (0 : ℝ), ∃ t₀ > (0 : ℝ),
      ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R, ∀ t : ℝ, 0 < t → t < t₀ →
        HarmonicBalls.lqgApprox γ (S.hcirc p.1) (HarmonicBalls.dyadicScale n) (ball x t) ≤
          ENNReal.ofReal (t ^ β) := by
    filter_upwards [hB, hgood'] with p hp hpg
    obtain ⟨hpN, hpc⟩ := hpg
    have hoff := circleOff_of_notMem (hcirc := S.hcirc) hpN
    rw [hoff] at hp
    exact exists_lqgApprox_ball_le_rpow_of_coneGFF hγ0 hpc p.2.continuous hp
  filter_upwards [Measure.ae_ae_of_ae_prod hprod] with ω hω
  exact hω.exists.elim fun _ h => h

end MatedCRT
