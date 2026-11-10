import MatedCRT.FirstPass.S5c.ClusterOpen
import MatedCRT.FirstPass.S5c.StoppedGeometry
import MatedCRT.FirstPass.S5d.StoppedSteps
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-!
# First pass: deterministic steps of the surplus maximum outside the killing set (task fp-S5f-5-1-max-outside, z10)

Pointwise facts used by `stoppedMaxOutside_of_steps` (MatedCRT/FirstPass/S5f.lean):

* `odometer_eq_zero_of_notMem_stopped_Lambda`: on `{t < T}`, the continuum odometer `v + t G_{B_ρ}(0,·)` vanishes at every
  point of `B_ρ` outside the harmonic ball `Λ_t` (Armitage–Gardiner, the obstacle problem of Harmonic-Balls-LQG).
  Route: `Λ_t = interior (closure (cluster))` (Obstacle characterization), `cluster` is open (`isOpen_cluster_of_stopped`,
  which uses the frozen pole continuity `FrozenGreenDiscPole`), so `cluster ⊆ Λ_t`; then `odometer_eq_zero_of_notMem_cluster`.
* `rescale_stoppedOdometer_eq`: the rescaled stopped odometer is the rescaled least supersolution plus `t` times the rescaled
  discrete Green function `ε⁻¹ g^ε_{B_ρ}(0, ·)` (linearity of `rescale`, Defs/Map.lean:200).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Surplus vanishes off the harmonic ball.** On `{t < T}` (`T = clusterExitTime Λ ρ`), for `x ∈ B_ρ` with `x ∉ Λ_t`, the
odometer `u_{B_ρ;0}(t)(x) = v_{B_ρ;0}(t)(x) + t G_{B_ρ}(0,x)` vanishes. -/
theorem odometer_eq_zero_of_notMem_stopped_Lambda {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hG : MatedCRT.FrozenGreenDiscPole) (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) (hxΛ : x ∉ Λ t) :
    odometer μ ρ 0 t x = 0 := by
  have hsub : Λ t ⊆ ball (0 : ℂ) (ρ / 3) := MatedCRT.S5c.subset_ball_of_le_clusterExitTime hfam hT ht le_rfl
  have hEq : Λ t = interior (closure (cluster μ ρ 0 t)) :=
    (hfam.2.2 t (ρ / 3) ht (div_pos hρ (by norm_num)) hsub ρ (by linarith)).1
  have hopen : IsOpen (cluster μ ρ 0 t) := MatedCRT.isOpen_cluster_of_stopped hG hfam hρ ht hT
  have hxc : x ∉ cluster μ ρ 0 t := by
    intro hc
    apply hxΛ
    rw [hEq]
    exact hopen.subset_interior_iff.2 subset_closure hc
  exact odometer_eq_zero_of_notMem_cluster ht.le hx hxc

/-- **Rescaling the stopped odometer.** At a point `x` whose vertex `a = a^ε_x` lies in the closed ball's vertex set,
`rescale (m_ε) ε η u_stopped x = rescale (m_ε) ε η w̃ x + t · (m_ε⁻¹ · ε⁻¹ · g^ε_{B_ρ}(0, a))`, where
`u_stopped = w̃ - matedObstacle = w̃ + (t/ε) g` (Defs/Sandpile.lean:75, stoppedOdometer Defs/Sandpile.lean:93). -/
theorem rescale_stoppedOdometer_eq (m : ℤ → ℤ → ℕ) (mε ε t ρ : ℝ) (η : ℝ → ℂ) (x : ℂ)
    (hx : vertexOf ε η x ∈ cellVertices ε η (closedBall (0 : ℂ) ρ)) :
    rescale mε ε η (stoppedOdometer m ε η ρ t) x =
      rescale mε ε η (matedLeastSupersolution m ε η ρ t) x +
        t * (mε⁻¹ * (ε⁻¹ * greenKernel m (ballInterior ε η ρ) 0 (vertexOf ε η x))) := by
  unfold rescale stoppedOdometer matedObstacle
  split_ifs
  ring

/-- **Cluster from positive surplus.** A vertex with positive stopped odometer lies in the discrete cluster, hence in the
cells meeting `B_ρ` (Proofs/Sec7/OdometerBoundMass/StoppedOdometer.lean). -/
theorem cell_meets_ball_of_stoppedOdometer_pos {m : ℤ → ℤ → ℕ} {ε t ρ : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (ht : 0 < t)
    {a : ℤ} (h : 0 < stoppedOdometer m ε η ρ t a) : a ∈ cellVertices ε η (ball (0 : ℂ) ρ) := by
  have hcl := MatedCRT.Sec7.mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht h
  unfold matedDiscreteCluster discreteCluster at hcl
  exact hcl.1

end MatedCRT
