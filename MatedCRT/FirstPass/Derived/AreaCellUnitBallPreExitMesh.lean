import MatedCRT.FirstPass.Derived.AreaCellUnitBallBufferedMesh
import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import MatedCRT.FirstPass.Derived.AreaCellFiniteStep
import LatticeProb.Walk.CellNetworkLocalPreExitMesh

/-! # Pre-exit mesh of finite area-cell walks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne LatticeProb
open scoped NNReal

/-- A unit-ball diameter estimate bounds each step before the representative
exits the target, for a walk stopped on an arbitrary finite ambient region. -/
theorem areaCellConfig_trajectoryLaw_ae_preExit_step_le_unit_ball_mesh
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (h : IsAreaParametrized (S.μ ω) (S.η ω))
    {ε : ℝ} (hε : 0 < ε)
    (hc : (areaCellConfig h hε (S.mult ε ω)).IsCellConfiguration)
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells)
    [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) {a : ℝ} (ha : 0 < a) (Uc : Set ℂ) (r d : ℝ) (hd : 0 ≤ d)
    (hU : Uc ⊆ ball 0 r) (hmargin : r + a * d ≤ a)
    (hdiam : ∀ k, (cell ε (S.η ω) k ∩ ball 0 1).Nonempty →
      diam (cell ε (S.η ω) k) ≤ d) :
    ∀ᵐ ξ ∂(finiteConductanceRestriction
      (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).trajectoryLaw A hA v,
      ∀ j : ℕ,
        (j : WithTop ℕ) < FiniteConductanceNetwork.exitTime
          ((fun x : R => a • areaCellRepresentative h hε (S.mult ε ω) x) ⁻¹'
            (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc)) ξ →
        dist (a • areaCellRepresentative h hε (S.mult ε ω) (ξ (j + 1)))
          (a • areaCellRepresentative h hε (S.mult ε ω) (ξ j)) ≤ 2 * (a * d) := by
  obtain ⟨hbuffer, hmesh⟩ := areaCellConfig_unit_ball_buffer_and_scaled_local_mesh
    h hε (S.mult ε ω) ha Uc r d hU hmargin hdiam
  exact CellConfigInterpolation.trajectoryLaw_ae_preExit_step_le_local_mesh
    (areaCellConfig h hε (S.mult ε ω)) hc
    (areaCellRepresentative h hε (S.mult ε ω))
    (areaCellRepresentative_mem h hε (S.mult ε ω)) (fun x : R => x.1)
    (finiteConductanceRestriction
      (fun v w : (areaCellConfig h hε (S.mult ε ω)).cells =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R)
    (fun _ _ hedge => hedge) A hA v id isometry_id
    (Complex.orthonormalBasisOneI.repr.symm ⁻¹' Uc) (ball 0 a) a d ha.le hd hbuffer hmesh

end MatedCRT
end
