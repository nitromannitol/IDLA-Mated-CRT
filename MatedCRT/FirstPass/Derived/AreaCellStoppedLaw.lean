import MatedCRT.FirstPass.Derived.AreaCellStoppedTrajectory

/-! # Stopped trajectories of finite curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- A finite cell walk, relabelled by integers, has the law of the integer walk
stopped on leaving the active cells. -/
theorem areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos : ∀ v ∈ A, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R).totalConductance v)
    (v : R) :
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (N.trajectoryLaw A hpos v).map (fun p n => f (p n)) =
      (srwLaw (S.mult ε ω) (f v)).map (stoppedPath D) := by
  classical
  dsimp only
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
  let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
  change (N.trajectoryLaw A hpos v).map (fun p n => f (p n)) =
    (srwLaw (S.mult ε ω) (f v)).map (stoppedPath D)
  have hm : Measurable (fun p : ℕ → R => fun n => f (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_finite f).comp (measurable_pi_apply n)
  have habs : ∀ᵐ p ∂N.trajectoryLaw A hpos v,
      IsAbsorbedPath D (fun n => f (p n)) := by
    filter_upwards [N.trajectoryLaw_ae_absorbed A hpos v] with p hp
    intro n hn
    apply congrArg f
    apply hp n
    intro hmem
    apply hn
    exact ⟨p n, hmem, by simp [f, e]⟩
  have hfixed : (N.trajectoryLaw A hpos v).map (fun p n => f (p n)) =
      ((N.trajectoryLaw A hpos v).map (fun p n => f (p n))).map (stoppedPath D) := by
    rw [Measure.map_map (measurable_stoppedPath D) hm]
    apply Measure.map_congr
    filter_upwards [habs] with p hp
    exact (stoppedPath_eq_self_of_absorbed D _ hp).symm
  rw [hfixed, areaCellConfig_finiteRestriction_trajectoryLaw_map S ω h hε hlf R A hretain hpos v]
  exact absorbedSrwKernel_stopped_trajectoryLaw (S.mult ε ω) D (f v)

end MatedCRT
