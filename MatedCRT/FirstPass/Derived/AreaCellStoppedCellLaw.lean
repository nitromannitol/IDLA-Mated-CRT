import MatedCRT.FirstPass.Derived.AreaCellStoppedLaw

/-! # Cell-valued stopped trajectories of finite curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The finite cell trajectory has the law of the integer walk stopped on
leaving the active labels and then relabelled by cells. -/
theorem areaCellConfig_finiteRestriction_stopped_cell_trajectoryLaw
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
    (N.trajectoryLaw A hpos v).map (fun p n => (p n : (areaCellConfig h hε (S.mult ε ω)).cells)) =
      ((srwLaw (S.mult ε ω) (f v)).map (stoppedPath D)).map (fun p n => e (p n)) := by
  classical
  dsimp only
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  have hf : Measurable (fun p : ℕ → R => fun n => f (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_finite f).comp (measurable_pi_apply n)
  have he : Measurable (fun p : ℕ → ℤ => fun n => e (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_countable e).comp (measurable_pi_apply n)
  have hmap := congrArg (fun M => Measure.map (fun p n => e (p n)) M)
    (areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map S ω h hε hlf R A hretain hpos v)
  rw [Measure.map_map he hf] at hmap
  simpa only [Function.comp_def, f, e, Equiv.apply_symm_apply] using hmap

end MatedCRT
