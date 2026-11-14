import MatedCRT.FirstPass.Derived.AreaCellStoppedLaw

/-! # Stopping-invariant observables of finite curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- A measurable observable unchanged by stopping has the same law for the
finite cell walk and the integer walk, after labelling cells by integers. -/
theorem areaCellConfig_finiteRestriction_stoppingInvariant_observableLaw
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
    (v : R) {T : Type*} [MeasurableSpace T] (F : (ℕ → ℤ) → T)
    (hF : Measurable F) :
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (∀ p, F (stoppedPath D p) = F p) →
      (N.trajectoryLaw A hpos v).map (fun p => F (fun n => f (p n))) =
        (srwLaw (S.mult ε ω) (f v)).map F := by
  classical
  dsimp only
  intro hstop
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
  let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
  change (N.trajectoryLaw A hpos v).map (fun p => F (fun n => f (p n))) =
    (srwLaw (S.mult ε ω) (f v)).map F
  have hf : Measurable (fun p : ℕ → R => fun n => f (p n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_of_finite f).comp (measurable_pi_apply n)
  change (N.trajectoryLaw A hpos v).map (F ∘ (fun p n => f (p n))) =
    (srwLaw (S.mult ε ω) (f v)).map F
  rw [← Measure.map_map hF hf,
    areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map S ω h hε hlf R A hretain hpos v,
    Measure.map_map hF (measurable_stoppedPath D)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall hstop

end MatedCRT
