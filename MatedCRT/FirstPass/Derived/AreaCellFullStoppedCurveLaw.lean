import MatedCRT.FirstPass.Derived.AreaCellCurveLawMeasurable
import LatticeProb.Walk.StoppedCurveRelabel

/-! # Stopped polygonal curves on the full area-cell carrier -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- Relabelling a finite restricted trajectory by its ambient cells preserves
its stopped polygonal curve law and identifies it with the integer walk law. -/
theorem areaCellConfig_fullCell_stopped_curveLaw
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
    (v : R) {d : ℕ} (pos : (areaCellConfig h hε (S.mult ε ω)).cells → Euc d)
    (B : Set (areaCellConfig h hε (S.mult ε ω)).cells)
    (hB : (fun x : R => (x : (areaCellConfig h hε (S.mult ε ω)).cells)) ⁻¹' B = A) :
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    ((N.trajectoryLaw A hpos v).map (fun p n =>
      (p n : (areaCellConfig h hε (S.mult ε ω)).cells))).map
        (stoppedPolygonalCurve pos B) =
      (srwLaw (S.mult ε ω) (f v)).map (stoppedPolygonalCurve (pos ∘ e) D) := by
  classical
  dsimp only
  let e := euclideanCellEquiv h hε
  let _ : Countable (areaCellConfig h hε (S.mult ε ω)).cells := Countable.of_equiv ℤ e
  rw [← LatticeProb.map_stoppedPolygonalCurve_relabel]
  rw [hB]
  simpa only [Function.comp_def, e, Equiv.apply_symm_apply] using
    (areaCellConfig_finiteRestriction_stopped_curveLaw_measurable
      S ω h hε hlf R A hretain hpos v (pos ∘ e))

end MatedCRT
