import MatedCRT.FirstPass.Derived.AreaCellStoppedCurve
import MatedCRT.FirstPass.Derived.AreaCellRepresentative

/-! # Stopped curves through the endpoints of area cells -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The stopped curve through cell endpoint representatives has the same law
as the stopped curve through the corresponding embedded integer vertices. -/
theorem areaCellConfig_endpoint_stopped_curveLaw
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
    let pos : ℤ → Euc 2 := fun k =>
      Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) k)
    Measurable (stoppedPolygonalCurve pos D) →
      (N.trajectoryLaw A hpos v).map (stoppedPolygonalCurve (fun x : R =>
        areaCellRepresentative h hε (S.mult ε ω) x.1) A) =
        (srwLaw (S.mult ε ω) (f v)).map (stoppedPolygonalCurve pos D) := by
  classical
  dsimp only
  intro hmeas
  simpa only [areaCellRepresentative, Function.comp_def] using
    (areaCellConfig_finiteRestriction_stopped_curveLaw S ω h hε hlf R A
      hretain hpos v
      (fun k : ℤ => Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) k))
      hmeas)

end MatedCRT
