import MatedCRT.FirstPass.Derived.AreaCellStoppedCurve
import MatedCRT.FirstPass.Derived.AreaCellEndpointStoppedCurve
import MatedCRT.FirstPass.Derived.AreaCellExitClockCurveLaw
import MatedCRT.FirstPass.Derived.AreaCellEndpointExitClockCurveLaw
import MatedCRT.FirstPass.Derived.AreaCellJointExitPoint
import LatticeProb.Walk.CountableStoppedCurveMeasurable

/-! # Measurable stopped-curve laws for area-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The corresponding stopped-curve law with integer-curve measurability supplied. -/
theorem areaCellConfig_finiteRestriction_stopped_curveLaw_measurable
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
    (v : R) {d : ℕ} (pos : ℤ → Euc d) :
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (N.trajectoryLaw A hpos v).map (stoppedPolygonalCurve (pos ∘ f) A) =
        (srwLaw (S.mult ε ω) (f v)).map (stoppedPolygonalCurve pos D) := by
  classical
  exact areaCellConfig_finiteRestriction_stopped_curveLaw S ω h hε hlf R A hretain hpos v pos (LatticeProb.measurable_stoppedPolygonalCurve_countable _ _)

/-- The corresponding stopped-curve law with integer-curve measurability supplied. -/
theorem areaCellConfig_endpoint_stopped_curveLaw_measurable
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
    (N.trajectoryLaw A hpos v).map (stoppedPolygonalCurve (fun x : R =>
        areaCellRepresentative h hε (S.mult ε ω) x.1) A) =
        (srwLaw (S.mult ε ω) (f v)).map (stoppedPolygonalCurve pos D) := by
  classical
  exact areaCellConfig_endpoint_stopped_curveLaw S ω h hε hlf R A hretain hpos v (LatticeProb.measurable_stoppedPolygonalCurve_countable _ _)

/-- The corresponding stopped-curve law with integer-curve measurability supplied. -/
theorem areaCellConfig_finiteRestriction_exitClock_stoppedCurve_jointLaw_measurable
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
    (v : R) {d : ℕ} (pos : ℤ → Euc d) :
    letI : MeasurableSpace ℕ∞ := ENat.instMeasurableSpace
    let e := euclideanCellEquiv h hε
    let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
    let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
    let N := LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
      (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R
    (N.trajectoryLaw A hpos v).map (fun p : ℕ → R =>
        ((id (α := ℕ∞) (exitTime A p)), stoppedPolygonalCurve (pos ∘ f) A p)) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        (vExitTime D p, stoppedPolygonalCurve pos D p)) := by
  classical
  exact areaCellConfig_finiteRestriction_exitClock_stoppedCurve_jointLaw S ω h hε hlf R A hretain hpos v pos (LatticeProb.measurable_stoppedPolygonalCurve_countable _ _)

/-- The corresponding stopped-curve law with integer-curve measurability supplied. -/
theorem areaCellConfig_endpoint_exitClock_stoppedCurve_jointLaw_measurable
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
    letI : MeasurableSpace ℕ∞ := ENat.instMeasurableSpace
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
    (N.trajectoryLaw A hpos v).map (fun p : ℕ → R =>
        ((id (α := ℕ∞) (exitTime A p)), stoppedPolygonalCurve (fun x : R =>
          areaCellRepresentative h hε (S.mult ε ω) x.1) A p)) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        (vExitTime D p, stoppedPolygonalCurve pos D p)) := by
  classical
  exact areaCellConfig_endpoint_exitClock_stoppedCurve_jointLaw S ω h hε hlf R A hretain hpos v (LatticeProb.measurable_stoppedPolygonalCurve_countable _ _)

/-- The corresponding stopped-curve law with integer-curve measurability supplied. -/
theorem areaCellConfig_endpoint_exitClock_curve_exitPoint_jointLaw_measurable
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
    letI : MeasurableSpace ℕ∞ := ENat.instMeasurableSpace
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
    (N.trajectoryLaw A hpos v).map (fun p : ℕ → R =>
        (id (α := ℕ∞) (exitTime A p),
          stoppedPolygonalCurve (fun x : R => areaCellRepresentative h hε (S.mult ε ω) x.1) A p,
          areaCellRepresentative h hε (S.mult ε ω) (p ((exitTime A p).untopD 0)).1)) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        (vExitTime D p, stoppedPolygonalCurve pos D p, pos (p ((vExitTime D p).untopD 0)))) := by
  classical
  exact areaCellConfig_endpoint_exitClock_curve_exitPoint_jointLaw S ω h hε hlf R A hretain hpos v (LatticeProb.measurable_stoppedPolygonalCurve_countable _ _)

end MatedCRT
