import MatedCRT.FirstPass.Derived.AreaCellEndpointExitClockCurveLaw
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties

/-! # Joint exit clocks, curves, and exit points of area-cell walks -/

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The exit clock, stopped curve, and exit representative have the same
joint law for the finite area-cell walk and the embedded integer walk. -/
theorem areaCellConfig_endpoint_exitClock_curve_exitPoint_jointLaw
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
    Measurable (stoppedPolygonalCurve pos D) →
      (N.trajectoryLaw A hpos v).map (fun p : ℕ → R =>
        (id (α := ℕ∞) (exitTime A p),
          stoppedPolygonalCurve (fun x : R => areaCellRepresentative h hε (S.mult ε ω) x.1) A p,
          areaCellRepresentative h hε (S.mult ε ω) (p ((exitTime A p).untopD 0)).1)) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        (vExitTime D p, stoppedPolygonalCurve pos D p, pos (p ((vExitTime D p).untopD 0)))) := by
  classical
  dsimp only
  intro hmeas
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
  let pos : ℤ → Euc 2 := fun k => Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) k)
  let rep : R → Euc 2 := fun x => areaCellRepresentative h hε (S.mult ε ω) x.1
  letI : MeasurableSpace ℕ∞ := ENat.instMeasurableSpace
  have hfinite : Measurable (stoppedPolygonalCurve rep A) :=
    measurable_stoppedPolygonalCurve rep A
  have htfinite : Measurable (fun p : ℕ → R => id (α := ℕ∞) (exitTime A p)) := by
    have heq : exitTime A = vExitTime D ∘ (fun p : ℕ → R => fun n => f (p n)) := by
      funext p
      change exitTime A p = vExitTime D (fun n => f (p n))
      rw [← integer_exitTime_eq_vExitTime]
      have hA : f ⁻¹' D = A := by
        ext x
        constructor
        · rintro ⟨y, hy, heq⟩
          have hxy : x = y := Subtype.ext (by simpa [e, f] using heq)
          simpa [hxy] using hy
        · intro hx
          exact ⟨x, hx, by simp [e, f]⟩
      change exitTime A p = exitTime D (fun n => f (p n))
      rw [← hA]
      rfl
    rw [heq]
    exact (measurable_vExitTime D).comp (Measurable.of_eval fun n =>
      (measurable_of_countable f).comp (measurable_pi_apply n))
  have htint : Measurable (vExitTime D) := measurable_vExitTime D
  have hg : Measurable (fun q : ℕ∞ × CurveSpace 2 =>
      (q.1, q.2, CurveSpace.endPoint q.2)) :=
    measurable_fst.prodMk (measurable_snd.prodMk
      (CurveSpace.continuous_endPoint.measurable.comp measurable_snd))
  have hlaw := areaCellConfig_endpoint_exitClock_stoppedCurve_jointLaw
    S ω h hε hlf R A hretain hpos v hmeas
  have hmapped := congrArg (fun m : Measure (ℕ∞ × CurveSpace 2) =>
    m.map (fun q => (q.1, q.2, CurveSpace.endPoint q.2))) hlaw
  rw [Measure.map_map hg (htfinite.prodMk hfinite),
    Measure.map_map hg (htint.prodMk hmeas)] at hmapped
  simpa only [Function.comp_def, stoppedPolygonalCurve_endPoint,
    integer_exitTime_eq_vExitTime, rep, pos, D, f, e] using hmapped

end MatedCRT
