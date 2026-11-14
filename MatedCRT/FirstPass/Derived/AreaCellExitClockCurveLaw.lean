import MatedCRT.FirstPass.Derived.AreaCellStoppedObservable
import MatedCRT.FirstPass.Derived.IntegerStoppedCurve

/-! # Joint exit clocks and stopped curves of finite curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The exit clock and stopped polygonal curve have the same joint law for
a finite cell walk and the corresponding integer walk. -/
theorem areaCellConfig_finiteRestriction_exitClock_stoppedCurve_jointLaw
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
    Measurable (stoppedPolygonalCurve pos D) →
      (N.trajectoryLaw A hpos v).map (fun p : ℕ → R =>
        ((id (α := ℕ∞) (exitTime A p)), stoppedPolygonalCurve (pos ∘ f) A p)) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        (vExitTime D p, stoppedPolygonalCurve pos D p)) := by
  classical
  dsimp only
  intro hmeas
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
  have hA : f ⁻¹' D = A := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : x = y := Subtype.ext (by simpa [e, f] using heq)
      simpa [hxy] using hy
    · intro hx
      exact ⟨x, hx, by simp [e, f]⟩
  have hclock (p : ℕ → R) :
      vExitTime D (fun n => f (p n)) = exitTime A p := by
    rw [← integer_exitTime_eq_vExitTime, ← hA]
    rfl
  have hcurve (p : ℕ → R) :
      stoppedPolygonalCurve (pos ∘ f) A p =
        stoppedPolygonalCurve pos D (fun n => f (p n)) := by
    rw [← hA]
    rfl
  have hstop (p : ℕ → ℤ) :
      (vExitTime D (stoppedPath D p), stoppedPolygonalCurve pos D (stoppedPath D p)) =
      (vExitTime D p, stoppedPolygonalCurve pos D p) := by
    rw [vExitTime_stoppedPath, stoppedPolygonalCurve_stoppedPath]
  have hlaw := areaCellConfig_finiteRestriction_stoppingInvariant_observableLaw
    S ω h hε hlf R A hretain hpos v
      (fun p => (vExitTime D p, stoppedPolygonalCurve pos D p))
      ((measurable_vExitTime D).prodMk hmeas) hstop
  have heq (p : ℕ → R) :
      (id (α := ℕ∞) (exitTime A p), stoppedPolygonalCurve (pos ∘ f) A p) =
      (vExitTime D (fun n => f (p n)), stoppedPolygonalCurve pos D (fun n => f (p n))) := by
    simp only [id_eq, hclock, hcurve]
  rw [show (fun p : ℕ → R =>
      (id (α := ℕ∞) (exitTime A p), stoppedPolygonalCurve (pos ∘ f) A p)) =
      (fun p => (vExitTime D (fun n => f (p n)),
        stoppedPolygonalCurve pos D (fun n => f (p n)))) from funext heq]
  exact hlaw

end MatedCRT
