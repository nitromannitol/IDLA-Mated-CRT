import MatedCRT.FirstPass.Derived.AreaCellHarmonicExitLabel
import MatedCRT.FirstPass.Derived.AreaCellRepresentative

/-! # Harmonic measure at curve-cell exit points -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The embedded exit-point law is harmonic measure at the cell representatives. -/
theorem areaCellConfig_discreteHarmonicMeasure_map_representative
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
    (N.discreteHarmonicMeasure A hpos v).map
        (fun x : R => areaCellRepresentative h hε (S.mult ε ω) x.1) =
      (srwLaw (S.mult ε ω) (f v)).map (fun p =>
        Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) (vExitPosition D p))) := by
  classical
  dsimp only
  let e := euclideanCellEquiv h hε
  let f : R → ℤ := fun x => e.symm (x : (areaCellConfig h hε (S.mult ε ω)).cells)
  let D : Set ℤ := {a | ∃ x ∈ A, e a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}
  let pos : ℤ → Euc 2 := fun k =>
    Complex.orthonormalBasisOneI.repr (vertexPoint ε (S.η ω) k)
  have hlaw := areaCellConfig_discreteHarmonicMeasure_map_label S ω h hε hlf R A hretain hpos v
  have hmap := congrArg (fun M : Measure ℤ => M.map pos) hlaw
  rw [Measure.map_map (measurable_of_countable pos) (measurable_of_finite f),
    Measure.map_map (measurable_of_countable pos) (measurable_vExitPosition D)] at hmap
  simpa only [pos, f, e, areaCellRepresentative, Function.comp_def] using hmap

end MatedCRT
