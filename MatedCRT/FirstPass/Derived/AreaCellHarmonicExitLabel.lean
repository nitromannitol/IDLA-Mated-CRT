import MatedCRT.FirstPass.Derived.AreaCellStoppedObservable
import MatedCRT.FirstPass.Derived.IntegerStoppedCurve
import LatticeProb.Bonanno.BouRabeeGwynne.DiscreteHarmonicMeasure

/-! # Harmonic measure of finite curve-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory BouRabeeGwynne
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- The exit vertex of a finite cell walk has the law of the integer walk's
exit position when both are expressed in integer labels. -/
theorem areaCellConfig_discreteHarmonicMeasure_map_label
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
    (N.discreteHarmonicMeasure A hpos v).map f =
      (srwLaw (S.mult ε ω) (f v)).map (vExitPosition D) := by
  classical
  dsimp only
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
  have hstop (p : ℕ → ℤ) : vExitPosition D (stoppedPath D p) = vExitPosition D p := by
    by_cases ht : vExitTime D p = ⊤
    · rw [stoppedPath_of_top ht]
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 ht
      have hk' : vExitTime D p = (k : ℕ∞) := hk.symm
      simp only [vExitPosition, vExitTime_stoppedPath, hk', ENat.toNat_natCast]
      exact stoppedPath_of_le hk' le_rfl
  have hlabel (p : ℕ → R) : vExitPosition D (fun n => f (p n)) = f (exitVertex A p) := by
    have htime : exitTime D (fun n => f (p n)) = exitTime A p := by
      rw [← hA]
      rfl
    simp only [vExitPosition, ← integer_exitTime_eq_vExitTime, htime, exitVertex]
    rfl
  have hlaw := areaCellConfig_finiteRestriction_stoppingInvariant_observableLaw
    S ω h hε hlf R A hretain hpos v (vExitPosition D) (measurable_vExitPosition D) hstop
  rw [discreteHarmonicMeasure, Measure.map_map (measurable_of_finite f) (measurable_exitVertex A)]
  convert hlaw using 1
  congr 1
  funext p
  exact (hlabel p).symm

end MatedCRT
