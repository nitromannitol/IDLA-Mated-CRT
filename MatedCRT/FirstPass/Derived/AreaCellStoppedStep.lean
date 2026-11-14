import MatedCRT.FirstPass.Derived.AreaCellFiniteStep

/-! # Stopped steps of the curve-cell walk -/

set_option autoImplicit false
set_option quotPrecheck false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS
open BouRabeeGwynne.FiniteConductanceNetwork

variable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
variable {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
variable {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))

local notation "H" => areaCellConfig h hε (S.mult ε ω)
local notation "cH" => (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) => (areaCellConfig h hε (S.mult ε ω)).c v w)
local notation "symmC" => areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω)
local notation "nonnegC" => areaCellConfig_conductance_nonneg h hε (S.mult ε ω)
local notation "loopC" => areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)

include hlf

open Classical in
/-- The stopped finite-restriction step agrees with the relabelled integer step
at active cells and is absorbing at all other cells in the region. -/
theorem areaCellConfig_finiteRestriction_stoppedStepPMF_map
    (R : Set (H).cells) [Fintype R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → cH v w = 0)
    (hpos : ∀ v ∈ A,
      0 < (LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).totalConductance v)
    (a : ℤ) (ha : euclideanCellEquiv h hε a ∈ R) :
    ((LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).stepPMF A hpos
      ⟨euclideanCellEquiv h hε a, ha⟩).map Subtype.val =
      if (⟨euclideanCellEquiv h hε a, ha⟩ : R) ∈ A then
        (srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε)
      else PMF.pure (euclideanCellEquiv h hε a) := by
  classical
  by_cases hactive : (⟨euclideanCellEquiv h hε a, ha⟩ : R) ∈ A
  · rw [ite_eq_left hactive]
    exact areaCellConfig_finiteRestriction_stepPMF_map S ω h hε hlf R A hretain hpos a ha hactive
  · rw [ite_eq_right hactive,
      (LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).stepPMF_of_not_mem
        A hpos hactive, PMF.pure_map]
    rfl

end MatedCRT
