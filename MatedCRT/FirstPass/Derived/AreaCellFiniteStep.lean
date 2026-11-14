import MatedCRT.FirstPass.Derived.AreaCellFiniteNeighbors
import MatedCRT.FirstPass.Derived.AreaCellStepPMF
import LatticeProb.Prob.FiniteConductanceStepLaw

/-! # Finite restrictions of the curve-cell walk -/

set_option autoImplicit false
set_option quotPrecheck false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

variable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
variable {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
variable {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))

local notation "H" => areaCellConfig h hε (S.mult ε ω)
local notation "cH" => (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) => (areaCellConfig h hε (S.mult ε ω)).c v w)
local notation "symmC" => areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω)
local notation "nonnegC" => areaCellConfig_conductance_nonneg h hε (S.mult ε ω)
local notation "loopC" => areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)
include hlf

/-- Retaining all neighbors of active cells preserves positive conductance. -/
theorem areaCellConfig_finiteRestriction_total_pos
    (R : Set (H).cells) [Fintype R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → cH v w = 0)
    (v : R) (hv : v ∈ A) :
    0 < (LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).totalConductance v := by
  rw [LatticeProb.finiteConductanceRestriction_total cH symmC nonnegC loopC R v (hretain v hv)]
  exact areaCellConfig_pi_pos S ω h hε hlf v

/-- At an active cell, a finite restriction has the same one-step law as the
integer walk relabelled by curve cells, provided every neighbor is retained. -/
theorem areaCellConfig_finiteRestriction_stepPMF_map
    (R : Set (H).cells) [Fintype R] (A : Set R)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → cH v w = 0)
    (hpos : ∀ v ∈ A,
      0 < (LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).totalConductance v)
    (a : ℤ) (ha : euclideanCellEquiv h hε a ∈ R)
    (hactive : (⟨euclideanCellEquiv h hε a, ha⟩ : R) ∈ A) :
    ((LatticeProb.finiteConductanceRestriction cH symmC nonnegC loopC R).stepPMF A hpos
      ⟨euclideanCellEquiv h hε a, ha⟩).map Subtype.val =
      (srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε) := by
  refine LatticeProb.finiteConductanceRestriction_stepPMF_map_eq cH symmC nonnegC loopC R A hpos
    ⟨euclideanCellEquiv h hε a, ha⟩ hactive (hretain _ hactive)
    ((srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε)) ?_ ?_
  · intro w
    change ((srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε)) (w : (H).cells) = _
    simpa only [CellConfig.transition, CellConfig.pi] using
      areaCellConfig_srwStep_toPMF_map_apply S ω h hε hlf a w
  · intro w hw
    change ((srwStep (S.mult ε ω) a).toPMF.map (euclideanCellEquiv h hε)) w = 0
    rw [areaCellConfig_srwStep_toPMF_map_apply S ω h hε hlf a w]
    simp only [CellConfig.transition, hretain _ hactive w hw, zero_div, ENNReal.ofReal_zero]

end MatedCRT
