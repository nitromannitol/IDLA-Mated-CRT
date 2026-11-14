import MatedCRT.FirstPass.Derived.AreaCellStoppedLaw

/-! # Finite-region independence of stopped area-cell walks -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace MatedCRT

open MeasureTheory ProbabilityTheory
open MatedCRT.ExitCouplingGlue MatedCRT.ExitDecomposition
open BouRabeeGwynne.FiniteConductanceNetwork

/-- Finite restrictions with the same active integer labels and initial label
have the same labelled stopped trajectory law. -/
theorem areaCellConfig_finiteRestriction_stopped_trajectoryLaw_eq
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    {μ : Measure ℂ} (h : IsAreaParametrized μ (S.η ω))
    {ε : ℝ} (hε : 0 < ε) (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (R1 : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R1]
    [MeasurableSpace R1] [MeasurableSingletonClass R1] (A1 : Set R1)
    (hretain1 : ∀ v ∈ A1, ∀ w, w ∉ R1 →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos1 : ∀ v ∈ A1, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R1).totalConductance v)
    (v1 : R1)
    (R2 : Set (areaCellConfig h hε (S.mult ε ω)).cells) [Fintype R2]
    [MeasurableSpace R2] [MeasurableSingletonClass R2] (A2 : Set R2)
    (hretain2 : ∀ v ∈ A2, ∀ w, w ∉ R2 →
      (areaCellConfig h hε (S.mult ε ω)).c v w = 0)
    (hpos2 : ∀ v ∈ A2, 0 < (LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R2).totalConductance v)
    (v2 : R2)
    (hstart : (euclideanCellEquiv h hε).symm (v1 : (areaCellConfig h hε (S.mult ε ω)).cells) =
      (euclideanCellEquiv h hε).symm (v2 : (areaCellConfig h hε (S.mult ε ω)).cells))
    (hactive : {a : ℤ | ∃ x ∈ A1, euclideanCellEquiv h hε a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)} =
      {a : ℤ | ∃ x ∈ A2, euclideanCellEquiv h hε a = (x : (areaCellConfig h hε (S.mult ε ω)).cells)}) :
    ((LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R1).trajectoryLaw A1 hpos1 v1).map
      (fun p n => (euclideanCellEquiv h hε).symm (p n : (areaCellConfig h hε (S.mult ε ω)).cells)) =
    ((LatticeProb.finiteConductanceRestriction
      (fun (v w : (areaCellConfig h hε (S.mult ε ω)).cells) =>
        (areaCellConfig h hε (S.mult ε ω)).c v w)
      (areaCellConfig_conductance_symm h hε (S.mult ε ω) (S.mult_symm ε ω))
      (areaCellConfig_conductance_nonneg h hε (S.mult ε ω))
      (areaCellConfig_conductance_self h hε (S.mult ε ω) (S.mult_self ε ω)) R2).trajectoryLaw A2 hpos2 v2).map
      (fun p n => (euclideanCellEquiv h hε).symm (p n : (areaCellConfig h hε (S.mult ε ω)).cells)) := by
  rw [areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map S ω h hε hlf
      R1 A1 hretain1 hpos1 v1,
    areaCellConfig_finiteRestriction_stopped_trajectoryLaw_map S ω h hε hlf
      R2 A2 hretain2 hpos2 v2]
  dsimp only
  rw [hstart, hactive]

end MatedCRT
