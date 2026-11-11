import MatedCRT.Proofs.IDLA.WalkerLawMeasurable

/-!
# Joint-law bridge for the IDLA probability (q4, task fp-S1d2, operator note 21:14 UTC, S5)

The operator note asked for the bridge `idlaProb ε E = joint law of (environment, walkers) at E`. In the Lean
development `MatedCRTEnv.idlaProb` is already defined as the joint measure `MatedCRTEnv.idlaJointMeasure`
(Defs/Setting.lean), and for a valid environment that measure is the joint law `IsValid.idlaJointLaw`
(Proofs/IDLA/WalkerLawMeasurable.lean). The bridge therefore holds for every event, with no measurability of the event:
it is `idlaJointMeasure_eq` after unfolding `idlaProb`.
-/

namespace MatedCRT

open MeasureTheory

/-- The annealed IDLA probability of any event `E` of environment and walkers equals the joint law at `E`
(valid environment). -/
theorem MatedCRTEnv.IsValid.idlaProb_eq_joint_law {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ε : ℝ) (E : Set (Ω × (ℕ → ℕ → ℤ))) :
    S.idlaProb ε E = hS.idlaJointLaw ε E := by
  rw [MatedCRTEnv.idlaProb, MatedCRTEnv.IsValid.idlaJointMeasure_eq hS]

end MatedCRT
