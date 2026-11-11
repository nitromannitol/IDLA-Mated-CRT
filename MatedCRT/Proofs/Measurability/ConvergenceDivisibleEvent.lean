import MatedCRT.Proofs.Sec4.ConvergenceDivisible.FromInputs
import MatedCRT.Proofs.Measurability.BoundaryLayer

/-!
# `ConvergenceDivisibleEventMeasurableStep` of Theorem 4.1 (finding F8)

`ConvergenceDivisibleEventMeasurableStep` reduces to Lemma 2.7 and the null measurability of the exit events
`{t < T_ρ}` of the harmonic ball family (`convergenceDivisibleEventMeasurable_of_local_exit_inputs`,
MatedCRT/Proofs/Sec4/ConvergenceDivisible/FromInputs.lean). The latter follows from `ConeFamilyAEMeasurableStep` and
Lemma 2.4 (`MatedCRTEnv.IsValid.nullMeasurableSet_lt_clusterExitTime`, MatedCRT/Proofs/Measurability/BoundaryLayer.lean).
-/

namespace MatedCRT

/-- **`ConvergenceDivisibleEventMeasurableStep`** from Lemma 2.7, Lemma 2.4 and the measurability of the harmonic
balls of the cone (`ConeFamilyAEMeasurableStep`). -/
theorem convergenceDivisibleEventMeasurableStep_of_coneFamilyAEMeasurable (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_local_exit_inputs 𝒮 h27
    fun _ hγ hγ2 _ hρ hρ1 _ _ _ hS _ hΛ _ ht =>
      hS.nullMeasurableSet_lt_clusterExitTime hγ hγ2 hfam h24 hρ hρ1 hΛ ht

/-- **Theorem 4.1** from Proposition 4.8, Proposition 4.6, Lemma 2.7, Lemma 2.4 and the measurability of the harmonic
balls of the cone (`ConeFamilyAEMeasurableStep`). -/
theorem convergenceDivisible_of_coneFamilyAEMeasurable (𝒮 : SpaceFillingSLEModel)
    (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_local_exit_inputs 𝒮 h48 h46 h27
    fun _ hγ hγ2 _ hρ hρ1 _ _ _ hS _ hΛ _ ht =>
      hS.nullMeasurableSet_lt_clusterExitTime hγ hγ2 hfam h24 hρ hρ1 hΛ ht

end MatedCRT
