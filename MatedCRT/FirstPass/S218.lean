import MatedCRT.FirstPass.S3c.ExitTimeCore

/-!
# FIRST PASS 2.18: exit-time upper bound from BG20 Proposition 5.1

`exitTimeUpperBound_of_bg20Prop51_volumeGrowth` derives `ExitTimeUpperBoundStmt 𝒮` (Draft Lemma 2.18,
`lemma:exit-time-upper-bound`) from the mass-restricted first moment `BG20Prop51 𝒮` (BG20 Proposition 5.1,
FIRST-PASS FROZEN, `MatedCRT/FirstPass/Frozen/S3c.lean`) and the volume growth `VolumeGrowthStmt`
(Lemma 2.7, BG20 Lemma A.1).

The derivation is already in the repository: `MatedCRT.exitTimeUpperBoundStmt_core`
(`MatedCRT/FirstPass/S3c/ExitTimeCore.lean`, commit d442da2) has exactly these hypotheses and this conclusion.
It follows the exit-time argument: for `D ⊆ B_ρ` the
BG20 estimate is applied to the open thickening `thickening (ε^(2α)) D`, whose mass is bounded below by
`VolumeGrowthStmt` at the centres of `D`; the interior cell set is monotone in the domain for open supersets
(`interiorCellVertices_mono_of_subset`, continuous `η`); `expectedExitTime` is monotone in the domain; and the
potential is monotone in the domain. This file only re-exports that proof under the name the assembly uses, so the assembly
has one entry point.
-/

namespace MatedCRT

/-- **Lemma 2.18 (`ExitTimeUpperBoundStmt`) from BG20 Proposition 5.1 and the volume growth (Lemma 2.7).**
`BG20Prop51 𝒮` (BG20 Proposition 5.1, frozen) and `VolumeGrowthStmt` (Lemma 2.7, BG20 Lemma A.1) imply both clauses of
`ExitTimeUpperBoundStmt 𝒮`, including the unrestricted clause for every `D ⊆ B_ρ`. -/
theorem exitTimeUpperBound_of_bg20Prop51_volumeGrowth {𝒮 : SpaceFillingSLEModel} (h51 : BG20Prop51 𝒮)
    (h27 : VolumeGrowthStmt) : ExitTimeUpperBoundStmt 𝒮 :=
  exitTimeUpperBoundStmt_core h51 h27

end MatedCRT
