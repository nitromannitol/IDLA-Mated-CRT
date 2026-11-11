import Mathlib
import MatedCRT.FirstPass.S6e.Uniform
import MatedCRT.FirstPass.S6e.Guard
import MatedCRT.FirstPass.S4S6c.ExitNull68

/-!
# Lemma 6.8, uniform constant-order lower bound: the final assembly of the redesign (S10 and final)

Target: `MatedCRT.UniformConstantOrderLowerBoundStmt` (FirstPass/S6d.lean:95), in the stronger quantifier order
(`ω₀`, `s₁`, `s₂` chosen before `s₀`), as required for Lemma 6.9.

Route (section 13; redesign S0-S10,
 section 12):
the uniform statement follows from the guard input `Lemma68Uniform.GuardProbStmt` (S6e/Uniform.lean:132) by
`Lemma68Uniform.uniform_of_guard`. The three non-guard inputs are discharged here by existing providers:
* the curve escapes both ends almost surely: `Lemma68Guard.ae_escapes_of_valid` (S6e/Guard.lean:176);
* the multiplicities are locally finite with consecutive adjacency almost surely:
  `Lemma68Guard.ae_finiteExit_of_valid` (S6e/Guard.lean:182);
* the exit from a finite set is almost surely finite: `ExitNull68.exit_null_of_finite` (S4S6c/ExitNull68.lean:20).

The guard input is the open part and is an explicit hypothesis of this file. Its proof is the redesign S10 (the
Borel-Cantelli cutoff `dd` over the dyadic scales, `exists_dyadic_cutoff` in S4S6c/DyadicCutoff68.lean, with the
constants `Constants68.ω` and `Constants68.ζ` of S6r/Constants.lean) together with the per-configuration bound
of the shell chain (`shell_product_le_half`, S7'/S8', not yet committed) and the constant-order bound
`S9_one_test_le_half` (S4S6c/Redesign68S9.lean, proved). Carried as hypotheses until those land.
-/

namespace MatedCRT

/-- **Lemma 6.8, uniform, redesigned schedule: the final assembly.** From the guard input (the S10 statement of the
redesign, which carries the shell chain S7'/S8' as an explicit hypothesis until it is committed), the uniform
constant-order lower bound `UniformConstantOrderLowerBoundStmt 𝒮` holds. -/
theorem uniformConstantOrderLowerBound_of_guard (𝒮 : SpaceFillingSLEModel)
    (hG : Lemma68Uniform.GuardProbStmt 𝒮) : UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68Uniform.uniform_of_guard 𝒮 hG
    (by intro γ _ _ Ω _ S hS; exact Lemma68Guard.ae_escapes_of_valid hS)
    (by intro γ hγ0 hγ2 Ω _ S hS; exact Lemma68Guard.ae_finiteExit_of_valid hγ0 hγ2 hS)
    (fun m hlf hcons A hA y => ExitNull68.exit_null_of_finite hlf hcons hA y)

end MatedCRT
