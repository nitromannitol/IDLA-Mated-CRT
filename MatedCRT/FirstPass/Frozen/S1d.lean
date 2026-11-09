import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.External.SLE

/-!
# First pass: frozen EXTERNAL input of the recomposed Theorems 1.4 and 1.6 (q4, task fp-S1d2)

One Prop is frozen here: `ConeEnvironmentScalingUnderSLE`, the closure-conditional form of the quantum-cone
environment scaling. It replaces the RETIRED `FrozenConeEnvironmentScaling` (Frozen/S3S4.lean; FALSE, truth check
2026-11-09, notes/fp-gaps/TRUTH-CHECK-2.md:50-56). Operator decision (fp-S1d2, 21:12 UTC): freeze as EXTERNAL.
-/

namespace MatedCRT

/-- FIRST-PASS FROZEN (EXTERNAL). Scaling of the quantum cone environment, conditional on the three space-filling SLE
closure properties (`SLEScaleInvarianceInput`, `SLEReparametrizationInput`, `SLEIndepMonoInput`, External/SLE.lean).
If the model 𝒮 is closed under scaling, reparametrization and restriction of independence, then for every valid
environment `S` with cone parameter `γ` and every `b > 0` there is a valid environment `S'` on the same probability space
with `η' = R_b⁻¹ η(b ·)`, `bm' = b^{-1/2} bm(b ·)`, `μ' = b⁻¹ μ_h(R_b ·)`, where `R_b` is the cone scale radius.
Source: route B of notes/fp-gaps/CHATGPT-sle-inputs-referee.md §4B (the direct rescaled-environment argument); quantum
cone scaling Duplantier–Miller–Sheffield (2014, *Mating of trees*, arXiv:1409.7055v4), Proposition 4.13(i)
(eq:quantum-cone-scaling), with canonical GMC covariance of the LQG measure (Duplantier–Sheffield, arXiv:0808.1560,
Proposition 2.1); space-filling SLE scaling Miller–Sheffield (*Imaginary geometry IV*, arXiv:1302.4738, §§1.2.3, 4.3).
Locator: DMS14 Prop 4.13(i) and the closure inputs of External/SLE.lean. Truth check to follow (operator).
Used by: firstPass_1_4, firstPass_1_6 (MatedCRT/FirstPass/S1d.lean). -/
def ConeEnvironmentScalingUnderSLE (𝒮 : SpaceFillingSLEModel) : Prop :=
  SLEScaleInvarianceInput 𝒮 → SLEReparametrizationInput 𝒮 → SLEIndepMonoInput 𝒮 → ConeEnvironmentScalingStep 𝒮

end MatedCRT
