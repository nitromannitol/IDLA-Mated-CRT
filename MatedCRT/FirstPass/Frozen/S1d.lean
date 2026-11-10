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
Route: B of notes/fp-gaps/CHATGPT-sle-inputs-referee.md §4B (the direct rescaled-environment argument).
Sources (operator decision 22:02 UTC; list in notes/fp-gaps/CHATGPT-cone-scaling-final.md):
(i) quantum-cone scaling `h^b =d h` and the rescaled LQG measure: Duplantier–Miller–Sheffield, *Mating of trees*,
arXiv:1409.7055, Definition 4.10 and Proposition 4.13(i).
(ii) field-dependent dilation: Sheffield–Wang, arXiv:1605.06171, Theorem 1.4 (simultaneous conformal covariance), with
localization to the cone. Geometry: Miller–Sheffield, *Imaginary geometry IV*, arXiv:1302.4738, equation (1.2),
Theorems 1.1–1.2 and 1.16; whole-plane construction DMS §1.4.1, footnote 4.
(iii) auxiliary witnesses on the same space: DMS Lemma 4.9 (radial/lateral independence); Kallenberg, *Foundations of
Modern Probability*, 2nd ed., Theorem 6.10 (with Theorem 6.3 and Lemma 3.22).
(iv) Brownian scaling `b^{-1/2} bm(b ·)`: Kallenberg, 2nd ed., Chapter 13, p. 253, before Lemma 13.6.
(v) clock clause for every starting point: Garban–Rhodes–Vargas, arXiv:1301.2876, Theorem 2.7(2)–(4), Proposition 2.3,
Lemma 2.5; Berestycki, *Diffusion in planar Liouville quantum gravity*, Theorem 1.2 and §2; Berestycki–Gwynne,
arXiv:2003.10320, §1.2 footnote 2 and Lemma A.1.
Truth check (operator 22:02 UTC): TRUE as the exact conditional Lean statement; the decisive clause is `boundaryLength`
in `IsMatingOfTreesCoupling`. The note classifies it as a derived consequence of these standard facts and the existing
coupling assumptions; it stays frozen as EXTERNAL by operator decision.
Truth check TRUE as the stated conditional implication, keeping all three SLE closure premises (ChatGPT, 02:35 UTC;
notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md §2).
Used by: firstPass_1_4, firstPass_1_6 (MatedCRT/FirstPass/S1d.lean). -/
def ConeEnvironmentScalingUnderSLE (𝒮 : SpaceFillingSLEModel) : Prop :=
  SLEScaleInvarianceInput 𝒮 → SLEReparametrizationInput 𝒮 → SLEIndepMonoInput 𝒮 → ConeEnvironmentScalingStep 𝒮

end MatedCRT
