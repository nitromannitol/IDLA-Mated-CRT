import MatedCRT.Steps.Sec3.DiscretePotentialTightness
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.Steps.Sec1.Convergence

/-!
# First pass: frozen external inputs of Sections 3 and 4 (q2, task fp-S3S4)

Each `def` below is an EXTERNAL input of the first pass (general mathematics or a cited result of the paper), used as
an explicit hypothesis. Nothing here is a claim about this paper's clusters, odometers, harmonic balls or IDLA
processes beyond the cited statement itself.
-/

namespace MatedCRT

/-- FIRST-PASS FROZEN. Lemma 3.2 (lemma:discrete-holder-continuity, paper line 1018), corrected form, cited from
\cite{gwynne2019harmonic} Theorem 3.9 (locator: GMS Theorem 3.9, (3.30)–(3.33), arXiv:1807.07511v3, per notes/fp-gaps/CHATGPT-frozen-locators.md; the paper's citation is "Theorem 3.9").
The printed Draft `DiscreteHolderContinuityStmt` is FALSE (review-L32 F1, docs/campaign/CORRECTED-FORMS.md, entry 3.2);
this is the corrected statement `DiscreteHolderContinuityCorrectedStep` of Steps/Sec3/DiscretePotentialTightness.lean:71.
Truth check UNRESOLVED for an unconstrained SLE model; TRUE under the certified reference law, see SLEReferenceExistsInput
(ChatGPT, 02:35 UTC; notes/fp-gaps/CHATGPT-idla-sle-frozen-7.md §3).
Used by: firstPass_3_1_corrected. -/
def FrozenDiscreteHolderContinuityCorrected (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteHolderContinuityCorrectedStep 𝒮

/-- FIRST-PASS FROZEN. Regular exit of planar Brownian motion from a disk: almost surely, immediately after the first
exit time from `ball z r` the path makes an outward radial excursion (`0 < ⟪b(τ) - z, b(t) - b(τ)⟫` for arbitrarily small
`t > τ`). Source: Mörters–Peres, *Brownian Motion* (Cambridge 2010), Theorem 2.7 and Theorem 2.16 (strong Markov property at
the exit time and Blumenthal's 0-1 law; standard). The statement is about planar Brownian motion only, not about this
Truth check UNCLEAR (ChatGPT, 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md §6): the body of BrownianOutwardExcursionAtExitStep is absent from the checked source; the fixed-disk and simultaneous-in-radius assertions have different truth values.
paper's objects. Used by: firstPass_3_6. -/
def FrozenBrownianOutwardExcursionAtExit : Prop :=
  BrownianOutwardExcursionAtExitStep

/-- RETIRED (FALSE, truth check 2026-11-09; notes/fp-gaps/TRUTH-CHECK-2.md:50). Validity would need closure of an
unrestricted SLE predicate under rescaling. Not used by the repaired `firstPass_4_1_coneLaw` (FirstPass/S4S6c.lean),
which uses `FrozenConeScalingLaw` (Frozen/S4S6c.lean) instead. Kept for the record; do not delete.
FIRST-PASS FROZEN. Scaling of the quantum cone environment and of the mating-of-trees coupling: for `b > 0` there is a
valid environment `S'` on the same probability space with `η^b = R_b⁻¹ η(b ·)`, `bm^b = b^{-1/2} bm(b ·)` and
`μ^b = b⁻¹ μ_h(R_b ·)`, where `R_b` is the cone scale radius. Source: Duplantier–Miller–Sheffield (2014, *Mating of trees*;
the arXiv identifier is as cited in MatedCRT/External/QuantumCone.lean), Proposition 4.13(i) (quantum cone scaling, DMS14 eq:quantum-cone-scaling) together with
the Brownian scaling of the mating-of-trees pair; the statement is `ConeEnvironmentScalingStep` (Steps/Sec1/Convergence.lean).
It concerns the quantum cone environment only, not clusters, odometers, harmonic balls or IDLA processes. Locator: standard;
judgment call, flagged in the report. Used by: firstPass_4_1. -/
def FrozenConeEnvironmentScaling (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConeEnvironmentScalingStep 𝒮

end MatedCRT
