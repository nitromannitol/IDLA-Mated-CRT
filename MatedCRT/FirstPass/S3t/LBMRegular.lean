import MatedCRT.Proofs.LBM.AlmostSureRegularExit
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions
import MatedCRT.FirstPass.S3t.Defs

/-!
# Truncated quenched laws, Step 4: almost-sure regular exit of the limiting LBM (fp-S3t, z2)

Step 4 of `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md` (section 3). For almost every environment and almost every
Brownian path `b` from `y`, the rescaled Liouville Brownian motion `rescaledLBMPath (S.clock ω) S.m₀ b` exits the disk
`ball z r` regularly. The proof is the existing transfer of Brownian radial excursions to LBM regular exits
(`MatedCRTEnv.IsValid.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion`,
`MatedCRT/Proofs/LBM/AlmostSureRegularExit.lean`), applied to `BrownianOutwardExcursionAtExitStep`.

`RegularExit` is the regular-exit predicate of Berestycki–Gwynne and Mörters–Peres (Theorem 2.16 and Theorem 2.8): the
path either never exits `D`, or it leaves the closure of `D` at arbitrarily small positive times after its exit time.
The answer's Step 4 omits the hypotheses `y ∈ ball z r` and `0 < S.m₀`; both are needed by the existing transfer lemma,
so they are added.
-/

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal

namespace MatedCRT.TruncatedLaws

/-- Regular exit of the path `w` from the disk-like set `D`: either `D` is never exited, or after the exit time `τ_D(w)`
the path is outside the closure of `D` at arbitrarily small positive times (Frequently in `𝓝[>] τ_D(w)`). -/
def RegularExit (D : Set ℂ) (w : ℝ≥0 → ℂ) : Prop :=
  pathExitTime D w = ⊤ ∨ ∃ᶠ t in 𝓝[>] (pathExitTime D w).toNNReal, w t ∉ closure D

/-- Step 4: almost surely, the limiting rescaled LBM from `y ∈ ball z r` exits `ball z r` regularly, for almost every
Brownian path from `y`. -/
theorem ae_regularExit_rescaledLBM {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hm : 0 < S.m₀) {y z : ℂ} {r : ℝ} (hy : y ∈ ball z r)
    (hexit : BrownianOutwardExcursionAtExitStep) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      RegularExit (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
  filter_upwards [MatedCRTEnv.IsValid.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hS hm hy
    (hexit y z r hy)] with ω hω
  filter_upwards [hω] with b hb
  exact Or.inr hb

#print axioms ae_regularExit_rescaledLBM

end MatedCRT.TruncatedLaws
