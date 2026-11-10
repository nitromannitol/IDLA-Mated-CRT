import MatedCRT.Defs.QuantumCone

/-!
# First pass: the corrected radial-divergence input (task fp-S1c-divergence-repair, z1)

`FrozenConeRadialDivergenceCorrected` replaces `FrozenConeRadialDivergence` (Frozen/S1c.lean), which is FALSE as stated: its
conclusion lives on the raw product space `(ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)` of `quantumConeRadialLaw`, where the event of real-time
divergence is not measurable and has outer measure one (notes/fp-gaps/CHATGPT-idla-frozen-batch.md §1, lines 32-117).
The corrected form keeps the conclusion on the continuous-path carrier `ContinuousPath ℝ` of `ν`; the transfer to the cone is
proved in FirstPass/S1c/RadialDivergence.lean.
-/

namespace MatedCRT

open MeasureTheory Filter Topology HarmonicBalls MarkovProcess
open scoped NNReal

/-- FIRST-PASS FROZEN. Radial divergence of the conditioned Brownian motion, on its continuous-path carrier. For `0 < γ < 2` and
every probability `ν` on continuous paths with `IsBMConditionedPositive (lqgQ γ - γ) ν` (the conditioned Brownian motion with
drift `c = Q - γ > 0`, where `Q = lqgQ γ`), `ν`-almost surely `w s + c s → ∞` as `s → ∞` on `ℝ≥0`.
Verdict: TRUE, as stated (ChatGPT, 03:41 UTC; notes/fp-gaps/CHATGPT-idla-S2m-S1cDiv.md §2). Repair of
`FrozenConeRadialDivergence` (FALSE, ChatGPT 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md §1, "Minimal corrected statement").
Source: Duplantier–Miller–Sheffield, *Mating of trees*, arXiv:1409.7055v4, Remark 4.4, printed pp. 74–75: the last-zero construction
`X_s = B̃_{τ+s} + c(τ+s)` with `τ = sup {t ≥ 0 : B̃_t + c t = 0}` on p. 75, with the cone convention Definition 4.10, p. 79.
Divergence follows from that construction and the Brownian strong law. For `c = Q - γ > 0` the conditioned process satisfies
`(w_s + c s) / s → c` almost surely, hence `w_s / s → 0` almost surely. Downstream only the rational-time transfer is used
(MatedCRT/FirstPass/S1c/RadialDivergence.lean; note §3).
Used by: coneScaleRadius_lowerTail (MatedCRT/FirstPass/S1c.lean), through the transfer lemmas of
MatedCRT/FirstPass/S1c/RadialDivergence.lean (`ae_ratDivergence_quantumConeRadialLaw`). -/
def FrozenConeRadialDivergenceCorrected : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
    ∀ᵐ w ∂ν, Tendsto (fun s : ℝ≥0 => w s + (lqgQ γ - γ) * (s : ℝ)) atTop atTop

end MatedCRT
