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
Source: the standard long-time behaviour of Brownian motion with positive drift conditioned to stay positive (Doob h-transform
of drifted Brownian motion killed at `0`; `w_s / s → c` a.s.), as used for the quantum cone in Duplantier–Miller–Sheffield
(2014, *Mating of trees*, arXiv:1409.7055v4): the last-zero construction of the conditioned process. Locator: standard; locator
pending. Repair of `FrozenConeRadialDivergence` (ChatGPT truth check FALSE, 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md
§1, "Minimal corrected statement", lines 96-110). PENDING TRUTH CHECK.
Used by: coneScaleRadius_lowerTail (MatedCRT/FirstPass/S1c.lean), through the transfer lemmas of
MatedCRT/FirstPass/S1c/RadialDivergence.lean (`ae_ratDivergence_quantumConeRadialLaw`). -/
def FrozenConeRadialDivergenceCorrected : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν →
    ∀ᵐ w ∂ν, Tendsto (fun s : ℝ≥0 => w s + (lqgQ γ - γ) * (s : ℝ)) atTop atTop

end MatedCRT
