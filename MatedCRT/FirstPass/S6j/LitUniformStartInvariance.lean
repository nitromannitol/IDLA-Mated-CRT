import MatedCRT.Defs.Setting

/-!
# The named literature input N4: uniform-start invariance principle for the mated-CRT map walk

`GMS21UniformStartInput 𝒮` is the input of the proof of BG20 Lemma 6.9 (Berestycki-Gwynne, arXiv:2003.10320,
proof of Lemma 6.9, the paragraph after (6.29)): for `γ ∈ (0,2)`, uniformly over the starting points in a compact
subset of `D = B_R(0)`, the Prokhorov distance between the law of the embedded, linearly interpolated simple random
walk on the cell-size-`ε` mated-CRT map and the law of planar Brownian motion, both stopped at the exit time of `D`,
for the topology of curves modulo time parametrization, tends to zero in probability as `ε → 0`.

BG20 cites this as [GMS21, Theorem 3.4]: Gwynne-Miller-Sheffield, *The Tutte embedding of the mated-CRT map converges
to Liouville quantum gravity*, Ann. Probab. 49(4) (2021), 1677-1717, arXiv:1705.11161. It is the mated-CRT
corollary of the general invariance principle of Gwynne-Miller-Sheffield (arXiv:1807.07515, Theorem 3.10), with the
covariance a positive multiple of the identity by rotational invariance; after the time change it is standard
planar Brownian motion. It is a literature input, not a result of the IDLA paper.

## The form stated here

The bound is the one-sided Prokhorov inequality `P(W ∈ A) ≤ P(B ∈ A^κ) + κ`, for every set `A` of paths (the
measures of arbitrary sets are outer measures), with `A^κ` the open `κ`-neighbourhood of `A` for the distance
`cmpEDist` of curves modulo time parametrization. The starting vertices are all `x` with
`η(εx) ∈ closedBall 0 ρ`, `ρ < R`, and the walk and the Brownian motion start at `η(εx)`. The time of the
interpolated walk is the step count (`mε = 1`). The good event fails with probability at most `θ` once `ε < ε₀`.
-/

namespace MatedCRT

open MeasureTheory Metric Set HarmonicBalls
open scoped ENNReal NNReal

/-- The distance of curves modulo time parametrization:
`inf_φ sup_t |f(t) - g(φ(t))|` over the increasing homeomorphisms `φ` of `[0, ∞)`. -/
noncomputable def cmpEDist (f g : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨅ φ : ℝ≥0 ≃o ℝ≥0, ⨆ t : ℝ≥0, edist (f t) (g (φ t))

/-- The path `f` stopped at its exit time `pathExitTime U f` from `U` (unchanged if it never leaves `U`). -/
noncomputable def stopAtExit (U : Set ℂ) (f : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  f (if pathExitTime U f = ⊤ then t else min t (pathExitTime U f).toNNReal)

/-- **Literature input N4 (uniform-start invariance principle for the mated-CRT map walk).** For `γ ∈ (0,2)`, every
valid environment `S`, radii `0 < ρ < R` and tolerances `κ, θ > 0`, there is `ε₀ > 0` such that for all
`ε ∈ (0, ε₀)`, with probability at least `1 - θ`, for every vertex `x` with `η(εx) ∈ closedBall 0 ρ` and every set
`A` of paths, the simple random walk on the cell-size-`ε` mated-CRT map started at `x`, embedded by `η(ε ·)`,
linearly interpolated and stopped at its exit time from `B_R(0)`, lies in `A` with probability at most
`κ` plus the probability that the planar Brownian motion started at `η(εx)`, stopped at the same exit time, is within
`cmpEDist`-distance `κ` of `A`.

Source: [GMS21, Theorem 3.4] as cited in the proof of BG20 Lemma 6.9 (Gwynne-Miller-Sheffield, arXiv:1705.11161;
from arXiv:1807.07515, Theorem 3.10). -/
def GMS21UniformStartInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x : ℤ, vertexPoint ε (S.η ω) x ∈ closedBall (0 : ℂ) ρ → ∀ A : Set (ℝ≥0 → ℂ),
          srwLaw (S.mult ε ω) x {w | stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε (S.η ω) 1 w) ∈ A} ≤
            planarBrownianMotion (vertexPoint ε (S.η ω) x)
              {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal κ} +
              ENNReal.ofReal κ}ᶜ ≤ ENNReal.ofReal θ

/-- `stopAtExit` agrees with `f` up to the exit time. -/
theorem stopAtExit_of_coe_le {U : Set ℂ} {f : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ pathExitTime U f) :
    stopAtExit U f t = f t := by
  unfold stopAtExit
  split_ifs with h
  · rfl
  · rw [min_eq_left]
    exact ENNReal.le_toNNReal_of_coe_le ht h

end MatedCRT
