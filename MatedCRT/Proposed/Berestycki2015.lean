import MatedCRT.Defs.DirichletGFF
import MatedCRT.Defs.KilledGMCClock

/-!
# Dyadic Liouville clock and diffusion

Staged literature input for independent source audit; this is a proposition,
not an axiom or a proof of the published theorem.
-/

namespace MatedCRT

open HarmonicBalls MeasureTheory MarkovProcess Filter Topology
open scoped ENNReal NNReal

/-- Berestycki, *Diffusion in planar Liouville quantum gravity*,
arXiv:1301.3356v1, Theorem 1.2, p. 949, its proof in Sections 2--3,
pp. 950--959, and Remark 3.5, p. 959. This is the localized form in the
proof: the Brownian path is stopped on exiting a bounded open `U` whose
closure lies in the simply connected field domain `D`. The zero-boundary
GFF and Brownian path are sampled independently, and `0 ≤ γ < 2`.
The dyadic clocks converge almost surely to a continuous clock, strictly
increasing before exit; their time changes converge before the terminal
clock time to a continuous path. The inverse of the limit clock is strictly
increasing before that time (Remark 3.5).

The source's statement allows a proper connected domain, but its proof on
p. 951 uses a conformal map of `D` to the disk. The restriction to simply
connected `D` makes this use explicit. Localization also ensures that the
circle averages used before the stopped exit are defined for all sufficiently
small scales, without imposing an arbitrary extension near `∂D`. -/
def BerestyckiLiouvilleDiffusionStmt : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ),
    IsOpen D → D ≠ Set.univ → SimplyConnectedSpace D →
    IsOpen U → Bornology.IsBounded U → closure U ⊆ D → x ∈ U →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ,
      ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
        let τ := ContinuousPath.exitTime U q.2
        let T := τ.toNNReal
        let K : ℕ → ℝ≥0 → ℝ := fun n =>
          killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2
        τ < ⊤ ∧
        (∀ t : ℝ≥0, Tendsto (fun n => K n t) atTop (𝓝 (F q.1 q.2 t))) ∧
        Continuous (F q.1 q.2) ∧ F q.1 q.2 0 = 0 ∧
        StrictMonoOn (F q.1 q.2) (Set.Iic T) ∧
        (∀ t : ℝ≥0, T ≤ t → F q.1 q.2 t = F q.1 q.2 T) ∧
        (∀ t : ℝ≥0, (t : ℝ) < F q.1 q.2 T →
          Tendsto (fun n => q.2 ((killedClockInverse (K n) τ t).toNNReal))
            atTop (𝓝 (q.2 ((killedClockInverse (F q.1 q.2) τ t).toNNReal)))) ∧
        ContinuousOn (fun t : ℝ≥0 =>
          q.2 ((killedClockInverse (F q.1 q.2) τ t).toNNReal))
          {t | (t : ℝ) < F q.1 q.2 T} ∧
        StrictMonoOn (fun t : ℝ≥0 => killedClockInverse (F q.1 q.2) τ t)
          {t | (t : ℝ) < F q.1 q.2 T}

end MatedCRT
