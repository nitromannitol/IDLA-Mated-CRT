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

/-- Berestycki, *Diffusion in planar Liouville quantum gravity*, Ann. Inst.
H. Poincaré Probab. Statist. 51 (2015), Theorem 1.2, p. 949. The
zero-boundary field and Brownian motion are independent, `0 ≤ γ < 2`, and
we restrict to bounded simply connected field domains. The epsilon-normalized
paths converge along dyadic scales to a path continuous before its first exit.
This formalization sets the circle average to zero when its closed disk is not
contained in `D`. The published statement does not specify that extension;
its compatibility with the theorem requires independent verification. No
assertion about convergence or regularity of the clocks is included. -/
def BerestyckiLiouvilleDiffusionStmt : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ),
    IsOpen D → D ≠ Set.univ → SimplyConnectedSpace D → Bornology.IsBounded D → x ∈ D →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    (∀ ω r z, ¬ Metric.closedBall z r ⊆ D → hcirc ω r z = 0) →
    ∃ Z : Ω → ContinuousPath ℂ → ℝ≥0 → ℂ,
      ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
        (∀ t : ℝ≥0, Tendsto (fun n => q.2 ((killedClockInverse
          (killedGMCClockApprox D γ (hcirc q.1) (dyadicScale n) q.2)
          (ContinuousPath.exitTime D q.2) t).toNNReal)) atTop (𝓝 (Z q.1 q.2 t))) ∧
        ContinuousOn (Z q.1 q.2) {t | ∀ s ≤ t, Z q.1 q.2 s ∈ D}

end MatedCRT
