import MatedCRT.Draft.Section3

/-!
# Lemma 3.4: continuum occupation identity

The identity at line 1172 of the corrected paper uses the Revuz measure of
Liouville Brownian motion. The current `IsLQGClock` states convergence of
clock approximations, but does not include the Revuz correspondence. This
step records the missing identity for the unscaled process. The factor two
comes from the normalization `ΔG = -δ` in `HarmonicBalls.greenFunction`.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The expected occupation integral of Liouville Brownian motion killed on
leaving `D`. Finiteness of the exit time is a separate part of the step. -/
noncomputable def lbmOccupationIntegral (F : ContinuousPath ℂ → ℝ≥0 → ℝ)
    (D : Set ℂ) (y : ℂ) (f : ℂ → ℝ) : ℝ :=
  ∫ b, (∫ t in Ioo (0 : ℝ) (lbmExitTime F D b).toReal,
    f (liouvilleBrownianPath F b t.toNNReal)) ∂(planarBrownianMotion y)

/-- The Revuz occupation identity needed at line 1172 of Lemma 3.4. This is
an explicit open step, not a theorem supplied by `IsLQGClock`: its source is
the Revuz-measure characterization of the LQG clock in Garban--Rhodes--Vargas,
*Liouville Brownian motion*, Theorem 2.7(1), pp. 10--11, together with the
potential formula for the killed Brownian motion. -/
def LBMGreenOccupationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ᵐ ω ∂S.P,
    (∀ᵐ b ∂planarBrownianMotion y, lbmExitTime (S.clock ω) (ball z r) b < ⊤) ∧
    ∀ f : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |f x| ≤ M) →
      IsHolderContinuousOn f (ball z r) →
      lbmOccupationIntegral (S.clock ω) (ball z r) y f =
        2 * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ ω

end MatedCRT
