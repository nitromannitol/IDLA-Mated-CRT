import MatedCRT.FirstPass.S3t.Integrate
import MatedCRT.FirstPass.S3t.EpsShell
import MatedCRT.FirstPass.S3t.BoundaryShells

/-!
# Truncated quenched laws: the staged assembly (fp-S3t, z8; answer section 4)

Source: `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md`, Steps 5–12 and section 4 (the replacement theorem).

`truncatedQuenchedLawsFixedTime_of_steps` assembles Steps 11 and 12 with the outputs of Steps 5–8 and 10, taken as
hypotheses with the answer's Lean types. Concrete now: the disk `D = B_r(z)`, the exhaustion `D_n = ballExhaustion z r a n`
and the shell functional `shellTime (D_n) (B_r(z)) T` (`S3t/BoundaryShells.lean`); the walk measurability of the stopped
occupation and of the shell functional is proved (`S3t/Integrate.lean`).

Notation (answer section 3): `W ε ω q := interpolatedWalk ε (S.η ω) (S.mε ε) q` is the interpolated walk,
`X ω b := rescaledLBMPath (S.clock ω) S.m₀ b` the rescaled LBM path, and the quenched walk law is
`srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- Sum of a term converging to `0` in probability and a term converging in probability to `Y`. Same statement and
proof as `MatedCRT.TruncatedLawsBridge.tendstoInProbability_add_of_zero` (`FirstPass/S3S4b/TruncatedLawsBridge.lean`),
restated here to keep the `S3t` closure free of the first-pass bridge. -/
theorem tendstoInProbability_add_of_zero_left {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D X : ℝ → Ω → ℝ} {Y : Ω → ℝ}
    (hD : TendstoInProbability P D (fun _ : Ω => (0 : ℝ))) (hX : TendstoInProbability P X Y) :
    TendstoInProbability P (fun ε ω => D ε ω + X ε ω) Y := by
  intro δ hδ
  have h2 : (0 : ℝ) < δ / 2 := by positivity
  have hsum : Tendsto (fun ε => P {ω | δ / 2 < |D ε ω - (0 : ℝ)|} + P {ω | δ / 2 < |X ε ω - Y ω|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hD (δ / 2) h2).add (hX (δ / 2) h2)
    rwa [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro ε
  have hsub : {ω | δ < |D ε ω + X ε ω - Y ω|} ⊆
      {ω | δ / 2 < |D ε ω - (0 : ℝ)|} ∪ {ω | δ / 2 < |X ε ω - Y ω|} := by
    intro ω hω
    have htri := abs_add_le (D ε ω - 0) (X ε ω - Y ω)
    have heq : D ε ω - 0 + (X ε ω - Y ω) = D ε ω + X ε ω - Y ω := by ring
    rw [heq] at htri
    rcases lt_or_ge (δ / 2) |D ε ω - 0| with h1 | h1
    · exact Or.inl h1
    rcases lt_or_ge (δ / 2) |X ε ω - Y ω| with h2 | h2
    · exact Or.inr h2
    have hω' : δ < |D ε ω + X ε ω - Y ω| := hω
    linarith
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **Staged truncated-laws theorem** (Steps 11–12 and section 4 of the answer). For the disk `D = B_r(z)`, the concentric
exhaustion `D_n = ballExhaustion z r a n` (`a ≥ 0`, Step 6 uses `a = (r - |y - z|)/2`), the fixed-`T` quenched expected
truncated discrete occupation converges in probability to the quenched expected truncated LBM occupation, given the
outputs of Steps 5, 6, 7, 8 and 10 as hypotheses. The conclusion is the body of `FrozenTruncatedQuenchedLawsFixedTime`
at `ball z r`. -/
theorem truncatedQuenchedLawsFixedTime_of_steps {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    [IsProbabilityMeasure S.P] (z : ℂ) (r a : ℝ) (ha : 0 ≤ a) (y : ℂ) (g : ℂ → ℝ) (hgc : Continuous g)
    {T M C χ α : ℝ} (hT : 0 < T) (hg : ∀ x, |g x| ≤ M) (hM : 0 < M) (hχ : 0 < χ) (hα : 0 < α)
    {Good : ℝ → Ω → Prop}
    -- Step 5 (Theorem 2.11 with K = {y}): the stopped occupation converges to the LBM stopped occupation.
    (hOcc : TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation (Metric.ball z r) T g (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    -- Step 6: boundary-shell functionals, their convergence in probability, and their a.s. limit.
    (hShell : ∀ n, TendstoInProbability S.P
      (fun ε ω => ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y))
    (hShellLimit : ∀ᵐ ω ∂S.P,
      Tendsto (fun n => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) atTop (𝓝 0))
    -- Named measurability of the LBM shell limit in the environment (G1: not written in the answer; see report).
    (hShellMeas : ∀ n, AEMeasurable (fun ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
        (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P)
    -- Step 7: mesh-good events have probability tending to one (upper half of Lemma 2.8).
    (hMesh : Tendsto (fun ε => S.P {ω | ¬ Good ε ω}) (𝓝[>] (0 : ℝ)) (𝓝 0))
    -- Step 8: normalization error (lower half of MepsScalingInput).
    (hMInv : Tendsto (fun ε => (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < S.mε ε)
    -- Step 10: pathwise Riemann-sum estimate, for quenched-a.e. walk on the mesh-good event, for small ε (depending on n).
    (hpath : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
        |quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
            - stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)|
          ≤ T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹
            + M * shellTime (ballExhaustion z r a n) (Metric.ball z r) T (interpolatedWalk ε (S.η ω) (S.mε ε) q)) :
    TendstoInProbability S.P
      (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, rescaledLBMOccupation S ω (Metric.ball z r) (ENNReal.ofReal T) g b
        ∂planarBrownianMotion y) := by
  -- Step 8 and Step 7 give the deterministic error `E ε → 0`.
  have hE : Tendsto (fun ε : ℝ => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_deterministicError hα hχ hMInv
  -- Step 11: integrate the pathwise bound on the good event, for each shell index `n`.
  have hpath11 : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      |(∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        - ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
            ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)|
        ≤ (T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹)
          + M * ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
              (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
    intro n
    filter_upwards [hpath n, hmpos] with ε hε hm ω hG
    exact abs_quenchedDiscrete_sub_stopped_integral_le S ω hgc.measurable hg hT.le hm
      (W := fun q => interpolatedWalk ε (S.η ω) (S.mε ε) q)
      (Rq := fun q => shellTime (ballExhaustion z r a n) (Metric.ball z r) T (interpolatedWalk ε (S.η ω) (S.mε ε) q))
      (measurable_stoppedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T hgc)
      (measurable_shellTime_interpolatedWalk ε (S.η ω) (S.mε ε) z r a T n)
      (fun q => shellTime_nonneg (ballExhaustion_subset z r ha n) T _)
      (fun q => shellTime_le hT.le _) (hε ω hG)
  -- Step 12: epsilon first, shell width second: `A - C → 0` in probability.
  have hstep12 := tendstoInProbability_sub_zero_of_shell (P := S.P) hM
    (A := fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (C := fun ε ω => ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (R := fun n ε ω => ∫ q, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
      (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (Rlim := fun n ω => ∫ b, shellTime (ballExhaustion z r a n) (Metric.ball z r) T
      (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)
    (E := fun ε => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (Good := Good)
    hpath11 hE hMesh hShell hShellMeas hShellLimit
  -- Section 4: add the fixed-`T` LBM comparison of Step 5.
  have hsum := tendstoInProbability_add_of_zero_left hstep12 hOcc
  have hfun : (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      = (fun ε ω => (∫ q, quenchedDiscreteOccupation S ω (Metric.ball z r) g T ε q
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          - ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          + ∫ q, stoppedOccupation (Metric.ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) := by
    funext ε ω
    ring
  rw [hfun]
  exact hsum

end MatedCRT.TruncatedLaws
