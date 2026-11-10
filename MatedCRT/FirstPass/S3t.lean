import MatedCRT.FirstPass.S3t.Integrate
import MatedCRT.FirstPass.S3t.EpsShell

/-!
# Truncated quenched laws: the staged assembly (fp-S3t, z8; answer section 4)

Source: `notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md`, Steps 5–12 and section 4 (the replacement theorem).

`truncatedQuenchedLawsFixedTime_of_steps` assembles Steps 11 and 12 with the outputs of Steps 5–8 and 10, taken as
hypotheses with the exact Lean types of the answer. Each hypothesis is replaced by its proof when its owner commits
(Steps 1–4: `S3t/Bounds.lean`, `S3t/BLExtension.lean`, `S3t/StoppedContinuity.lean`, `S3t/LBMRegular.lean`;
Steps 5–8: `S3t/…` owned by z10; Steps 9–10: `S3t/CellGeometry.lean`, `S3t/RiemannSum.lean`).

Notation (answer section 3): `W ε ω q := interpolatedWalk ε (S.η ω) (S.mε ε) q` is the interpolated walk,
`X ω b := rescaledLBMPath (S.clock ω) S.m₀ b` the rescaled LBM path, and the quenched walk law is
`srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)`. The shell index `n` runs over the nested disks `D n` of Step 6, which enter
only through the shell functional `R n`; its bounds `0 ≤ R n w ≤ T` are Step 6.
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

/-- **Staged truncated-laws theorem** (Steps 11–12 and section 4 of the answer). For fixed parameters
`(S, D, y, g, T, M, C, χ, α)`, the fixed-time quenched expected truncated discrete occupation converges in probability to
the quenched expected truncated LBM occupation, given the outputs of Steps 5–8 and 10 as hypotheses. The conclusion is the
body of `FrozenTruncatedQuenchedLawsFixedTime` at `D = ball z r`. -/
theorem truncatedQuenchedLawsFixedTime_of_steps {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    [IsProbabilityMeasure S.P] (D : Set ℂ) (y : ℂ) (g : ℂ → ℝ) (hgm : Measurable g)
    {T M C χ α : ℝ} (hT : 0 < T) (hg : ∀ x, |g x| ≤ M) (hM : 0 < M) (hχ : 0 < χ) (hα : 0 < α)
    {Good : ℝ → Ω → Prop} {R : ℕ → (ℝ≥0 → ℂ) → ℝ} (hR0 : ∀ n w, 0 ≤ R n w) (hRT : ∀ n w, R n w ≤ T)
    -- Step 5 (Theorem 2.11 with K = {y}): the stopped occupation converges to the LBM stopped occupation.
    (hOcc : TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation D T g (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y))
    -- Step 6: boundary-shell functionals, their convergence in probability, and their a.s. limit.
    (hShell : ∀ n, TendstoInProbability S.P
      (fun ε ω => ∫ q, R n (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, R n (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y))
    (hShellLimit : ∀ᵐ ω ∂S.P,
      Tendsto (fun n => ∫ b, R n (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) atTop (𝓝 0))
    -- Named measurability of the LBM shell limit in the environment (not written in the answer; see report).
    (hShellMeas : ∀ n, AEMeasurable
      (fun ω => ∫ b, R n (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y) S.P)
    -- Step 7: mesh-good events have probability tending to one (upper half of Lemma 2.8).
    (hMesh : Tendsto (fun ε => S.P {ω | ¬ Good ε ω}) (𝓝[>] (0 : ℝ)) (𝓝 0))
    -- Step 8: normalization error (lower half of MepsScalingInput).
    (hMInv : Tendsto (fun ε => (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hmpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < S.mε ε)
    -- Step 10: pathwise Riemann-sum estimate, for quenched-a.e. walk on the mesh-good event, for small ε (depending on n).
    (hpath : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      ∀ᵐ q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y),
        |quenchedDiscreteOccupation S ω D g T ε q
            - stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)|
          ≤ T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹ + M * R n (interpolatedWalk ε (S.η ω) (S.mε ε) q))
    -- Named measurability in the walk variable of the stopped occupation and of the shell functional (not written
    -- in the answer; see report).
    (hCMeas : ∀ ε ω, Measurable
      (fun q : ℕ → ℤ => stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)))
    (hRMeas : ∀ n ε ω, Measurable (fun q : ℕ → ℤ => R n (interpolatedWalk ε (S.η ω) (S.mε ε) q))) :
    TendstoInProbability S.P
      (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, rescaledLBMOccupation S ω D (ENNReal.ofReal T) g b ∂planarBrownianMotion y) := by
  -- Step 8 and Step 7 give the deterministic error `E ε → 0`.
  have hE : Tendsto (fun ε : ℝ => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_deterministicError hα hχ hMInv
  -- Step 11: integrate the pathwise bound on the good event, for each shell index `n`.
  have hpath11 : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω, Good ε ω →
      |(∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        - ∫ q, stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
            ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)|
        ≤ (T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹)
          + M * ∫ q, R n (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) := by
    intro n
    filter_upwards [hpath n, hmpos] with ε hε hm ω hG
    exact abs_quenchedDiscrete_sub_stopped_integral_le S ω hgm hg hT.le hm
      (W := fun q => interpolatedWalk ε (S.η ω) (S.mε ε) q) (Rq := fun q => R n (interpolatedWalk ε (S.η ω) (S.mε ε) q))
      (hCMeas ε ω) (hRMeas n ε ω) (fun q => hR0 n _) (fun q => hRT n _) (hε ω hG)
  -- Step 12: epsilon first, shell width second: `A - C → 0` in probability.
  have hstep12 := tendstoInProbability_sub_zero_of_shell (P := S.P) hM
    (A := fun ε ω => ∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (C := fun ε ω => ∫ q, stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (R := fun n ε ω => ∫ q, R n (interpolatedWalk ε (S.η ω) (S.mε ε) q) ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (Rlim := fun n ω => ∫ b, R n (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion y)
    (E := fun ε => T * C * (2 * ε ^ α) ^ χ + 4 * M * (S.mε ε)⁻¹) (Good := Good)
    hpath11 hE hMesh hShell hShellMeas hShellLimit
  -- Section 4: add the fixed-`T` LBM comparison of Step 5.
  have hsum := tendstoInProbability_add_of_zero_left hstep12 hOcc
  have hfun : (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      = (fun ε ω => (∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          - ∫ q, stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
          + ∫ q, stoppedOccupation D T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
              ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) := by
    funext ε ω
    ring
  rw [hfun]
  exact hsum

end MatedCRT.TruncatedLaws
