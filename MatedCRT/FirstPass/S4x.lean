import MatedCRT.FirstPass.S3S4
import MatedCRT.Steps.Sec4.SubsequentialPropertiesPrepared
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedIdentification

/-! Lemma 4.8 (lemma:subsequential-properties), corrected form.

The printed `firstPass_4_8` (FirstPass/S3S4.lean) proves the legacy `SubsequentialPropertiesStmt`, in which one
deterministic subsequence `φ` is chosen before `t` (`∀ εs, ∃ φ, StrictMono φ ∧ ∀ᵐ ω, ∀ t > 0, ...`), and it does
not assert relative compactness. The corrected statement chooses the deterministic thinning after the fixed `t` and
the input sequence, and asserts (i) almost sure relative compactness `OdometerPreparedCompactness` (Lemma 4.6,
corrected) and (ii) identification of every subsequential limit. -/

open HarmonicBalls

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- The properties of one subsequential limit `w` of the rescaled least supersolutions at time `t` in Lemma 4.8,
corrected [C1] (`c₀ = 2/m₀`). The Green lower bound is stated off the pole, for `x ≠ 0` (at the pole the printed
bound is `-∞`; HB's `greenFunction` has the junk value `G(0,0) = 0`). The equality region is written with
`x = 0 ∨ ...`. Same clauses as the conclusion of `SubsequentialPropertiesPreparedStmt`
(Draft/Section4PropertiesPrepared.lean), with `t` and `w` fixed. -/
def SubsequentialLimitProperties {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ t : ℝ) (ω : Ω)
    (w : ℂ → ℝ) : Prop :=
  (∀ x ∈ closedBall (0 : ℂ) ρ, w x ≤ 0 ∧ (x ≠ 0 → -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x ≤ w x)) ∧
  LaplacianGE w 0 (ball 0 ρ) ∧
  LaplacianLE w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 ρ) ∧
  HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0
    {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x}

/-- **Lemma 4.8, corrected** (the minimal corrected target). For `γ`, `ρ`, a valid environment
`S`, a fixed `t > 0` and a positive input sequence `εs → 0`, one deterministic strictly monotone `φ`, chosen after `t`
and `εs`, satisfies almost surely: relative compactness `OdometerPreparedCompactness` of `εs ∘ φ`, and
`SubsequentialLimitProperties` for every uniform limit `w` of the rescaled least supersolutions along a further
subsequence of `εs ∘ φ`. The legacy `SubsequentialPropertiesStmt` puts `∀ t` inside the almost sure event after `φ`
(one `φ` for all `t`); that quantifier order is the audit's FAIL. -/
def SubsequentialPropertiesCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ᵐ ω ∂S.P,
      OdometerPreparedCompactness S ρ t (εs ∘ φ) ω ∧
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ w : ℂ → ℝ,
        TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs (φ (ψ n))) ω) w atTop
          (closedBall 0 ρ) →
        SubsequentialLimitProperties S ρ t ω w

/-- **Lemma 4.8, corrected**, from the corrected Lemma 4.6 `firstPass_4_6_corrected` (a.s. relative compactness along a
deterministic thinning, chosen after `t` and the input) and the limit-identification input
`OdometerPropertiesPreparedIdentificationStep 𝒮` (every uniform limit along a further thinning satisfies the four
clauses; Patch D of the audit). Proof: `φ` from the identification input, then `χ` from Lemma 4.6 applied to `εs ∘ φ`;
the subsequence is `φ ∘ χ`. Compactness of `(εs ∘ φ) ∘ χ` is the 4.6 conclusion; a uniform limit `w` along `φ ∘ χ` is
continuous by the Hölder clause of `OdometerPreparedCompactness`, and then it is a limit along `χ ∘ ψ` for the
identification input. -/
theorem firstPass_4_8_corrected {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮)
    (hid : OdometerPropertiesPreparedIdentificationStep 𝒮) :
    SubsequentialPropertiesCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht εs hεs hεs0
  obtain ⟨φ, hφ, hp⟩ := hid γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht εs hεs hεs0
  obtain ⟨χ, hχ, hc, -⟩ := firstPass_4_6_corrected hm h27 h218 hH h35 h37 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht
    (εs ∘ φ) (fun n => hεs _) (hεs0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ χ, hφ.comp hχ, ?_⟩
  filter_upwards [hp, hc] with ω hp hc
  refine ⟨hc, ?_⟩
  intro ψ hψ w hw
  have hcont : ContinuousOn w (closedBall 0 ρ) := by
    obtain ⟨_, a, ha, _, hH⟩ := hc.2 ψ hψ w hw
    exact hH.continuousOn ha
  exact hp w ⟨hcont, χ ∘ ψ, hχ.comp hψ, hw⟩

/-- Lemma 4.8, corrected, from the Draft statements of Lemmas 3.3, 3.5, 3.7 and the corrected maximum principle (2.13),
through `odometerPropertiesPreparedIdentificationStep_of_inputs` (Proofs/Sec4/SubsequentialProperties/PreparedIdentification.lean).
That proof passes through the legacy `SubsequentialPropertiesStmt` (`subsequentialProperties_of_inputs`); only the
identification step is taken from it, and the legacy statement is not the conclusion here. -/
theorem firstPass_4_8_corrected_of_inputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  firstPass_4_8_corrected hm h27 h218 hH h35 h37
    (odometerPropertiesPreparedIdentificationStep_of_inputs 𝒮 h33 h35 h37
      (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)))

end MatedCRT

#print axioms MatedCRT.firstPass_4_8_corrected
#print axioms MatedCRT.firstPass_4_8_corrected_of_inputs
