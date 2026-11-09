import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# FIRST PASS: faithful statements of Lemmas 6.7, 6.8, 6.9 (task fp-S6d-6-9-faithful, q4)

Printed quantifier order (paper/idla_mated_crt-corrected.tex: `lemma:constant-order-lower-bound` at line 2743,
`lemma:constant-order-lower-bound-div` at line 2771, `lemma:chance-of-being-absorbed` at line 2959):
* the exponent `ω = ω(γ) > 0` of Lemmas 6.7, 6.8, 6.9 is deterministic and depends only on `γ`, so it is chosen
  before `ρ` (Lemma 6.9 also: `s₃` is chosen after `ρ` and before `s₀`);
* `β⁻` is the fixed exponent `chosenBetaMinus γ` (CHATGPT-s6-constants.md §1, the 21:27 UTC ruling).

The bodies (the event, `dd`, the probability bounds) are those of the Draft statements `ConstantOrderLowerBoundStmt`,
`ConstantOrderLowerBoundDivStmt` and `ChanceOfBeingAbsorbedStmt` (MatedCRT/Draft/Section6.lean), unchanged. Only the
quantifiers over `ω₀`, `s₃` and `β⁻` differ: the Draft headers choose `ω₀` after `ρ` and quantify `β⁻` over all
`β⁻ > (2+γ)²/2`. Neither Draft form implies the faithful one (see the report of this round).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The fixed exponent `β⁻ = B(γ) = (2+γ)²/2 + 1` (CHATGPT-s6-constants.md §1; the paper fixes `β⁻` depending only on
`γ` after Lemma 2.7). -/
noncomputable def chosenBetaMinus (γ : ℝ) : ℝ := (2 + γ) ^ 2 / 2 + 1

/-- The standing constant `c₀ = min{1/200, e^{-2C_G}/16}` (CHATGPT-s6-constants.md §2), with `C_G` the Green constant
of the reference radius. Taking `C_G` as an argument keeps the definition free of an undefined constant. Lemma 6.4 is
not restated here ([C18] keeps its header), so this definition is not yet used by a statement. -/
noncomputable def chosenC0 (CG : ℝ) : ℝ := min (1 / 200) (Real.exp (-2 * CG) / 16)

/-- **Lemma 6.7, faithful header** (`lemma:constant-order-lower-bound`, corrected tex line 2743). For `γ ∈ (0,2)` there
is a deterministic `ω₀ > 0` (depending only on `γ`, chosen before `ρ`) such that for every `ρ ∈ (0,1)` and `s₀ ∈ (0,1)`
there are `s₁, s₂ ∈ (0,1)` with the event and bound of the Draft `ConstantOrderLowerBoundStmt` (Draft/Section6.lean),
at `β⁻ = chosenBetaMinus γ`. -/
def FaithfulConstantOrderLowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ a ∈ vClosure (S.mult ε ω) Θ, ∀ S' ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)),
        ((S' \ Θ).ncard : ℝ) < s₁ * r ^ (2 * chosenBetaMinus γ) / ε →
        ENNReal.ofReal s₂ ≤ srwLaw (S.mult ε ω) a {x | ∃ n : ℕ,
          (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) x ∧
          x n ∈ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ (S' ∪ Θ)}}

/-- **Lemma 6.8, faithful header** (`lemma:constant-order-lower-bound-div`, corrected tex line 2771). Same quantifier
order as `FaithfulConstantOrderLowerBoundStmt`: `ω₀` depends only on `γ` and is chosen before `ρ`; `β⁻ = chosenBetaMinus γ`.
Body: the Draft `ConstantOrderLowerBoundDivStmt`. -/
def FaithfulConstantOrderLowerBoundDivStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ A ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ,
        (∀ z : ℂ, ((A ∩ cellVertices ε (S.η ω) (ball z r)).ncard : ℝ) < s₁ * r ^ (2 * chosenBetaMinus γ) / ε) →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (thickening (r / 2) (fillCells ε (S.η ω) Θ))),
          srwLaw (S.mult ε ω) a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂)}

/-- **Lemma 6.9, faithful header** (`lemma:chance-of-being-absorbed`, corrected tex line 2959). Quantifier order: `ω₀`
depends only on `γ` and is chosen before `ρ`; then the rate `s₃` (universal, deterministic) is chosen after `ρ` and
before `s₀`; `s₄, s₅` are chosen after `s₀`. `β⁻ = chosenBetaMinus γ`. Body: the Draft `ChanceOfBeingAbsorbedStmt`. -/
def FaithfulChanceOfBeingAbsorbedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ s₃ : ℝ, 0 < s₃ ∧ ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₄ s₅ : ℝ, 0 < s₄ ∧ s₄ < 1 ∧ 0 < s₅ ∧ s₅ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ (k : ℕ) (a : Fin k → ℤ), (k : ℝ) ≤ s₅ * r ^ (2 * chosenBetaMinus γ) / ε →
        (∀ i, a i ∈ vClosure (S.mult ε ω) Θ) →
        walkersLaw (S.mult ε ω) a {xs |
          ((idlaAggregate Θ (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) (List.ofFn xs) \
            Θ).ncard : ℝ) ≤ s₄ * k} ≤ ENNReal.ofReal (Real.exp (-s₃ * k))}

/-- **Uniform form of Lemma 6.7/6.8** (NOT printed). The printed Lemmas 6.7 and 6.8 choose `s₁, s₂` after `s₀`
(`FaithfulConstantOrderLowerBoundStmt`, `FaithfulConstantOrderLowerBoundDivStmt`). The printed Lemma 6.9 proof uses one
`s₂` for all walkers and all `s₀` (CHATGPT-6-9-printed-proof.md, "Inputs used"; LEMMA68.md proves the uniform choices
`s₁ = 1/4`, `s₂ = 1/2`). Here `s₁, s₂` are chosen after `ρ` and before `s₀`; the body is that of
`FaithfulConstantOrderLowerBoundStmt`. A rate `s₃` uniform in `s₀` needs this form: the walker absorption bound
`s₂(s₀)` of the printed 6.7/6.8 only gives the rate `s₂(s₀)/4` (`AbsorptionChernoffStep`). Input of
`firstPass_6_9_faithful`. -/
def UniformConstantOrderLowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ a ∈ vClosure (S.mult ε ω) Θ, ∀ S' ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)),
        ((S' \ Θ).ncard : ℝ) < s₁ * r ^ (2 * chosenBetaMinus γ) / ε →
        ENNReal.ofReal s₂ ≤ srwLaw (S.mult ε ω) a {x | ∃ n : ℕ,
          (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) x ∧
          x n ∈ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ (S' ∪ Θ)}}

/-- **Lemma 6.9, faithful header, from the uniform Lemma 6.7/6.8 input** (`firstPass_6_9_faithful`). Reduction: with
`ω₀, s₁, s₂` from `hU` (`ω₀` before `ρ`, `s₁, s₂` before `s₀`), the rate is `s₃ = s₂/4` and `s₄ = s₂/4`, `s₅ = s₁`;
`AbsorptionChernoffStep` (proved, Proofs/Sec6/ChanceOfBeingAbsorbed/Chernoff.lean) turns the walker-absorption bound
of the Lemma 6.7 event into the tail bound, pointwise on that event, and `ProbTendsToOne.mono'` transfers it. -/
theorem firstPass_6_9_faithful (𝒮 : SpaceFillingSLEModel) (hU : UniformConstantOrderLowerBoundStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hU'⟩ := hU γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, hU''⟩ := hU' ρ hρ0 hρ1
  refine ⟨s₂ / 4, by positivity, fun s₀ hs₀0 hs₀1 => ⟨s₂ / 4, s₁, by positivity, by linarith, hs₁0, hs₁1, ?_⟩⟩
  intro Ω _ S hS
  obtain ⟨dd, hdm, hdpos, hP⟩ := hU'' s₀ hs₀0 hs₀1 Ω S hS
  refine ⟨dd, hdm, hdpos, hP.mono' fun ε => ?_⟩
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω ⊢
  intro r hr1 hr2 Θ hΘ1 hΘ2 k a hk ha
  have hω' := hω r hr1 hr2 Θ hΘ1 hΘ2
  exact Absorption.absorptionChernoffStep (S.mult ε ω) Θ
    (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) s₂ (s₁ * r ^ (2 * chosenBetaMinus γ) / ε)
    hs₂0 hs₂1 (fun a' ha' S' hS' hlt => hω' a' ha' S' hS' hlt) k a hk ha

end MatedCRT
