import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff
import MatedCRT.FirstPass.S6d.Assemble
import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

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

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
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

/-- **Uniform form of Lemma 6.8** (NOT printed). LEMMA68.md proves Lemma 6.8 with the uniform choices `s₁ = 1/4`,
`s₂ = 1/2` ("Lemma 6.8 holds with s₁ = 1/4, s₂ = 1/2"), and reads "exits through A" as "the walk belongs to A at every
time strictly before its exit from the indicated vertex set" (LEMMA68.md verdict). The body is that of
`FaithfulConstantOrderLowerBoundDivStmt`; `s₁, s₂` are chosen after `ρ` and before `s₀`.

This is the exact missing clause of `firstPass_6_8_faithful`. `UniformConstantOrderLowerBoundStmt` (the 6.7 body) does
not imply it: the 6.8 event assumes only local smallness of `A` (for every ball of radius `r`), starts in
`∂(Θ̄ + B_{r/2})`, and the walk is stopped on entering `Θ`, while the 6.7 event assumes global smallness of `S'`,
starts in `cl(Θ)`, and exits `U` only. -/
def UniformConstantOrderLowerBoundDivStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
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

/-- **Lemma 6.7, faithful header, from the uniform input** (`firstPass_6_7_faithful`). The uniform statement has the
same body and the same quantifier order, with `s₁, s₂` chosen before `s₀`; the constants serve every `s₀`, so the
faithful header follows. Proof: exchange of the quantifiers `∃ s₁ s₂` and `∀ s₀`. -/
theorem firstPass_6_7_faithful (𝒮 : SpaceFillingSLEModel) (hU : UniformConstantOrderLowerBoundStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hU'⟩ := hU γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, hbody⟩ := hU' ρ hρ0 hρ1
  exact fun s₀ hs₀0 hs₀1 => ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, hbody s₀ hs₀0 hs₀1⟩

/-- **Lemma 6.8, faithful header, from the uniform Lemma 6.8 (conditional form, superseded).** Conditional on
`UniformConstantOrderLowerBoundDivStmt`; kept for the record. The unconditional-in-6.8 route is `firstPass_6_8_faithful`
(localization from `UniformConstantOrderLowerBoundStmt`). -/
theorem firstPass_6_8_faithful_of_uniform_div (𝒮 : SpaceFillingSLEModel) (hUD : UniformConstantOrderLowerBoundDivStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ω₀, hω₀, hU'⟩ := hUD γ hγ0 hγ2
  refine ⟨ω₀, hω₀, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, hbody⟩ := hU' ρ hρ0 hρ1
  exact fun s₀ hs₀0 hs₀1 => ⟨s₁, s₂, hs₁0, hs₁1, hs₂0, hs₂1, hbody s₀ hs₀0 hs₀1⟩

/-- The cell-size exponent `2/(2+γ)² − ζ` of `CellSizeEstimateStmt` at `ζ = 1/16` is positive for `γ ∈ (0,2)`. -/
theorem cellSizeExponent_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 0 < 2 / (2 + γ) ^ 2 - 1 / 16 := by
  have h1 : (2 + γ) ^ 2 < 16 := by nlinarith
  have h2 : 0 < (2 + γ) ^ 2 := by positivity
  have h3 : 1 / 8 < 2 / (2 + γ) ^ 2 := by
    rw [lt_div_iff₀ h2]
    nlinarith
  linarith

/-- **Lemma 6.8, faithful header, from the uniform Lemma 6.7** (`firstPass_6_8_faithful`, task fp-S6e-6-7-6-8-from-uniform).
Localization (CHATGPT-6-9-claims-referee.md, "Do faithful 6.7 and 6.8 follow?"): the starting vertex `a` of the walk
lies on the frontier of `Θ + B_{r/2}`; the localized sets `W₁ = V(B_{r/8}(cell a))` and `W₀ = V(B_{r/8}(Θ̄))` are not
joined by an edge; the uniform Lemma 6.7 applied to `Θ ∪ {a}` at radius `r/8` with `S' = A ∩ W₁` and the constant
`s₁ = s₁'/8^{2β⁻}` gives the bound. Inputs beyond `UniformConstantOrderLowerBoundStmt`: `VolumeGrowthStmt` and
`CellSizeEstimateStmt` (Draft Lemmas 2.7 and 2.8, the cell-size estimate of the paper, used by the finiteness step
`cellVerticesBallFiniteStep` and by the cell diameters). Exponents: `ζ = 1/16`, `κ = 2/(2+γ)² − 1/16`, `ω₀ = min(ω_U, κ)/2`. -/
theorem firstPass_6_8_faithful (𝒮 : SpaceFillingSLEModel) (hU : UniformConstantOrderLowerBoundStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) : FaithfulConstantOrderLowerBoundDivStmt 𝒮 := by
  intro γ hγ0 hγ2
  obtain ⟨ωU, hωU, hU'⟩ := hU γ hγ0 hγ2
  have hκ : 0 < 2 / (2 + γ) ^ 2 - 1 / 16 := cellSizeExponent_pos hγ0 hγ2
  set κ : ℝ := 2 / (2 + γ) ^ 2 - 1 / 16 with hκdef
  set ωd : ℝ := min ωU κ / 2 with hωddef
  have hωd0 : 0 < ωd := div_pos (lt_min hωU hκ) two_pos
  have hωdU : ωd < ωU := by
    have := min_le_left ωU κ
    rw [hωddef]
    linarith
  have hωdκ : ωd < κ := by
    have := min_le_right ωU κ
    rw [hωddef]
    linarith
  refine ⟨ωd, hωd0, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨s1', s2', hs1'0, hs1'1, hs2'0, hs2'1, hbody⟩ := hU' ((1 + ρ) / 2) (by linarith) (by linarith)
  intro s₀ hs₀0 hs₀1
  refine ⟨s1' / 8 ^ (2 * chosenBetaMinus γ), s2', ?_, ?_, hs2'0, hs2'1, ?_⟩
  · positivity
  · have h8 : (1 : ℝ) ≤ 8 ^ (2 * chosenBetaMinus γ) :=
      Real.one_le_rpow (by norm_num) (by unfold chosenBetaMinus; positivity)
    rw [div_lt_one (by positivity)]
    linarith
  intro Ω _ S hS
  obtain ⟨dd67, hdm67, hdpos67, hP67⟩ := hbody s₀ hs₀0 hs₀1 Ω S hS
  refine ⟨fun ω => min (8 * dd67 ω) ((1 - ρ) / 8), ((hdm67.const_mul 8).min measurable_const),
    fun ω => lt_min (by linarith [hdpos67 ω]) (div_pos (by linarith) (by norm_num)), ?_⟩
  -- the good event: the uniform 6.7 event, the cell-size estimate, finiteness, continuity, edge-cell contacts
  have hCS : ProbTendsToOne S.P (fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + 1 / 16) ≤ diam (cell ε (S.η ω) k) ∧
        diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / 16)}) :=
    HarmonicBalls.PolyHighProb.probTendsToOne (h28 γ hγ0 hγ2 (1 / 16) ((1 + ρ) / 2) (by norm_num) (by norm_num) (by linarith) (by linarith) Ω S hS)
  have hFin : ProbTendsToOne S.P (fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))).Finite}) :=
    cellVerticesBallFiniteStep 𝒮 h27 h28 γ hγ0 hγ2 ((1 + ρ) / 2) (by linarith) (by linarith) Ω S hS
  have hCont : ProbTendsToOne S.P (fun _ => {ω | Continuous (S.η ω)}) :=
    loc_pt_of_ae (hS.isAreaParametrized.mono fun ω h => h.1)
  have hADJ : ProbTendsToOne S.P (fun _ => {ω | ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty}) :=
    loc_pt_of_ae (adjacentCellsMeetAeStep 𝒮 γ hγ0 hγ2 Ω S hS)
  have hgood := loc_pt_inter (loc_pt_inter (loc_pt_inter (loc_pt_inter hP67 hCS) hFin) hCont) hADJ
  have hκωd : 0 < κ - ωd := by linarith
  have hωUωd : 0 < ωU - ωd := by linarith
  refine loc_pt_mono_ev hgood ?_
  filter_upwards [loc_eventually_rpow_lt hωUωd (K := 1 / 8) (by norm_num),
    loc_eventually_rpow_lt hκωd (K := 1 / 10) (by norm_num), self_mem_nhdsWithin] with ε hε8 hε10 hεpos
  have hε : 0 < ε := hεpos
  have hε8' : 8 * ε ^ ωU < ε ^ ωd := loc_mul_rpow_lt hε (by norm_num) hε8
  have hε10' : 10 * ε ^ κ < ε ^ ωd := loc_mul_rpow_lt hε (by norm_num) hε10
  rintro ω ⟨⟨⟨⟨h67, hcs⟩, hfin⟩, hcont⟩, hadj⟩
  simp only [Set.mem_ofPred_eq]
  intro r hr1 hr2 Θ hΘ1 hΘ2 A hA hloc a ha
  -- numerical bounds on the radius
  have hεd : 0 < ε ^ ωd := Real.rpow_pos_of_pos hε _
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr1
  have hrρ : r ≤ (1 - ρ) / 8 := le_trans hr2 (min_le_right _ _)
  have hr67 : r ≤ 8 * dd67 ω := le_trans hr2 (min_le_left _ _)
  have ht8 : 10 * ε ^ ωU ≤ r / 8 := by linarith
  have ht8' : r / 8 ≤ dd67 ω := by linarith
  have hdr : ε ^ κ < r / 100 := by linarith
  -- cell geometry on the good event
  have hdiam : ∀ v : ℤ, (cell ε (S.η ω) v ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε (S.η ω) v, ∀ y ∈ cell ε (S.η ω) v, dist x y ≤ ε ^ κ :=
    fun v hv => dist_le_of_diam_le hcont (hcs v hv).2
  have hadj' : ∀ v w : ℤ, S.mult ε ω v w ≠ 0 → (cell ε (S.η ω) v ∩ cell ε (S.η ω) w).Nonempty :=
    fun v w h => hadj ε hε v w h
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    loc_core (m := S.mult ε ω) hε.le hρ0 hr0 hrρ hdr hΘ1 hdiam hadj' ha
  -- the uniform Lemma 6.7 for the augmented cluster `Θ ∪ {a}` at radius `r/8`
  have hc1 : closure (fillCells ε (S.η ω) (insert a Θ)) ⊆ ball 0 ((1 + ρ) / 2 / 2) := by
    rw [show (1 + ρ) / 2 / 2 = (1 + ρ) / 4 by ring]
    exact c1
  have hball : ball 0 s₀ ⊆ fillCells ε (S.η ω) (insert a Θ) :=
    hΘ2.trans (by rw [fillCells_insert_eq]; exact subset_union_right)
  have ha' : a ∈ vClosure (S.mult ε ω) (insert a Θ) := Or.inl (mem_insert a Θ)
  set W1 := cellVertices ε (S.η ω) (thickening (r / 8) (cell ε (S.η ω) a)) with hW1
  set W0 := cellVertices ε (S.η ω) (thickening (r / 8) (fillCells ε (S.η ω) Θ)) with hW0
  have hsub : A ∩ W1 ⊆ cellVertices ε (S.η ω) (thickening (r / 8) (fillCells ε (S.η ω) (insert a Θ))) := by
    rw [cellVertices_thick_fill_insert]
    exact fun v hv => Or.inl hv.2
  -- the number of walkers allowed in `A ∩ W₁` is controlled by the local smallness of `A`
  have hfinV : (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).Finite :=
    Set.Finite.subset hfin (cellVertices_mono_set ε (S.η ω) c6)
  have hsub2 : (A ∩ W1) \ insert a Θ ⊆ A ∩ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r) :=
    fun x hx => ⟨hx.1.1, c5 x hx.1.2⟩
  have hfinA : (A ∩ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).Finite :=
    hfinV.subset inter_subset_right
  have hncard_le : (((A ∩ W1) \ insert a Θ).ncard : ℝ) ≤
      ((A ∩ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) r)).ncard : ℝ) :=
    Nat.cast_le.2 (Set.ncard_le_ncard hsub2 hfinA)
  have hloc' := hloc (vertexPoint ε (S.η ω) a)
  have hpow : s1' / 8 ^ (2 * chosenBetaMinus γ) * r ^ (2 * chosenBetaMinus γ) / ε =
      s1' * (r / 8) ^ (2 * chosenBetaMinus γ) / ε := by
    rw [Real.div_rpow hr0.le (by norm_num)]
    ring
  have hncard : (((A ∩ W1) \ insert a Θ).ncard : ℝ) < s1' * (r / 8) ^ (2 * chosenBetaMinus γ) / ε := by
    rw [← hpow]
    linarith
  have h67' := h67 (r / 8) ht8 ht8' (insert a Θ) hc1 hball a ha' (A ∩ W1) hsub hncard
  have hunion : cellVertices ε (S.η ω) (thickening (r / 8) (fillCells ε (S.η ω) (insert a Θ))) = W0 ∪ W1 := by
    rw [cellVertices_thick_fill_insert, Set.union_comm]
  rw [hunion] at h67'
  exact srw_localized_bound (S.mult ε ω) a A
    (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ) W0 W1 (insert a Θ)
    hs2'0.le c2 c4 c3 h67'

end MatedCRT
