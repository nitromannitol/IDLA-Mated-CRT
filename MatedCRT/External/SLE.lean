import MatedCRT.Defs.Setting

/-!
# Literature inputs: whole-plane space-filling SLE and the mated-CRT map (ESCALATIONS E-A1, review-S (S7))

The space-filling SLE is the abstract model `𝒮 : SpaceFillingSLEModel` (MatedCRT/Defs/Setting.lean), whose predicate
`𝒮.IsSLE P 𝓕 κ η` stands for "under `P`, `η` viewed modulo increasing reparametrization is a whole-plane
space-filling SLE_κ from `∞` to `∞`, independent of `𝓕`". Every SLE-specific fact used by the proofs, beyond the
numbered cited results (drafted as Stmts in MatedCRT/Draft), enters only as one of the following hypotheses over the
model. Each is a true statement for the model whose predicate is the true one, with the source given. Listed in
INPUT-REQUESTS.md (IR-A3).

* `SLEScaleInvarianceInput`: `r η =d η` modulo parametrization (eq:eta-scale-invariant, line 619).
* `SLEReparametrizationInput`, `SLEIndepMonoInput`: the predicate is about `η` modulo increasing reparametrization,
  up to null sets, independent of `𝓕` (meaning of the model, lines 192-193, 621).
* `MepsScalingInput`: `m_ε ≍ ε⁻¹` (eq:meps-scaling, line 733; BG20 (1.8)).
* `DegreeBoundInput`: `max_{V^ε(B_ρ)} deg^ε ≤ (log ε⁻¹)²` (eq:degree-bound, line 3071; GMS19 Lemma 2.6).

Dropped after the graph switch (L1): `SpaceFillingSLEPathInput` (a.s. `|η(t)| → ∞`, and `a ∼ a + 1` in `𝒢^ε`). Both are
now theorems (MatedCRT/Proofs/Infra/MatingOfTrees.lean): `MatedCRTEnv.IsValid.ae_tendsto_cocompact` from the
mating-of-trees coupling of `MatedCRTEnv.IsValid` (fields `spaceFilling`, `areaParam`), and
`MatedCRTEnv.mult_succ_ne_zero` from Definition 1.1 for the continuous pair `bm` (deterministic). Local finiteness of
`𝒢^ε` follows from these and `AdjacentCellsMeetAeStep` (MatedCRT/Steps/Infra/MatingOfTrees.lean), a consequence of the
coupling (DMS14 Lemma 8.8, field `merge`), not an input.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Scale invariance of whole-plane space-filling SLE** (eq:eta-scale-invariant, line 619; Miller-Sheffield,
Imaginary geometry IV, Sections 1.2.3 and 4.3): `r η =d η` for every `r > 0`, as curves modulo time parametrization.
Stated for the model, for a positive `𝓕`-measurable random factor `R`: for deterministic `R ≡ r` it is the cited scale
invariance; for `𝓕`-measurable `R` it follows by conditioning on `𝓕`, of which `η` is independent. This is the form
used in the proof of Theorems 1.4 and 1.6 (line 3289, `η^b = R_b⁻¹ η(b ·)` with `R_b` a function of `h`). -/
def SLEScaleInvarianceInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (𝓕 : MeasurableSpace Ω) (κ : ℝ)
    (η : Ω → ℝ → ℂ), 4 < κ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η → ∀ R : Ω → ℝ, Measurable[𝓕] R → (∀ ω, 0 < R ω) →
      @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ fun ω s => (R ω : ℂ) * η ω s

/-- **The law of `η` is taken modulo increasing reparametrization and up to null sets** (lines 192-193, 621): if `η`
is a whole-plane space-filling SLE_κ independent of `𝓕`, so is every curve which a.s. is an increasing
reparametrization of `η` (e.g. `η(b ·)`, `b > 0`, or the `μ_h`-area parametrization). -/
def SLEReparametrizationInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (𝓕 : MeasurableSpace Ω) (κ : ℝ)
    (η η' : Ω → ℝ → ℂ), 4 < κ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η →
    (∀ᵐ ω ∂P, ∃ φ : ℝ ≃ₜ ℝ, StrictMono φ ∧ η' ω = η ω ∘ φ) →
      @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η'

/-- **Independence of a smaller σ-algebra** (meaning of the model, line 192): if `η` is a whole-plane space-filling
SLE_κ independent of `𝓕`, it is independent of every `𝓖 ≤ 𝓕` (e.g. the σ-algebra of the rescaled field `h^b`,
line 3286). -/
def SLEIndepMonoInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (𝓕 𝓖 : MeasurableSpace Ω) (κ : ℝ)
    (η : Ω → ℝ → ℂ), 4 < κ →
    @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓕 κ η → 𝓖 ≤ 𝓕 → @SpaceFillingSLEModel.IsSLE 𝒮 Ω mΩ P 𝓖 κ η

/-- **Scaling of `m_ε`** (eq:meps-scaling, line 733; BG20 eq. (1.8)): there is `C = C(γ) > 1` such that
`C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹` for all small `ε > 0`. -/
def MepsScalingInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ C : ℝ, 1 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → C⁻¹ * ε⁻¹ ≤ S.mε ε ∧ S.mε ε ≤ C * ε⁻¹

/-- **Degree bound** (eq:degree-bound, line 3071; GMS19 Lemma 2.6, as quoted in the proof of Lemma 7.4): with
polynomially high probability as `ε → 0`, `max_{a ∈ V^ε(B_ρ)} deg^ε(a) ≤ (log ε⁻¹)²`. -/
def DegreeBoundInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ((matedDeg (S.mult ε ω) a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2}

end MatedCRT
