import MatedCRT.Draft.Section2
import MatedCRT.Steps.Sec6.ChanceOfBeingAbsorbed

/-!
# Lemma 6.10 (lemma:iterative-bound, line 2694): carving of the proof (lines 2706-2838)

The printed proof iterates Lemma 6.9 with the Abelian property (Lemma 6.3): with `Θ⁰ = Θ`, `P₀ = (a₁, …, a_j)`, the
`k`-th round releases the walkers `P_{k-1}`, stopped upon exiting `V^ε(Θ̄^{k-1} + B_{r_k})` with
`r_k = max((|P_{k-1}| ε s₅⁻¹)^{1/2β⁻}, 10 ε^ω)`; Lemma 6.9 makes `|P_k| ≤ (1 - s₄)|P_{k-1}|` except on an event of
probability `e^{-s₃|P_{k-1}|}` (Steps 1-2, union bound over the rounds), and the last `ε^{-ω₀}` walkers spread by at
most `ε^{-ω₀}` cell diameters (Step 3, Lemma 2.8). The radii sum to `O(δ₀^{1/2β⁻})` (Step 4).

Carving. The quenched part (one environment `(m, η)`, the conclusions of Lemmas 6.3, 6.9 and 2.8 as hypotheses) is
`QuenchedIterationStep`; `iterativeBound_of_steps` (MatedCRT/Proofs/Sec6/IterativeBound/OfSteps.lean) chooses the
parameters and passes to the annealed outer integral of the Draft.

Departures from the printed proof, all reported (ESCALATIONS E-c5-2 and the report of worker c5):
* **Lemma 6.3 with arbitrary starting sites** (`AbelianIDLAAnyStartStep`). The frozen `AbelianIDLAStmt` assumes
  `a₁, …, a_k ∈ Θ` (as printed, line 2306), but Lemma 6.10 starts at `a_i ∈ cl(Θ)` and every round restarts the
  walkers at `P_{k-1} ⊆ ∂Θ'_{k-1}`, outside `Θ^{k-1}` (lines 2717-2726); Lemma 6.3's own conclusion restarts outside
  `Θ` too. The Abelian property of Diaconis-Fulton (1991, Section 4) holds for arbitrary starting sites.
* **Lemma 6.9 at `(1 + ρ)/2`.** Lemma 6.9 requires `Θ̄ ⋐ B_{ρ/2}`, but the clusters `Θ^k` of the iteration are only
  in `B_{ρ/2 + R}` (line 2837: `R < ρ/4`). Lemma 6.9 is applied with `(1 + ρ)/2` in place of `ρ`, and `R < (1-ρ)/4`.
* **Lemma 6.9 in the E-A10 (b) form** (`ChanceOfBeingAbsorbedLogLossStmt`): the rates `s₃, s₄` carry the factor
  `(1 + |log r|)⁻²`, and `s₃` is chosen after `s₀` (E-c5-1). It is implied by the drafted Lemma 6.9 and by its
  local-rate reading (`ChanceOfBeingAbsorbedLocalRateStmt.logLoss`). The halving time of `|P_k|` grows by
  `(1 + |log r_k|)²`, which the exponent `β < 1/(2β⁻)` absorbs (the constant `C(s₄, s₅)` of line 2835 too, so `C = 1`).
* **Adjacent cells meet** (`AdjacentCellsMeetStep`): Step 3 and the restart sites use that the cells of adjacent
  vertices intersect. This is Definition 1.2; the map of `MatedCRTEnv.mult` is Definition 1.1, and the equivalence is
  Duplantier-Miller-Sheffield (mating of trees) Theorem 1.9 / Lemma 8.8 (INPUT-REQUESTS IR-A2).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-! ## Quenched notions (one environment) -/

/-- The **Abelian property of IDLA** (Lemma 6.3, Diaconis-Fulton 1991, Section 4) on the multigraph `m`, for
arbitrary starting sites: the law of the aggregate `A(Θ; a₁, …, a_k)` is that of the restarted aggregate
`A(A(Θ; a → Θ'); P(Θ; a → Θ'))`, compared on each value `B`. -/
def IsAbelianIDLA (m : ℤ → ℤ → ℕ) : Prop :=
  ∀ (Θ Θ' : Set ℤ) (k : ℕ) (a : Fin k → ℤ), Θ ⊆ Θ' → ∀ B : Set ℤ,
    walkersLaw m a {xs | idlaAggregate Θ univ (List.ofFn xs) = B} =
      ∫⁻ xs, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = B}
        ∂walkersLaw m a

/-- Simple random walk on `m` started at `a` almost surely starts at `a` and moves along edges (or stays put, junk at
vertices of degree `0` or `∞`). -/
def IsSrwPathLaw (m : ℤ → ℤ → ℕ) : Prop :=
  ∀ a : ℤ, ∀ᵐ x ∂srwLaw m a, x 0 = a ∧ ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0

/-- The conclusion of Lemma 6.9 (E-A10 (b) form) for one environment `(m, ε, η)` with the parameters `ρ, β⁻, ω, s₀,
s₃, s₄, s₅` and the value `dd` of the random radius `𝛅`: for `r ∈ [10 ε^ω, dd]`, `Θ̄ ⋐ B_{ρ/2}`, `B_{s₀} ⊆ Θ̄`,
`k ≤ s₅ r^{2β⁻} ε⁻¹` and `a₁, …, a_k ∈ cl(Θ)`,
`P[|A(Θ; a → V^ε(Θ̄ + B_r)) \ Θ| ≤ s₄ (1 + |log r|)⁻² k] ≤ exp(-s₃ (1 + |log r|)⁻² k)`. -/
def AbsorptionBound (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (ρ βm ω₀ s₀ s₃ s₄ s₅ dd : ℝ) : Prop :=
  ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd → ∀ Θ : Set ℤ,
    closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η Θ →
    ∀ (k : ℕ) (a : Fin k → ℤ), (k : ℝ) ≤ s₅ * r ^ (2 * βm) / ε → (∀ i, a i ∈ vClosure m Θ) →
      walkersLaw m a {xs |
        ((idlaAggregate Θ (cellVertices ε η (thickening r (fillCells ε η Θ))) (List.ofFn xs) \ Θ).ncard : ℝ) ≤
          s₄ / (1 + |Real.log r|) ^ 2 * k} ≤
        ENNReal.ofReal (Real.exp (-(s₃ / (1 + |Real.log r|) ^ 2) * k))

/-! ## Statement forms of the inputs -/

/-- **Lemma 6.9** in the form of the E-A10 verdict (b) (ESCALATIONS, "STATEMENT CHANGES (b)", 6.9), with the order of
quantifiers of E-c5-1 (`s₃` after `s₀`): the rates are `s₃ (1 + |log r|)⁻²` and `s₄ (1 + |log r|)⁻²`. -/
def ChanceOfBeingAbsorbedLogLossStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm →
  ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₃ s₄ s₅ : ℝ, 0 < s₃ ∧ 0 < s₄ ∧ s₄ < 1 ∧ 0 < s₅ ∧ s₅ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | AbsorptionBound (S.mult ε ω) ε (S.η ω) ρ βm ω₀ s₀ s₃ s₄ s₅ (dd ω)}

/-- The local-rate reading of Lemma 6.9 (E-c5-1) implies the E-A10 (b) form (the rates only decrease). -/
theorem ChanceOfBeingAbsorbedLocalRateStmt.logLoss {𝒮 : SpaceFillingSLEModel}
    (h : ChanceOfBeingAbsorbedLocalRateStmt 𝒮) : ChanceOfBeingAbsorbedLogLossStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβm
  obtain ⟨ω₀, hω₀, h⟩ := h γ hγ hγ2 ρ hρ hρ1 βm hβm
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₃, s₄, s₅, hs₃, hs₄, hs₄1, hs₅, hs₅1, h⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₃, s₄, s₅, hs₃, hs₄, hs₄1, hs₅, hs₅1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hE⟩ := h Ω S hS
  refine ⟨dd, hdd, hddpos, hE.mono' fun ε ω hω => ?_⟩
  intro r hr1 hr2 Θ hΘ1 hΘ2 k a hk ha
  have hL : 1 ≤ (1 + |Real.log r|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine (measure_mono fun xs hxs => ?_).trans ((hω r hr1 hr2 Θ hΘ1 hΘ2 k a hk ha).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
  · refine le_trans (show _ ≤ s₄ / (1 + |Real.log r|) ^ 2 * k from hxs) ?_
    exact mul_le_mul_of_nonneg_right (div_le_self hs₄.le hL) hk0
  · have : s₃ / (1 + |Real.log r|) ^ 2 ≤ s₃ := div_le_self hs₃.le hL
    nlinarith

/-- The drafted Lemma 6.9 implies its E-A10 (b) form. -/
theorem ChanceOfBeingAbsorbedStmt.logLoss {𝒮 : SpaceFillingSLEModel} (h : ChanceOfBeingAbsorbedStmt 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 :=
  h.localRate.logLoss

/-! ## Steps -/

/-- Step (literature input, ESCALATIONS E-c5-2): **Lemma 6.3 for arbitrary starting sites** (Diaconis-Fulton 1991,
Section 4), almost surely for all `ε > 0`. It is `AbelianIDLAStmt` without the hypothesis `a₁, …, a_k ∈ Θ`. -/
def AbelianIDLAAnyStartStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsAbelianIDLA (S.mult ε ω)

/-- `AbelianIDLAAnyStartStep` strengthens the frozen Lemma 6.3. -/
theorem AbelianIDLAAnyStartStep.abelianIDLA {𝒮 : SpaceFillingSLEModel} (h : AbelianIDLAAnyStartStep 𝒮) :
    AbelianIDLAStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS
  filter_upwards [h γ hγ hγ2 Ω S hS] with ω hω ε hε Θ Θ' k a hΘ _ B
  exact hω ε hε Θ Θ' k a hΘ B

/-- Step (literature input, INPUT-REQUESTS IR-A2: Duplantier-Miller-Sheffield, mating of trees, Theorem 1.9 /
Lemma 8.8, the equivalence of Definitions 1.1 and 1.2): with probability tending to `1`, the cells of adjacent
vertices of `V^ε(B_ρ)` intersect. -/
def AdjacentCellsMeetStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ProbTendsToOne S.P fun ε => {ω | ∀ a b : ℤ, a ∈ cellVertices ε (S.η ω) (ball 0 ρ) → S.mult ε ω a b ≠ 0 →
      (cell ε (S.η ω) a ∩ cell ε (S.η ω) b).Nonempty}

/-- Step (any multigraph): simple random walk starts at its starting site and moves along edges. -/
def SrwPathStep : Prop :=
  ∀ m : ℤ → ℤ → ℕ, IsSrwPathLaw m

/-- Step (modeling; the `σ(h)` half of `EnvSigmaMeasurableStep`, MatedCRT/Steps/Sec5/GeneralIDLALowerBound.lean):
the field is a random variable, i.e. `σ(h)` is contained in the σ-algebra of `Ω`. Used for `P[𝛅 < τ] → 0` as
`τ → 0` for the `σ(h)`-measurable radius `𝛅 > 0` of Lemma 6.9. -/
def FieldSigmaMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    S.fieldSigma ≤ mΩ

/-- Step (the quenched iteration, lines 2706-2838, for one environment). Fix `ρ`, the exponent `β⁻` and the exponent
`ω` of Lemma 6.9, and a cell-size exponent `κ > 0` (Lemma 2.8: `diam H^ε_a ≤ ε^κ`). There is `β > 0` such that for
all `s₀` and rates `s₃, s₄, s₅` there is `D₀ > 0` with the following property: for each `τ > 0` there is an error
`θ(ε) → 0` such that for all small `ε`, every environment `(m, η)` with radius `dd ≥ τ` satisfying the Abelian
property, the walk path property, the conclusion of Lemma 6.9 at `(1 + ρ)/2`, the intersection of adjacent cells and
the cell-size bound in `B_{(1+ρ)/2}`, and all `Θ̄ ⋐ B_{ρ/2}` with `B_{s₀} ⊆ Θ̄`, `δ₀ < D₀ ∧ δ₀ < s₅ (dd ∧ 1)^{2β⁻}/2`,
`j ≤ ⌈δ₀ ε⁻¹⌉` and `a₁, …, a_j ∈ cl(Θ)`:
`P[A(Θ; a₁, …, a_j) ⊄ V^ε(B⁺_{δ₀^β}(Θ̄)) or V^ε(B⁺_{δ₀^β}(Θ̄)) ⊄ V^ε(B_ρ)] ≤ θ(ε)`.
(`β < min(1/(2β⁻), ω, κ)/2`, so that the error terms `C(s₄, s₅) δ₀^{1/2β⁻} (1 + log δ₀⁻¹)²`,
`C log³ε⁻¹ (ε^ω + ε^κ)` and `ε^{κ - ω₀}` of Steps 1-3 are at most `δ₀^β` uniformly in `δ₀`.) -/
def QuenchedIterationStep : Prop :=
  ∀ ρ βm ω₀ κ : ℝ, 0 < ρ → ρ < 1 → 0 < βm → 0 < ω₀ → 0 < κ →
  ∃ β : ℝ, 0 < β ∧
  ∀ s₀ s₃ s₄ s₅ : ℝ, 0 < s₀ → 0 < s₃ → 0 < s₄ → s₄ < 1 → 0 < s₅ → s₅ < 1 →
  ∃ D₀ : ℝ, 0 < D₀ ∧
  ∀ τ : ℝ, 0 < τ → ∃ θ : ℝ → ℝ≥0∞, Tendsto θ (𝓝[>] 0) (𝓝 0) ∧
  ∀ᶠ ε in 𝓝[>] 0, ∀ (m : ℤ → ℤ → ℕ) (η : ℝ → ℂ) (dd : ℝ), τ ≤ dd → Continuous η →
    IsAbelianIDLA m → IsSrwPathLaw m →
    AbsorptionBound m ε η ((1 + ρ) / 2) βm ω₀ s₀ s₃ s₄ s₅ dd →
    (∀ a b : ℤ, a ∈ cellVertices ε η (ball 0 ((1 + ρ) / 2)) → m a b ≠ 0 →
      (cell ε η a ∩ cell ε η b).Nonempty) →
    (∀ a ∈ cellVertices ε η (ball 0 ((1 + ρ) / 2)), diam (cell ε η a) ≤ ε ^ κ) →
    ∀ Θ : Set ℤ, closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε η Θ →
    ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ < D₀ → δ₀ < s₅ * min dd 1 ^ (2 * βm) / 2 →
    ∀ j : ℕ, j ≤ ⌈δ₀ / ε⌉₊ → ∀ a : Fin j → ℤ, (∀ i, a i ∈ vClosure m Θ) →
      walkersLaw m a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
          cellVertices ε η (outerNbhd (δ₀ ^ β) (fillCells ε η Θ)) ∧
        cellVertices ε η (outerNbhd (δ₀ ^ β) (fillCells ε η Θ)) ⊆ cellVertices ε η (ball 0 ρ))} ≤ θ ε

end MatedCRT
