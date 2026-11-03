import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 6: statements of Proposition 6.1 and Lemmas 6.3-6.10 (lines 2232-2911)

The IDLA upper bound. Conventions: see `MatedCRT/Draft/Section1.lean`. `ρ ∈ (0, 1)` is fixed and universally
quantified.

* Definition 6.2 (stopped IDLA aggregates) is `idlaAggregate Θ Θ' xs` / `idlaStopped Θ Θ' xs`
  (MatedCRT/Defs/RandomWalk.lean); `k` walkers from `a₁, …, a_k` have law `walkersLaw m a`.
* `Θ̄` is `fillCells ε η Θ`; `Θ̄ + B_r = {x + y : x ∈ Θ̄, |y| < r}` is `Metric.thickening r Θ̄`; `Θ̄ ⋐ B_{ρ/2}` is
  `closure Θ̄ ⊆ B_{ρ/2}`.
* `β⁻` is the exponent of Lemma 2.7, "fixed depending only on `γ`" (line 665): the statements quantify over every
  admissible `β⁻ > (2 + γ)²/2`.
* `𝐜₀ ∈ (0, 1/5)` is the constant of eq:choice-of-constant-annulus (line 2302), chosen from the constant of
  Lemma 2.16; the statements of Lemmas 6.4 and 6.5 quantify over every `𝐜₀ ∈ (0, 1/5)`.
* "A random `σ(h)`-measurable `𝛅 > 0`" is `𝛅 : Ω → ℝ`, measurable for `S.fieldSigma`, positive.

Cited: Lemma 6.3 (Diaconis-Fulton 1991, Section 4), Lemma 6.6 (Gwynne-Miller, local metrics of the GFF; stated for the
whole-plane GFF).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 6.1** (prop:IDLA-upper-bound, line 2236). For each `δ ∈ (0, ρ)` and `t > 0`, on the event `{t < T}`,
except on an event of probability tending to `0` as `ε → 0`, `Ā_ε(⌊t ε⁻¹⌋) ⊆ B⁺_δ(Λ_t)`. -/
def IDLAUpperBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    Tendsto (fun ε => ∫⁻ ω in {ω | t < clusterExitTime (Λ ω) ρ}, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ fillCells ε (S.η ω) (idlaCluster xs ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ ω t)} ∂S.P)
      (𝓝[>] 0) (𝓝 0)

/-- **Lemma 6.3** (lemma:abelian-IDLA, line 2289; Diaconis-Fulton 1991, Section 4). For `Θ ⊆ Θ' ⊆ V^ε` and
`a₁, …, a_k ∈ Θ`, the conditional laws given `(h, η)` of `A(Θ; a₁, …, a_k)` and of the restarted aggregate
`A(A(Θ; a₁, …, a_k → Θ'); P(Θ; a₁, …, a_k → Θ'))` agree: the second runs `k` stopped walkers, then restarts one fresh
independent walker from each stopped position (`P` is the list of stopped positions, ESCALATIONS E-A5) with the
aggregate of the first stage occupied. Stated almost surely, for all `ε > 0` and all (in particular all
`σ(h, η)`-measurable) choices; the laws are compared on each value `B` of the aggregate. -/
def AbelianIDLAStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ (Θ Θ' : Set ℤ) (k : ℕ) (a : Fin k → ℤ), Θ ⊆ Θ' → (∀ i, a i ∈ Θ) →
    ∀ B : Set ℤ,
      walkersLaw (S.mult ε ω) a {xs | idlaAggregate Θ univ (List.ofFn xs) = B} =
        ∫⁻ xs, walkersLaw (S.mult ε ω) (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
            (idlaStopped Θ Θ' (List.ofFn xs)).get i)
          {ys | idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) = B}
          ∂walkersLaw (S.mult ε ω) a

/-- **Lemma 6.4** (lemma:good-prevalance, line 2318). There is a constant `C` (depending only on `γ`, and on the fixed
`ρ`, `𝐜₀`) such that with polynomially high probability as `δ → 0`: for each
`z ∈ (B_{ρ - 3√δ} \ B_{10√δ}) ∩ (δ/100) ℤ²` there is at least one radius `r ∈ [δ, δ^{1/2}] ∩ {7^{-n}}_{n ∈ ℕ}` for which
`E_r(z; C)` occurs. -/
def GoodAnnulusPrevalenceStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  PolyHighProb P fun δ => {ω | ∀ z : ℂ, z ∈ ball 0 (ρ - 3 * Real.sqrt δ) \ ball 0 (10 * Real.sqrt δ) →
    (∃ m n : ℤ, z = ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)) →
    ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulusEvent (μ ω) c₀ C r z}

/-- **Lemma 6.5** (lemma:annulus-hit, line 2333). For each `p ∈ (0, 1)` there is `C = C(p) > 0` such that
`P[E_r(z; C)] ≥ p` for all `r > 0` and all `z` with `𝔸_{r/3,3r}(z) ⊆ B_ρ` and `dist(𝔸_{r/3,3r}(z), {0}) ≥ r/100`. -/
def AnnulusHitStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ c₀ : ℝ, 0 < c₀ → c₀ < 1 / 5 →
  ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → annulus z (r / 3) (3 * r) ⊆ ball 0 ρ →
    r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)) →
    ENNReal.ofReal p ≤ P {ω | IsGoodAnnulusEvent (μ ω) c₀ C r z}

/-- **Lemma 6.6** (lemma:annulus-iterate, line 2371; Gwynne-Miller). Fix `0 < s₁ < s₂ < 1`. Let `{r_k}` be decreasing
positive numbers with `r_{k+1}/r_k ≤ s₁`, and `{E_{r_k}}` events with `E_{r_k}` a.s. determined by `h|_{𝔸_{s₁ r_k, s₂ r_k}(0)}`
viewed modulo additive constant. Let `N(K)` be the number of `k ∈ [1, K]` for which `E_{r_k}` occurs. For each
`α > 0` there are `p = p(α, s₁, s₂) ∈ (0, 1)` and `C = C(α, s₁, s₂) > 0` (independent of `{r_k}`, `{E_{r_k}}`) such that
if `P[E_{r_k}] ≥ p` for all `k` then `P[N(K) = 0] ≤ C e^{-αK}` for all `K`. Stated for the whole-plane GFF `h = h^ℂ`
(`IsWholePlaneGFF`), the field of the source. "A.s. determined" is: equal up to a null set to an event of the
σ-algebra generated by the mean-zero pairings supported in the annulus (`modConstSigma`). -/
def AnnulusIterateStmt : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ α : ℝ, 0 < α → ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
  ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω), Antitone r → (∀ k, 0 < r k) → (∀ k, r (k + 1) / r k ≤ s₁) →
    (∀ k, ∃ E' : Set Ω, MeasurableSet[modConstSigma hC (annulus 0 (s₁ * r k) (s₂ * r k))] E' ∧ E k =ᵐ[P] E') →
    (∀ k, ENNReal.ofReal p ≤ P (E k)) →
    ∀ K : ℕ, P {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} ≤ ENNReal.ofReal (C * Real.exp (-α * K))

/-- **Lemma 6.7** (lemma:constant-order-lower-bound, line 2410). There is a deterministic `ω₀ = ω(γ) > 0` such that
for each `s₀ ∈ (0, 1)` there are `s₁, s₂ ∈ (0, 1)` and a random `σ(h)`-measurable `𝛅 > 0` such that with probability
tending to `1` as `ε → 0`, for all `r ∈ [10 ε^{ω₀}, 𝛅]` and all `Θ ⊆ V^ε` with `Θ̄ ⋐ B_{ρ/2}` and `B_{s₀} ⊆ Θ̄`: for
each `a ∈ cl(Θ)` and `S' ⊆ V^ε(Θ̄ + B_r)` with `|S' \ Θ| < s₁ r^{2β⁻} ε⁻¹`, the trace `Ξ` of a random walk started at
`a` and stopped upon exiting `V^ε(Θ̄ + B_r)` satisfies `P[Ξ ∩ V^ε(Θ̄ + B_r) \ (S' ∪ Θ) ≠ ∅ | h, η] ≥ s₂`. -/
def ConstantOrderLowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm → ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ a ∈ vClosure (S.mult ε ω) Θ, ∀ S' ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)),
        ((S' \ Θ).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε →
        ENNReal.ofReal s₂ ≤ srwLaw (S.mult ε ω) a {x | ∃ n : ℕ,
          (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) x ∧
          x n ∈ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ (S' ∪ Θ)}}

/-- **Lemma 6.8** (lemma:constant-order-lower-bound-div, line 2438). Same quantifiers as Lemma 6.7. For all
`A ⊆ V^ε(Θ̄ + B_r) \ Θ` with `|A ∩ V^ε(B_r(z))| < s₁ r^{2β⁻} ε⁻¹` for all `z ∈ ℂ`,
`sup_{a ∈ V^ε(∂(Θ̄ + B_{r/2}))} P[X^{a,ε} exits V^ε(Θ̄ + B_r) \ Θ through A | h, η] ≤ 1 - s₂`.
"Exits `U = V^ε(Θ̄ + B_r) \ Θ` through `A`" is read as: the walk stays in `A` until it exits `U` (the walk exits via
a path inside `A`; this is how it is used in the proof of Lemma 6.7, lines 2449-2461, and Figure 7; ESCALATIONS
E-A9). -/
def ConstantOrderLowerBoundDivStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm → ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧ 0 < s₂ ∧ s₂ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ A ⊆ cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ,
        (∀ z : ℂ, ((A ∩ cellVertices ε (S.η ω) (ball z r)).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε) →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (thickening (r / 2) (fillCells ε (S.η ω) Θ))),
          srwLaw (S.mult ε ω) a {x | ∀ n : ℕ,
            (n : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ)) \ Θ) x →
            x n ∈ A} ≤ ENNReal.ofReal (1 - s₂)}

/-- **Lemma 6.9** (lemma:chance-of-being-absorbed, line 2626). There are deterministic `ω₀ = ω(γ) > 0` and `s₃ > 0`
such that for each `s₀ ∈ (0, 1)` there are `s₄, s₅ ∈ (0, 1)` and a random `σ(h)`-measurable `𝛅 > 0` such that with
probability tending to `1` as `ε → 0`, for `r ∈ [10 ε^{ω₀}, 𝛅]` and all `Θ ⊆ V^ε` with `Θ̄ ⋐ B_{ρ/2}` and
`B_{s₀} ⊆ Θ̄`: for each `k ≤ s₅ r^{2β⁻} ε⁻¹` and `a₁, …, a_k ∈ cl(Θ)`,
`P[|A(Θ; a₁, …, a_k → V^ε(Θ̄ + B_r)) \ Θ| ≤ s₄ k | h, η] ≤ exp(-s₃ k)`. -/
def ChanceOfBeingAbsorbedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm →
  ∃ ω₀ s₃ : ℝ, 0 < ω₀ ∧ 0 < s₃ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₄ s₅ : ℝ, 0 < s₄ ∧ s₄ < 1 ∧ 0 < s₅ ∧ s₅ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ (k : ℕ) (a : Fin k → ℤ), (k : ℝ) ≤ s₅ * r ^ (2 * βm) / ε → (∀ i, a i ∈ vClosure (S.mult ε ω) Θ) →
        walkersLaw (S.mult ε ω) a {xs |
          ((idlaAggregate Θ (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) (List.ofFn xs) \
            Θ).ncard : ℝ) ≤ s₄ * k} ≤ ENNReal.ofReal (Real.exp (-s₃ * k))}

/-- **Lemma 6.10** (lemma:iterative-bound, line 2679). There are a deterministic exponent `β = β(ρ, γ) > 0` and a
constant `C = C(ρ, γ) > 0` such that for each `s₀ ∈ (0, 1)` there is a `σ(h)`-measurable `𝛅₀` such that with
probability tending to `1` as `ε → 0`, for each `Θ` with `Θ̄ ⋐ B_{ρ/2}` and `B_{s₀} ⊆ Θ̄` and each `δ₀ < 𝛅₀`: the IDLA
cluster started with `Θ` occupied and `j ≤ ⌈δ₀ ε⁻¹⌉` walkers at sites `a₁, …, a_j ∈ cl(Θ)` satisfies
`A(Θ; a₁, …, a_j) ⊆ V^ε(B⁺_{C δ₀^β}(Θ̄)) ⊆ V^ε(B_ρ)`.
The cluster is random given `(h, η)`; "with probability tending to `1`" is read for the annealed probability, uniformly
over `Θ`, `δ₀`, `j` and the starting sites: the `P`-integral of the supremum over these of the conditional
probability that the inclusion fails tends to `0`. The printed `B_{s₀} ⊂ Θ` is read as `B_{s₀} ⊆ Θ̄`. -/
def IterativeBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    Tendsto (fun ε => ∫⁻ ω, ⨆ (Θ : Set ℤ) (_ : closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2))
        (_ : ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ) (δ₀ : ℝ) (_ : 0 < δ₀) (_ : δ₀ < dd ω) (j : ℕ)
        (_ : j ≤ ⌈δ₀ / ε⌉₊) (a : Fin j → ℤ) (_ : ∀ i, a i ∈ vClosure (S.mult ε ω) Θ),
          walkersLaw (S.mult ε ω) a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
            cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ∧
            cellVertices ε (S.η ω) (outerNbhd (C * δ₀ ^ β) (fillCells ε (S.η ω) Θ)) ⊆
              cellVertices ε (S.η ω) (ball 0 ρ))} ∂S.P)
      (𝓝[>] 0) (𝓝 0)

end MatedCRT
