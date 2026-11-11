import MatedCRT.Draft.Section6

/-!
# Lemma 6.9 (lemma:chance-of-being-absorbed, line 2626): carving of the proof (lines 2637-2666)

The proof releases the walkers one at a time from `cl(Θ)`, with the current aggregate `S_{k'-1}` occupied, and applies
Lemma 6.7 with `S := S_{k'-1}` to the `k'`-th walker: given the first `k' - 1` walkers, the `k'`-th walker is absorbed
in `V^ε(Θ̄ + B_r)` with conditional probability at least `s₂`. The number of absorbed walkers therefore dominates a
binomial random variable with parameters `k` and `s₂`, which gives the exponential bound. The walkers are independent
(`walkersLaw` is a product measure), so no Markov property of the walk is needed at this point.

* `AbsorptionChernoffStep`: the Chernoff-type iteration, deterministic given the map (the multigraph `m`), with the
  conclusion of Lemma 6.7 as hypothesis. Proved in MatedCRT/Proofs/Sec6/ChanceOfBeingAbsorbed/Chernoff.lean with
  `s₃ = s₄ = s₂/4`.
* `chanceOfBeingAbsorbedLocalRate_of_steps`: Lemma 6.7 + `AbsorptionChernoffStep` give Lemma 6.9 with the rate `s₃`
  chosen after `s₀` (`ChanceOfBeingAbsorbedLocalRateStmt`).

**Order of quantifiers.** The printed statement (line 2627) and `ChanceOfBeingAbsorbedStmt` choose
`s₃` before `s₀`, but the printed proof takes `s₃ = c`, the rate of the negative binomial concentration bound
(eq:number-of-walkers-nb-bound, line 2657) for success probability `s₂`, and `s₂ = s₂(s₀)` comes from Lemma 6.7.
Lemma 6.7 gives no lower bound on the absorption probability uniform in `s₀`, and for `k = 1` the conclusion of
Lemma 6.9 reads `P[walker not absorbed] ≤ e^{-s₃}`, which forces `s₃ ≤ -log(1 - s₂(s₀))`. Hence the proof supports
the statement with `s₃` chosen after `s₀`, which is `ChanceOfBeingAbsorbedLocalRateStmt`. Its only use, in the proof
of Lemma 6.10 (lines 2692, 2753), fixes `s₀` first, so this reading suffices there.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Lemma 6.9** with the rate `s₃` chosen after `s₀`; otherwise identical to
`ChanceOfBeingAbsorbedStmt`. -/
def ChanceOfBeingAbsorbedLocalRateStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ βm : ℝ, (2 + γ) ^ 2 / 2 < βm →
  ∃ ω₀ : ℝ, 0 < ω₀ ∧
  ∀ s₀ : ℝ, 0 < s₀ → s₀ < 1 → ∃ s₃ s₄ s₅ : ℝ, 0 < s₃ ∧ 0 < s₄ ∧ s₄ < 1 ∧ 0 < s₅ ∧ s₅ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ dd : Ω → ℝ, Measurable[S.fieldSigma] dd ∧ (∀ ω, 0 < dd ω) ∧
    ProbTendsToOne S.P fun ε => {ω | ∀ r : ℝ, 10 * ε ^ ω₀ ≤ r → r ≤ dd ω → ∀ Θ : Set ℤ,
      closure (fillCells ε (S.η ω) Θ) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) Θ →
      ∀ (k : ℕ) (a : Fin k → ℤ), (k : ℝ) ≤ s₅ * r ^ (2 * βm) / ε → (∀ i, a i ∈ vClosure (S.mult ε ω) Θ) →
        walkersLaw (S.mult ε ω) a {xs |
          ((idlaAggregate Θ (cellVertices ε (S.η ω) (thickening r (fillCells ε (S.η ω) Θ))) (List.ofFn xs) \
            Θ).ncard : ℝ) ≤ s₄ * k} ≤ ENNReal.ofReal (Real.exp (-s₃ * k))}

/-- The printed order of quantifiers implies the local-rate reading (a rate chosen before `s₀` serves for each
`s₀`). -/
theorem ChanceOfBeingAbsorbedStmt.localRate {𝒮 : SpaceFillingSLEModel} (h : ChanceOfBeingAbsorbedStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβ
  obtain ⟨ω₀, s₃, hω₀, hs₃, h'⟩ := h γ hγ hγ2 ρ hρ hρ1 βm hβ
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₄, s₅, h4, h4', h5, h5', h''⟩ := h' s₀ hs₀ hs₀1
  exact ⟨s₃, s₄, s₅, hs₃, h4, h4', h5, h5', h''⟩

/-- Step (the Chernoff-type iteration of the proof of Lemma 6.9, lines 2643-2665; deterministic given the map `m`).
Let `U ⊆ ℤ` (in the application `U = V^ε(Θ̄ + B_r)`). Suppose that a walker started anywhere in `cl(Θ)` visits
`U \ (S' ∪ Θ)` before exiting `U` with probability at least `s₂`, for every `S' ⊆ U` with `|S' \ Θ| < L` (the
conclusion of Lemma 6.7, with `L = s₁ r^{2β⁻} ε⁻¹`). Then for `k ≤ L` walkers started in `cl(Θ)`, the aggregate
`A(Θ; a₁, …, a_k → U)` has more than `s₂ k / 4` sites outside `Θ` except with probability at most `e^{-s₂ k / 4}`. -/
def AbsorptionChernoffStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (Θ U : Set ℤ) (s₂ L : ℝ), 0 < s₂ → s₂ < 1 →
    (∀ a ∈ vClosure m Θ, ∀ S' ⊆ U, ((S' \ Θ).ncard : ℝ) < L →
      ENNReal.ofReal s₂ ≤ srwLaw m a {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime U x ∧ x n ∈ U \ (S' ∪ Θ)}) →
    ∀ (k : ℕ) (a : Fin k → ℤ), (k : ℝ) ≤ L → (∀ i, a i ∈ vClosure m Θ) →
      walkersLaw m a {xs | ((idlaAggregate Θ U (List.ofFn xs) \ Θ).ncard : ℝ) ≤ s₂ / 4 * k} ≤
        ENNReal.ofReal (Real.exp (-(s₂ / 4) * k))

/-- Enlarging the events preserves "with probability tending to `1`". -/
theorem ProbTendsToOne.mono' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (h : ProbTendsToOne P E) (hEF : ∀ ε, E ε ⊆ F ε) : ProbTendsToOne P F :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    (fun ε => measure_mono (compl_subset_compl.2 (hEF ε)))

/-- **Lemma 6.9** (local-rate reading) from Lemma 6.7 and the Chernoff-type iteration, with
`s₃ = s₄ = s₂/4` and `s₅ = s₁`, and the same `ω₀` and `𝛅` as in Lemma 6.7. -/
theorem chanceOfBeingAbsorbedLocalRate_of_steps (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮)
    (hC : AbsorptionChernoffStep) : ChanceOfBeingAbsorbedLocalRateStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 βm hβ
  obtain ⟨ω₀, hω₀, h⟩ := h67 γ hγ hγ2 ρ hρ hρ1 βm hβ
  refine ⟨ω₀, hω₀, fun s₀ hs₀ hs₀1 => ?_⟩
  obtain ⟨s₁, s₂, hs₁, hs₁1, hs₂, hs₂1, h'⟩ := h s₀ hs₀ hs₀1
  refine ⟨s₂ / 4, s₂ / 4, s₁, by positivity, by positivity, by linarith, hs₁, hs₁1, fun Ω _ S hS => ?_⟩
  obtain ⟨dd, hdd, hddpos, hP⟩ := h' Ω S hS
  refine ⟨dd, hdd, hddpos, hP.mono' fun ε ω hω => ?_⟩
  simp only [mem_ofPred_eq] at hω ⊢
  intro r hr1 hr2 Θ hΘ1 hΘ2 k a hk ha
  exact hC (S.mult ε ω) Θ _ s₂ (s₁ * r ^ (2 * βm) / ε) hs₂ hs₂1 (hω r hr1 hr2 Θ hΘ1 hΘ2) k a hk ha

end MatedCRT
