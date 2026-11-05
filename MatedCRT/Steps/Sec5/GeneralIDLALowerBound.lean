import MatedCRT.Draft.Section5
import MatedCRT.Proofs.IDLA.Counts
import MatedCRT.Proofs.IDLA.JointLowerBound

/-!
# Lemma 5.2: carving into steps (proof at lines 2132-2229; Lawler-Bramson-Griffeath, LBG92 Section 3)

Fix a multigraph `m`, a vertex set `O` (the paper's `O₂^ε`), a site `a` (the paper's `b`, line 2162) and `n = ⌊K_ε⌋`
walkers from the origin. Write `p_z = P^z[τ_a < T_O]` (`hitBeforeExitProb`) and `μ = ∑_{z ∈ O} p_z`. Then
`G_O(z, a) = p_z G_O(a, a)` (eq:markov-chain-renewal, LL10 Lemma 4.6.1), so that `E M = n p_0` and `E L̂ = μ`
(eq:expected-value-of-m, eq:expected-value-of-l), and the two conditions of the lemma read `n p_0 ≥ (1 + 𝔰) μ`,
`μ ≥ ε^{-q}`.

Quenched steps (deterministic multigraph `m`, law `walkerSequenceLaw m 0` of the walkers):
* `GreenHittingStep`: `G_O(z, a) = p_z G_O(a, a)` (line 2176);
* `MissedSiteVisitStep`: pathwise, if `a` is not in the cluster then `M ≤ L` (eq:upper-bound, line 2170), where
  `M = visitCount` counts the walkers hitting `a` before exiting `O` and `L = lateVisitCount` those which moreover
  have left the current cluster before hitting `a` (lines 2163-2168);
* `VisitCountLowerTailStep`: Chernoff bound for the lower tail of the binomial variable `M`;
* `LateVisitUpperTailStep`: `P[L ≥ k] ≤ exp(-λk + (e^λ - 1) μ)`, from `E e^{λL} ≤ exp((e^λ - 1) μ)` (the strong
  Markov reduction eq:strong-markov-reduction, line 2187, in exponential-moment form: each walker counted in `L`
  leaves the cluster at a new site `z ∈ O`, after which it is a fresh walk from `z`);
* `QuenchedSiteBoundStep`: `P[a ∉ A(n)] ≤ 2 exp(-c μ)` with `c = c(𝔰) > 0` (eq:exponential-bound, line 2148,
  from the three previous steps and eq:concentration-inequality, LBG92 Lemma 3.3).

Annealed steps:
* `CellCountStep`: `|V^ε(B_ρ)| ≤ ε^{-2}` with probability tending to `1` (line 2155: the cells have `μ_h`-mass `ε`
  and intersect only along their boundaries);
* `EnvSigmaMeasurableStep`: the environment `(h, η)` consists of random variables (`σ(h, η)` is contained in the
  σ-algebra of `Ω`), so that `P[𝔰 < δ] → 0` as `δ → 0` for the `σ(h, η)`-measurable `𝔰 > 0`.

`generalIDLALowerBound_of_steps` proves Lemma 5.2 from `GreenHittingStep`, `QuenchedSiteBoundStep`, `CellCountStep`
and `EnvSigmaMeasurableStep` (union bound over `a ∈ O₁^ε` and integration over the environment).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-! ## Steps

The quenched objects `hitBeforeExitProb`, `visitCount` (`M`) and `lateVisitCount` (`L`) are defined in
MatedCRT/Proofs/IDLA/Counts.lean. -/

/-- Step (eq:markov-chain-renewal, line 2176; LL10 Lemma 4.6.1, by the strong Markov property at `τ_a`):
`G_O(z, a) = P^z[τ_a < T_O] G_O(a, a)`. -/
def GreenHittingStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a z : ℤ),
    greenFn m O z a = hitBeforeExitProb m O a z * greenFn m O a a

/-- Step (eq:upper-bound, line 2170): if `a` does not belong to the cluster after `n` walkers then every walker which
hits `a` before exiting `O` does so after leaving the cluster of the previous walkers, so `M ≤ L` (and `M = L`). For
the IDLA cluster and for the cluster with walkers stopped upon exiting `O`. -/
def MissedSiteVisitStep : Prop :=
  ∀ (O : Set ℤ) (a : ℤ) (xs : ℕ → ℕ → ℤ) (n : ℕ),
    (a ∉ idlaCluster xs n → visitCount O a xs n ≤ lateVisitCount (idlaCluster xs) O a xs n) ∧
    (a ∉ stoppedIDLACluster O xs n →
      visitCount O a xs n ≤ lateVisitCount (stoppedIDLACluster O xs) O a xs n)

/-- Step (Chernoff bound for `M`, a sum of `n` independent indicators of mean `p_0`, eq:expected-value-of-m and
eq:concentration-inequality): `P[M ≤ k] ≤ exp(λ k - n p_0 (1 - e^{-λ}))` for `λ ≥ 0`. -/
def VisitCountLowerTailStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (n : ℕ) (l k : ℝ), 0 ≤ l →
    walkerSequenceLaw m 0 {xs | (visitCount O a xs n : ℝ) ≤ k} ≤
      ENNReal.ofReal (Real.exp (l * k - n * hitBeforeExitProb m O a 0 * (1 - Real.exp (-l))))

/-- Step (eq:strong-markov-reduction and eq:expected-value-of-l, lines 2187-2194, with the Chernoff bound for the
upper tail): for `λ ≥ 0`, `P[L ≥ k] ≤ exp(-λ k + (e^λ - 1) μ)`, `μ = ∑_{z ∈ O} P^z[τ_a < T_O]`, for the IDLA cluster
and for the cluster with walkers stopped upon exiting `O`. (Proof: `E[e^{λ L}] ≤ exp((e^λ - 1) μ)` by induction on
the walkers, each walker counted in `L` leaving the current cluster at a new site `z ∈ O`, after which it is a fresh
walk from `z` by the strong Markov property; then Markov's inequality.) -/
def LateVisitUpperTailStep : Prop :=
  ∀ (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (n : ℕ) (l k : ℝ), 0 ≤ l →
    Summable (fun z : O => hitBeforeExitProb m O a z) →
    walkerSequenceLaw m 0 {xs | k ≤ (lateVisitCount (idlaCluster xs) O a xs n : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z)) ∧
      walkerSequenceLaw m 0 {xs | k ≤ (lateVisitCount (stoppedIDLACluster O xs) O a xs n : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(l * k) + (Real.exp l - 1) * ∑' z : O, hitBeforeExitProb m O a z))

/-- Step (eq:exponential-bound, line 2148, for one site; from eq:upper-bound with `k = (1 + 𝔰/2) μ`, the Chernoff
bounds for `M` and `L`, eq:concentration-inequality): for each `𝔰 > 0` there is `c > 0` such that, on any
multigraph, if `n p_0 ≥ (1 + 𝔰) μ` with `μ = ∑_{z ∈ O} p_z` then `P[a ∉ A(n)] ≤ 2 e^{-c μ}`, for the IDLA cluster
and for the cluster with walkers stopped upon exiting `O`. -/
def QuenchedSiteBoundStep : Prop :=
  ∀ s : ℝ, 0 < s → ∃ c : ℝ, 0 < c ∧ ∀ (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (n : ℕ),
    Summable (fun z : O => hitBeforeExitProb m O a z) →
    (1 + s) * ∑' z : O, hitBeforeExitProb m O a z ≤ n * hitBeforeExitProb m O a 0 →
    walkerSequenceLaw m 0 {xs | a ∉ idlaCluster xs n} ≤
        ENNReal.ofReal (2 * Real.exp (-(c * ∑' z : O, hitBeforeExitProb m O a z))) ∧
      walkerSequenceLaw m 0 {xs | a ∉ stoppedIDLACluster O xs n} ≤
        ENNReal.ofReal (2 * Real.exp (-(c * ∑' z : O, hitBeforeExitProb m O a z)))

/-- Step (line 2155): `V^ε(B_ρ)` is finite with `|V^ε(B_ρ)| ≤ ε^{-2}`, with probability tending to `1` as `ε → 0`
(the paper: `|V^ε(B_ρ)| ≤ C ε^{-1}` for a random `C`, since the cells have `μ_h`-mass `ε` and intersect only along
their boundaries; from Lemma 2.8 and the local finiteness of `μ_h`, Fact 2.2). -/
def CellCountStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ProbTendsToOne S.P fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ρ)).Finite ∧
      ((cellVertices ε (S.η ω) (ball 0 ρ)).ncard : ℝ) ≤ ε ^ (-2 : ℝ)}

/-- Step (modeling): the field and the curve are random variables, i.e. `σ(h, η)` is contained in the σ-algebra of
`Ω`. Used for `P[𝔰 < δ] → 0` as `δ → 0` for the `σ(h, η)`-measurable `𝔰 > 0` of Lemma 5.2. -/
def EnvSigmaMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    S.envSigma ≤ mΩ

/-! ## Assembly -/

/-- If `f ε ≤ 1` and, for each `δ₀ > 0`, eventually `f ε ≤ β ε → 0` on `E ε ∩ {𝔰 ≥ δ₀}`, where `P[(E ε)ᶜ] → 0` and
`𝔰 > 0` is measurable, then the outer integral `∫* f ε dP → 0`. -/
theorem tendsto_outerLIntegral_of_eventually_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ ε ω, f ε ω ≤ 1) (s : Ω → ℝ)
    (hs : Measurable s) (hspos : ∀ ω, 0 < s ω) (E : ℝ → Set Ω)
    (hE : Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0))
    (hb : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ β : ℝ → ℝ≥0∞, Tendsto β (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝[>] 0, ∀ ω ∈ E ε, δ₀ ≤ s ω → f ε ω ≤ β ε) :
    Tendsto (fun ε => outerLIntegral P (f ε)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  set A : ℕ → Set Ω := fun n => {ω | s ω < 1 / ((n : ℝ) + 1)} with hA
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
    have hanti : Antitone A := by
      intro i j hij ω hω
      simp only [hA, mem_ofPred_eq] at hω ⊢
      refine hω.trans_le (one_div_le_one_div_of_le (by positivity) ?_)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (measurableSet_lt hs measurable_const).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
    have hempty : (⋂ n, A n) = ∅ := by
      ext ω
      simp only [hA, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hspos ω)
      exact ⟨n, hn.le⟩
    rw [hempty, measure_empty] at h
    exact h
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hlim (e / 2) he2).exists
  have hδ₀ : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨β, hβ, hev⟩ := hb _ hδ₀
  have hsum : Tendsto (fun ε => P (E ε)ᶜ + β ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using hE.add hβ
  filter_upwards [hev, ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2] with ε hε hε2
  set T := toMeasurable P ((E ε)ᶜ ∪ A N) with hT
  have hpt : ∀ ω, f ε ω ≤ T.indicator 1 ω + β ε := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω]
      exact (hf ε ω).trans le_self_add
    · have hω' : ω ∉ (E ε)ᶜ ∪ A N := fun h => hω (subset_toMeasurable _ _ h)
      simp only [hA, mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq, not_lt] at hω'
      exact (hε ω hω'.1 hω'.2).trans le_add_self
  have hgm : Measurable fun ω => T.indicator 1 ω + β ε :=
    (measurable_one.indicator (measurableSet_toMeasurable _ _)).add measurable_const
  calc outerLIntegral P (f ε) ≤ ∫⁻ ω, (T.indicator 1 ω + β ε) ∂P :=
        iInf_le_of_le (fun ω => T.indicator 1 ω + β ε) (iInf_le_of_le hgm (iInf_le_of_le hpt le_rfl))
    _ = P T + β ε := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_indicator_one (measurableSet_toMeasurable _ _), lintegral_const, measure_univ, mul_one]
    _ ≤ (P (E ε)ᶜ + P (A N)) + β ε := by
        rw [hT, measure_toMeasurable]
        exact add_le_add (measure_union_le _ _) le_rfl
    _ = P (A N) + (P (E ε)ᶜ + β ε) := by rw [add_comm (P (E ε)ᶜ), add_assoc]
    _ ≤ e / 2 + e / 2 := add_le_add hN hε2
    _ = e := ENNReal.add_halves e

/-- The bound for one site `a` on a fixed multigraph from the two conditions of Lemma 5.2 (eq:mean-value-ineq,
eq:L-lower-bound, rewritten by `GreenHittingStep` as `K p_0 ≥ (1 + 𝔰) μ` and `μ ≥ x`). -/
theorem siteBound_of_conditions (hG : GreenHittingStep) {δ₀ c : ℝ} (hδ₀ : 0 < δ₀) (hc : 0 < c)
    (hcQ : ∀ (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (n : ℕ),
      Summable (fun z : O => hitBeforeExitProb m O a z) →
      (1 + δ₀ / 2) * ∑' z : O, hitBeforeExitProb m O a z ≤ n * hitBeforeExitProb m O a 0 →
      walkerSequenceLaw m 0 {xs | a ∉ idlaCluster xs n} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * ∑' z : O, hitBeforeExitProb m O a z))) ∧
        walkerSequenceLaw m 0 {xs | a ∉ stoppedIDLACluster O xs n} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * ∑' z : O, hitBeforeExitProb m O a z))))
    (m : ℤ → ℤ → ℕ) (O : Set ℤ) (a : ℤ) (Kε sω x : ℝ) (hx : 0 < x) (hxδ : 2 / δ₀ ≤ x) (hs : δ₀ ≤ sω)
    (h1 : (1 + sω) * ∑' b : O, greenFn m O b a ≤ Kε * greenFn m O 0 a)
    (h2 : x ≤ (∑' b : O, greenFn m O b a) / greenFn m O a a) :
    walkerSequenceLaw m 0 {xs | a ∉ idlaCluster xs ⌊Kε⌋₊} ≤ ENNReal.ofReal (2 * Real.exp (-(c * x))) ∧
      walkerSequenceLaw m 0 {xs | a ∉ stoppedIDLACluster O xs ⌊Kε⌋₊} ≤
        ENNReal.ofReal (2 * Real.exp (-(c * x))) := by
  set g : ℝ := greenFn m O a a with hg
  set μ : ℝ := ∑' z : O, hitBeforeExitProb m O a z with hμ
  have hsum : ∑' b : O, greenFn m O b a = μ * g := by
    rw [hμ, ← tsum_mul_right]
    exact tsum_congr fun b => hG m O a b
  rw [hsum] at h1 h2
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at h2
      linarith
  rw [mul_div_assoc, div_self hgpos.ne', mul_one] at h2
  have hp0 : 0 ≤ hitBeforeExitProb m O a 0 := ENNReal.toReal_nonneg
  have hp1 : hitBeforeExitProb m O a 0 ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have h1' : ((1 + sω) * μ) * g ≤ (Kε * hitBeforeExitProb m O a 0) * g := by
    have h0 := hG m O a 0
    calc ((1 + sω) * μ) * g = (1 + sω) * (μ * g) := by ring
      _ ≤ Kε * greenFn m O 0 a := h1
      _ = (Kε * hitBeforeExitProb m O a 0) * g := by rw [h0]; ring
  have h1'' := le_of_mul_le_mul_right h1' hgpos
  have hfl := Nat.lt_floor_add_one Kε
  have hμpos : 0 < μ := lt_of_lt_of_le hx h2
  have hkey : (1 + δ₀ / 2) * μ ≤ (⌊Kε⌋₊ : ℝ) * hitBeforeExitProb m O a 0 := by
    have e1 : Kε * hitBeforeExitProb m O a 0 ≤ ((⌊Kε⌋₊ : ℝ) + 1) * hitBeforeExitProb m O a 0 :=
      mul_le_mul_of_nonneg_right hfl.le hp0
    have e2 : (1 + δ₀) * μ ≤ (1 + sω) * μ := mul_le_mul_of_nonneg_right (by linarith) hμpos.le
    have e3 : 2 ≤ μ * δ₀ := (div_le_iff₀ hδ₀).1 (hxδ.trans h2)
    nlinarith
  have hsumm : Summable (fun z : O => hitBeforeExitProb m O a z) := by
    by_contra hns
    have h0 : μ = 0 := tsum_eq_zero_of_not_summable hns
    linarith
  obtain ⟨hA, hB⟩ := hcQ m O a ⌊Kε⌋₊ hsumm hkey
  have hmono : ENNReal.ofReal (2 * Real.exp (-(c * μ))) ≤ ENNReal.ofReal (2 * Real.exp (-(c * x))) := by
    apply ENNReal.ofReal_le_ofReal
    have h3 : c * x ≤ c * μ := mul_le_mul_of_nonneg_left h2 hc.le
    have h4 := Real.exp_le_exp.2 (neg_le_neg h3)
    linarith
  exact ⟨hA.trans hmono, hB.trans hmono⟩

/-- `ε^{-q} → ∞` as `ε → 0⁺`. -/
theorem tendsto_rpow_neg_nhdsGT_zero_atTop {q : ℝ} (hq : 0 < q) :
    Tendsto (fun ε : ℝ => ε ^ (-q)) (𝓝[>] 0) atTop := by
  refine ((tendsto_rpow_atTop hq).comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp [Function.comp, Real.inv_rpow hε.le, Real.rpow_neg hε.le]

/-- `ε^{-2} · 2 e^{-c ε^{-q}} → 0` as `ε → 0⁺`. -/
theorem tendsto_card_mul_exp_bound {q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))) (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / q) c hc).comp
    (tendsto_rpow_neg_nhdsGT_zero_atTop hq)).const_mul 2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp, neg_mul]
  rw [← Real.rpow_mul hε.le, show -q * (2 / q) = (-2 : ℝ) by field_simp]
  ring

/-- Sectionwise form of Lemma 5.2, used to assemble the joint-law statement. -/
def GeneralIDLALowerBoundSectionwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (O₁ O₂ : ℝ → Ω → Set ℤ) (K : ℝ → ℝ) (q : ℝ) (s : Ω → ℝ),
    (∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₁ ε ω}) → (∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₂ ε ω}) →
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) ∧ (0 : ℤ) ∈ O₁ ε ω ∧
      IsVConnected (S.mult ε ω) (O₁ ε ω) ∧ IsVConnected (S.mult ε ω) (O₂ ε ω)) →
    (∀ ε, 0 < K ε) → 0 < q → Measurable[S.envSigma] s → (∀ ω, 0 < s ω) →
    ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) / greenFn (S.mult ε ω) (O₂ ε ω) a a}) →
    Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ idlaCluster p.2 ⌊K ε⌋₊}) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ stoppedIDLACluster (O₂ ε p.1) p.2 ⌊K ε⌋₊})
      (𝓝[>] 0) (𝓝 0)

/-- **Lemma 5.2** from its steps: the quenched one-site bound, the Green function identity, the count of the cells
meeting `B_ρ`, and the measurability of the environment. -/
theorem generalIDLALowerBoundSectionwise_of_steps (𝒮 : SpaceFillingSLEModel) (hG : GreenHittingStep)
    (hQ : QuenchedSiteBoundStep) (hC : CellCountStep 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) :
    GeneralIDLALowerBoundSectionwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS O₁ O₂ K q s _ _ hO _ hq hs hspos hgood
  have := hS.isProbabilityMeasure
  have hsm : Measurable s := hs.mono (hM γ hγ hγ2 Ω S hS) le_rfl
  -- the events of the proof
  set A : ℝ → Set Ω := fun ε =>
    {ω | O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ)} with hA
  set B : ℝ → Set Ω := fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) /
        greenFn (S.mult ε ω) (O₂ ε ω) a a} with hB
  set C : ℝ → Set Ω := fun ε => {ω | (cellVertices ε (S.η ω) (ball 0 ρ)).Finite ∧
      ((cellVertices ε (S.η ω) (ball 0 ρ)).ncard : ℝ) ≤ ε ^ (-2 : ℝ)} with hCdef
  have hBt : Tendsto (fun ε => S.P (B ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hgood
  have hCt : Tendsto (fun ε => S.P (C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := hC γ hγ hγ2 ρ hρ hρ1 Ω S hS
  have hE : Tendsto (fun ε => S.P (A ε ∩ B ε ∩ C ε)ᶜ) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hBt.add hCt) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hnull : S.P (A ε)ᶜ = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 (hO ε hε))
      intro ω hω
      simp only [hA, mem_compl_iff, mem_ofPred_eq] at hω
      simp only [mem_ofPred_eq]
      exact fun h => hω ⟨h.1, h.2.1⟩
    calc S.P (A ε ∩ B ε ∩ C ε)ᶜ = S.P ((A ε)ᶜ ∪ (B ε)ᶜ ∪ (C ε)ᶜ) := by
          rw [compl_inter, compl_inter]
      _ ≤ S.P (A ε)ᶜ + S.P (B ε)ᶜ + S.P (C ε)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = S.P (B ε)ᶜ + S.P (C ε)ᶜ := by rw [hnull, zero_add]
  -- the assembly, for a cluster `clus ε ω xs` satisfying the one-site bound
  have main : ∀ clus : ℝ → Ω → (ℕ → ℕ → ℤ) → Set ℤ,
      (∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
        δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q))))) →
      Tendsto (fun ε => S.idlaSectionProb ε {p | ¬ O₁ ε p.1 ⊆ clus ε p.1 p.2}) (𝓝[>] 0) (𝓝 0) := by
    intro clus hsite
    refine tendsto_outerLIntegral_of_eventually_le S.P
      (fun ε ω => walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs})
      (fun ε ω => prob_le_one) s hsm hspos (fun ε => A ε ∩ B ε ∩ C ε) hE ?_
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcs⟩ := hsite δ₀ hδ₀
    refine ⟨fun ε => ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))), ?_, ?_⟩
    · simpa using ENNReal.tendsto_ofReal (tendsto_card_mul_exp_bound hq hc)
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_rpow_neg_nhdsGT_zero_atTop hq).eventually_ge_atTop (2 / δ₀)] with ε (hε : 0 < ε) hεq
    rintro ω ⟨⟨⟨hsub1, hsub2⟩, hωB⟩, hCfin, hCcard⟩ hsω
    have hfin : (O₁ ε ω).Finite := hCfin.subset (hsub1.trans hsub2)
    have hsite' := hcs ε hε hεq ω hωB hsω
    calc walkerSequenceLaw (S.mult ε ω) 0 {xs | ¬ O₁ ε ω ⊆ clus ε ω xs}
        ≤ walkerSequenceLaw (S.mult ε ω) 0 (⋃ a ∈ hfin.toFinset, {xs | a ∉ clus ε ω xs}) := by
          apply measure_mono
          intro xs hxs
          simp only [mem_ofPred_eq, not_subset] at hxs
          obtain ⟨a, ha, hna⟩ := hxs
          simp only [mem_iUnion]
          exact ⟨a, hfin.mem_toFinset.2 ha, hna⟩
      _ ≤ ∑ a ∈ hfin.toFinset, walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ clus ε ω xs} :=
          measure_biUnion_finset_le _ _
      _ ≤ hfin.toFinset.card • ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) :=
          Finset.sum_le_card_nsmul _ _ _ fun a ha => hsite' a (hfin.mem_toFinset.1 ha)
      _ ≤ ENNReal.ofReal (ε ^ (-2 : ℝ) * (2 * Real.exp (-(c * ε ^ (-q))))) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact (Nat.cast_le.2 (Set.ncard_le_ncard (hsub1.trans hsub2) hCfin)).trans hCcard
  -- the one-site bound from `QuenchedSiteBoundStep`
  have hsite : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → 2 / δ₀ ≤ ε ^ (-q) → ∀ ω ∈ B ε,
      δ₀ ≤ s ω → ∀ a ∈ O₁ ε ω,
        walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ idlaCluster xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) ∧
          walkerSequenceLaw (S.mult ε ω) 0 {xs | a ∉ stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊} ≤
            ENNReal.ofReal (2 * Real.exp (-(c * ε ^ (-q)))) := by
    intro δ₀ hδ₀
    obtain ⟨c, hc, hcQ⟩ := hQ (δ₀ / 2) (by positivity)
    refine ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => ?_⟩
    obtain ⟨h1, h2⟩ := hωB a ha
    exact siteBound_of_conditions hG hδ₀ hc hcQ (S.mult ε ω) (O₂ ε ω) a (K ε) (s ω) (ε ^ (-q))
      (Real.rpow_pos_of_pos hε _) hεq hsω h1 h2
  refine ⟨main (fun ε _ xs => idlaCluster xs ⌊K ε⌋₊) ?_,
    main (fun ε ω xs => stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊) ?_⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).1⟩
  · intro δ₀ hδ₀
    obtain ⟨c, hc, h⟩ := hsite δ₀ hδ₀
    exact ⟨c, hc, fun ε hε hεq ω hωB hsω a ha => (h ε hε hεq ω hωB hsω a ha).2⟩

/-- The sectionwise proof supplies the present statement of Lemma 5.2. -/
theorem generalIDLALowerBound_of_steps (𝒮 : SpaceFillingSLEModel) (hG : GreenHittingStep)
    (hQ : QuenchedSiteBoundStep) (hC : CellCountStep 𝒮) (hM : EnvSigmaMeasurableStep 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS O₁ O₂ K q s hm₁ hm₂ hO hK hq hs hspos hgood
  obtain ⟨hl, hs'⟩ := generalIDLALowerBoundSectionwise_of_steps 𝒮 hG hQ hC hM
    γ hγ hγ2 ρ hρ hρ1 Ω S hS O₁ O₂ K q s hm₁ hm₂ hO hK hq hs hspos hgood
  obtain ⟨hjl, hjs⟩ := hS.joint_generalIDLABounds_of_sectionwise O₁ O₂ K hm₁ hm₂ hl hs'
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hjl (fun _ => zero_le) ?_
    intro ε
    exact hS.idlaProb_le_jointMeasure ε _
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hjs (fun _ => zero_le) ?_
    intro ε
    exact hS.idlaProb_le_jointMeasure ε _

end MatedCRT
