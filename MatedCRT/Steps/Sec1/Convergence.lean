import MatedCRT.Draft.Section1
import MatedCRT.Draft.Section8
import MatedCRT.Proofs.Sec1.Scaling
import MatedCRT.Proofs.Sec8.Annealed
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence

/-!
# Theorems 1.4 and 1.6 from Proposition 8.1 by scale invariance (Section 8.1, lines 3284-3336)

The printed proof: for `b > 0` the rescaled field `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`, the rescaled curve
`η^b = R_b⁻¹ η(b ·)` and the rescaled family `R_b⁻¹ Λ_{b ·}` have the joint law of `(h, η, {Λ_t})` (Lemma 2.6, the scale
invariance of `η` and the independence of `η` and `h`, eq:scale-invariance-of-field-and-eta). Proposition 8.1 for the
rescaled objects, at time `t / b` and width `δ / R_b`, gives the approximation of `Λ_t` by the cluster on the event
`{t < b T^b}`, where `T^b = sup {s : R_b⁻¹ Λ_{bs} ⊆ B_{ρ/3}} =d T`; and `b T^b → ∞` in probability as `b → ∞`
(eq:btb-converge-to-inf).

## Formalization

Proposition 8.1 is stated for every valid environment, so instead of an equality of joint laws we use a valid
environment `S'` on the same probability space whose curve, boundary-length pair and LQG measure are the rescaled ones
(`ConeEnvironmentScalingStep`). Then pathwise:
* the map of `S'` with cell size `ε / b` is the map of `S` with cell size `ε` (`Sec1.bmEdgeCount_rescale`), so the
  IDLA walkers and the sandpile are the same;
* the cells of `S'` with cell size `ε / b` are `R_b⁻¹` times the cells of `S` with cell size `ε`
  (`Sec1.fillCells_rescale`), and the approximation event with width `δ'` for `S'` implies the one with width
  `R_b δ' ≤ δ` for `S` (`Sec1.approximatesWithin_of_rescaled`).
The random width `δ / R_b` of the printed proof is replaced by a deterministic `δ' = min(δ, 1/4) / M` with
`P[R_b > M]` small (`R_b` is a random variable, `ConeScaleRadiusStep`). The annealed probabilities are compared with
`Sec8.annealedOuterProb_le_of_forall_not_mem`.

## Steps (hypotheses of `convergenceOfIDLA_of_steps`, `convergenceOfDivSandpile_of_steps`)

* `ConeEnvironmentScalingStep`: the rescaled environment is valid (DMS14 Prop 4.13(i) eq:quantum-cone-scaling for the
  field, eq:eta-scale-invariant and the independence of `η` and `h` for the curve, Fact 2.2 (coordinate change, Weyl
  scaling) for `μ_{h^b}`, Brownian scaling of the boundary-length pair in the mating-of-trees coupling, LBM scaling for
  the clock). This is the content of eq:scale-invariance-of-field-and-eta in the form Proposition 8.1 can use.
* `HarmonicBallFamilyScalingStep`: deterministic covariance of the conditions (a)-(c) of Theorem 2.3 under
  `μ ↦ b⁻¹ μ(R ·)`, `Λ_t ↦ R⁻¹ Λ_{bt}` (used implicitly in Lemma 2.6 and at line 3290).
* `ConeScaleRadiusStep`: `R_b` (eq:cone-scale-radius) is an a.e.-measurable, a.s. positive random variable.
* `ScaledClusterExitTimeStep`: eq:btb-converge-to-inf, `P[b T^b ≤ t] → 0` as `b → ∞`.

Lemma 2.6 (`ConeScaleInvarianceStmt`) is NOT a hypothesis: in its Lean form it is an equality of image measures
`P.map (circleProcess h, globalFamilyProcess Λ)`, and `Measure.map` of a map which is not a.e.-measurable is a junk
value which does not depend on the map, so the equality says nothing about non-measurable families.
Theorem 1.4 does not assume that `ω ↦ {Λ_t}` is measurable, and `{T ≤ s}` is not determined by countably many
coordinates of the indicator process, so `T^b =d T` cannot be read off from it. Its use (line 3292) enters through
`ScaledClusterExitTimeStep` (law of `T^b`) and `ConeEnvironmentScalingStep` + `HarmonicBallFamilyScalingStep`
(the joint law of eq:scale-invariance-of-field-and-eta).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The rescaled measure `A ↦ b⁻¹ μ(R A)`: the `γ`-LQG measure of `h(R ·) + Q log R - γ⁻¹ log b` when `μ = μ_h`
(Fact 2.2, coordinate change and Weyl scaling; line 578). -/
noncomputable def rescaledMeasure (μ : Measure ℂ) (R b : ℝ) : Measure ℂ :=
  (ENNReal.ofReal b)⁻¹ • μ.map fun x => (R : ℂ)⁻¹ * x

/-- **The rescaled environment is valid** (eq:scale-invariance-of-field-and-eta, lines 3286-3293): for `b > 0` there
is a valid environment on the same probability space whose curve is `η^b = R_b⁻¹ η(b ·)`, whose boundary-length pair
is `b^{-1/2} (L, R)(b ·)` and whose LQG measure is `A ↦ b⁻¹ μ_h(R_b A)`, the measure of
`h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`, with `R_b` the cone scale radius (eq:cone-scale-radius). Sources: DMS14
Proposition 4.13(i) (eq:quantum-cone-scaling) for `h^b`; eq:eta-scale-invariant (line 619) and the independence of `η`
and `h` for `η^b`; Fact 2.2 for `μ_{h^b}`; Brownian scaling of the mating-of-trees coupling for the pair. -/
def ConeEnvironmentScalingStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ b : ℝ, 0 < b → ∃ S' : MatedCRTEnv Ω, S'.IsValid 𝒮 γ ∧ S'.P = S.P ∧
    (∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
    (∀ᵐ ω ∂S.P, ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s)) ∧
    (∀ᵐ ω ∂S.P, S'.μ ω = rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b)

/-- **Scaling covariance of the harmonic balls of Theorem 2.3** (deterministic; used implicitly in Lemma 2.6 and at
line 3290): if `{Λ_t}` satisfies the conditions of Theorem 2.3 for `μ`, then `{R⁻¹ Λ_{bt}}` satisfies them for
`A ↦ b⁻¹ μ(R A)` (`R, b > 0`). -/
def HarmonicBallFamilyScalingStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (R b : ℝ), 0 < R → 0 < b → IsConeHarmonicBallFamily μ Λ →
    IsConeHarmonicBallFamily (rescaledMeasure μ R b) (rescaledFamily Λ R b)

/-- **The cone scale radius is a random variable** (eq:cone-scale-radius, line 454): for `b > 0`,
`R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` is a.e.-measurable and a.s. positive. -/
def ConeScaleRadiusStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ b : ℝ, 0 < b → AEMeasurable (fun ω => coneScaleRadius γ (hcirc ω) b) P ∧
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b

/-- **eq:btb-converge-to-inf** (line 3330): for `T^b = sup {s > 0 : R_b⁻¹ Λ_{bs} ⊆ B_{ρ/3}}`, `b T^b → ∞` in
probability as `b → ∞`: `P[b T^b ≤ t] → 0` for each `t > 0`. The printed justification is `T^b =d T` (Lemma 2.6) and
`T > 0` a.s. -/
def ScaledClusterExitTimeStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
    Tendsto (fun b => P {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t})
      atTop (𝓝 0)

namespace Sec1

/-- The IDLA walkers have a probability law (`walkerSequenceLaw` is an infinite product of probability measures). -/
theorem walkerSequenceLaw_univ_le_one (m : ℤ → ℤ → ℕ) (a : ℤ) : walkerSequenceLaw m a univ ≤ 1 := by
  unfold walkerSequenceLaw
  exact prob_le_one

/-- `ε ↦ ε / b` maps `0⁺` to `0⁺`. -/
theorem tendsto_div_const_nhdsGT {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ε / b) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun ε : ℝ => ε / b) (𝓝 0) (𝓝 (0 / b)) := (continuous_id.div_const b).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hb

/-- **The rescaled environment and the good event** (lines 3294-3330). Given `e > 0` there are `b > 0`, a valid
environment `S'` with harmonic ball family `Λ'`, a width `δ' ∈ (0, 1/2)` and a set `B` of environments with
`P(B) ≤ 2e/3` such that off `B`: the map of `S'` with cell size `ε / b` is the map of `S` with cell size `ε`,
`t / b < T'` (with `ρ = 1/2`), and the approximation of `Λ'_{t/b}` with width `δ'` by the cells of `S'` with cell
size `ε / b` of any vertex set implies the approximation of `Λ_t` with width `δ` by the cells of `S` with cell size
`ε` of the same set. -/
theorem exists_rescaled_environment (𝒮 : SpaceFillingSLEModel) (hEnv : ConeEnvironmentScalingStep 𝒮)
    (hHB : HarmonicBallFamilyScalingStep) (hR : ConeScaleRadiusStep) (hT : ScaledClusterExitTimeStep)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {Λ : Ω → ℝ → Set ℂ} (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ (b : ℝ) (S' : MatedCRTEnv Ω) (Λ' : Ω → ℝ → Set ℂ) (δ' : ℝ) (B : Set Ω),
      0 < b ∧ S'.IsValid 𝒮 γ ∧ S'.P = S.P ∧ (∀ᵐ ω ∂S'.P, IsConeHarmonicBallFamily (S'.μ ω) (Λ' ω)) ∧
      0 < δ' ∧ δ' < 1 / 2 ∧ S.P B ≤ e / 3 + e / 3 ∧
      ∀ ω, ω ∉ B → (∀ ε : ℝ, S'.mult (ε / b) ω = S.mult ε ω) ∧ t / b < clusterExitTime (Λ' ω) (1 / 2) ∧
        ∀ (ε : ℝ) (A : Set ℤ), ApproximatesWithin δ' (Λ' ω (t / b)) (fillCells (ε / b) (S'.η ω) A) →
          ApproximatesWithin δ (Λ ω t) (fillCells ε (S.η ω) A) := by
  have hfield : IsConeField γ S.P S.hC S.hcirc S.μ := ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have := hS.isProbabilityMeasure
  have he3 : 0 < e / 3 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  -- the scale `b ≥ 1` with `P[b T^b ≤ t] ≤ e/3`
  have hTb := hT γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num) Ω S.P S.hC S.hcirc S.μ hfield Λ hΛ t ht
  obtain ⟨b, hbT, hb1⟩ := ((ENNReal.tendsto_nhds_zero.1 hTb (e / 3) he3).and (eventually_ge_atTop 1)).exists
  have hb : 0 < b := by linarith
  obtain ⟨hRm, hRpos⟩ := hR γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hfield b hb
  -- the bound `M ≥ 1` with `P[R_b > M] ≤ e/3`
  obtain ⟨M, hMR, hM1⟩ := ((ENNReal.tendsto_nhds_zero.1 (tendsto_measure_lt_atTop hRm) (e / 3) he3).and
    (eventually_ge_atTop 1)).exists
  have hM : 0 < M := by linarith
  obtain ⟨S', hS', hP, hη, hbm, hμ⟩ := hEnv γ hγ hγ2 Ω S hS b hb
  have hδ₀ : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hN0 : S.P {ω | ¬ (0 < coneScaleRadius γ (S.hcirc ω) b ∧
      (∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
      ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))} = 0 :=
    ae_iff.1 (hRpos.and (hη.and hbm))
  refine ⟨b, S', fun ω => rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b, min δ (1 / 4) / M,
    {ω | ¬ (0 < coneScaleRadius γ (S.hcirc ω) b ∧
      (∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
      ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s))} ∪
      {ω | M < coneScaleRadius γ (S.hcirc ω) b} ∪
      {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b) (1 / 2) ≤ t},
    hb, hS', hP, ?_, div_pos hδ₀ hM, ?_, ?_, ?_⟩
  · rw [hP]
    filter_upwards [hRpos, hμ, hΛ] with ω hRω hμω hΛω
    rw [hμω]
    exact hHB (S.μ ω) (Λ ω) _ b hRω hb hΛω
  · calc min δ (1 / 4) / M ≤ min δ (1 / 4) := div_le_self hδ₀.le hM1
      _ ≤ 1 / 4 := min_le_right _ _
      _ < 1 / 2 := by norm_num
  · refine (measure_union_le _ _).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    rw [hN0, zero_add]
    exact add_le_add hMR hbT
  · intro ω hω
    have hωN : ¬ ¬ (0 < coneScaleRadius γ (S.hcirc ω) b ∧
        (∀ s : ℝ, S'.η ω s = ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) ∧
        ∀ s : ℝ, S'.bm ω s = (Real.sqrt b)⁻¹ • S.bm ω (b * s)) := fun h => hω (Or.inl (Or.inl h))
    have hωM : ¬ M < coneScaleRadius γ (S.hcirc ω) b := fun h => hω (Or.inl (Or.inr h))
    have hωT : ¬ b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b) (1 / 2) ≤ t :=
      fun h => hω (Or.inr h)
    obtain ⟨hRω, hηω, hbmω⟩ := not_not.1 hωN
    have hRω' : ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hRω.ne'
    refine ⟨fun ε => ?_, ?_, fun ε A hA => ?_⟩
    · funext j k
      exact bmEdgeCount_rescale (ε := ε) hb (inv_pos.2 (Real.sqrt_pos.2 hb)) (fun s => (S.bm ω s).1)
        (fun s => (S.bm ω s).2) (fun s => (S'.bm ω s).1) (fun s => (S'.bm ω s).2)
        (fun s => by simp only [hbmω s, Prod.smul_fst, smul_eq_mul])
        (fun s => by simp only [hbmω s, Prod.smul_snd, smul_eq_mul]) j k
    · show t / b < clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b) (1 / 2)
      rw [div_lt_iff₀ hb, mul_comm]
      exact not_le.1 hωT
    · have h1 : b * (t / b) = t := by field_simp
      have h3 : rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b (t / b) =
          {x | ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ) * x ∈ Λ ω t} := by
        simp only [rescaledFamily, h1]
      have hA' : ApproximatesWithin (min δ (1 / 4) / M)
          (rescaledFamily (Λ ω) (coneScaleRadius γ (S.hcirc ω) b) b (t / b)) (fillCells (ε / b) (S'.η ω) A) := hA
      rw [h3, fillCells_rescale hb hRω' (S.η ω) (S'.η ω) hηω A] at hA'
      refine approximatesWithin_of_rescaled hRω ?_ hA'
      calc coneScaleRadius γ (S.hcirc ω) b * (min δ (1 / 4) / M) ≤ M * (min δ (1 / 4) / M) :=
            mul_le_mul_of_nonneg_right (not_lt.1 hωM) (div_pos hδ₀ hM).le
        _ = min δ (1 / 4) := by field_simp
        _ ≤ δ := min_le_left _ _

end Sec1

/-- **Theorem 1.4** (theorem:convergence-of-IDLA, line 251) from Proposition 8.1 by scale invariance (Section 8.1,
lines 3284-3336). -/
theorem convergenceOfIDLA_of_steps (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hHB : HarmonicBallFamilyScalingStep) (hR : ConeScaleRadiusStep)
    (hT : ScaledClusterExitTimeStep) : ConvergenceOfIDLAStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ δ t hδ ht
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨b, S', Λ', δ', B, hb, hS', hP, hΛ', hδ', hδ'ρ, hB, hgood⟩ :=
    Sec1.exists_rescaled_environment 𝒮 hEnv hHB hR hT hγ hγ2 hS hΛ hδ ht he
  have he3 : 0 < e / 3 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  have h8 := (h81 γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num) Ω S' hS' Λ' hΛ' δ' (t / b) hδ' hδ'ρ
    (div_pos ht hb)).1
  have hlim := h8.comp (Sec1.tendsto_div_const_nhdsGT hb)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (e / 3) he3] with ε hgε
  refine le_trans ?_ ((add_le_add hgε hB).trans_eq ?_)
  · show S.idlaProb ε _ ≤ S'.idlaProb (ε / b) _ + S.P B
    unfold MatedCRTEnv.idlaProb
    rw [hP]
    refine Sec8.annealedOuterProb_le_of_forall_not_mem S.P _ _
      (fun ω => Sec1.walkerSequenceLaw_univ_le_one (S.mult ε ω) 0) _ _ B fun ω hω => ?_
    obtain ⟨hmult, hTω, happrox⟩ := hgood ω hω
    simp only [hmult ε]
    refine measure_mono fun xs hxs => And.intro hTω fun hA => hxs ?_
    have hidx : t / b / (ε / b) = t / ε := by field_simp
    have hA' : ApproximatesWithin δ' (Λ' ω (t / b))
        (fillCells (ε / b) (S'.η ω) (idlaCluster xs ⌊t / b / (ε / b)⌋₊)) := hA
    rw [hidx] at hA'
    exact happrox ε _ hA'
  · rw [← add_assoc, ENNReal.add_thirds]

/-- **Theorem 1.6** (theorem:convergence-of-div-sandpile, line 283) from Proposition 8.1 by scale invariance
(Section 8.1, lines 3284-3336). -/
theorem convergenceOfDivSandpile_of_steps (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hHB : HarmonicBallFamilyScalingStep) (hR : ConeScaleRadiusStep)
    (hT : ScaledClusterExitTimeStep) : ConvergenceOfDivSandpileStmt 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ δ t hδ ht
  unfold ProbTendsToOne
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨b, S', Λ', δ', B, hb, hS', hP, hΛ', hδ', hδ'ρ, hB, hgood⟩ :=
    Sec1.exists_rescaled_environment 𝒮 hEnv hHB hR hT hγ hγ2 hS hΛ hδ ht he
  have he3 : 0 < e / 3 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  have h8 := (h81 γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num) Ω S' hS' Λ' hΛ' δ' (t / b) hδ' hδ'ρ
    (div_pos ht hb)).2
  unfold TendsToOneOn at h8
  have hlim := h8.comp (Sec1.tendsto_div_const_nhdsGT hb)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (e / 3) he3] with ε hgε
  refine le_trans ?_ ((add_le_add hgε hB).trans_eq ?_)
  · show S.P _ ≤ S'.P _ + S.P B
    rw [hP]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hωB : ω ∈ B
    · exact Or.inr hωB
    · obtain ⟨hmult, hTω, happrox⟩ := hgood ω hωB
      refine Or.inl (And.intro hTω fun hA => hω ?_)
      have hidx : t / b / (ε / b) = t / ε := by field_simp
      have hA' : ApproximatesWithin δ' (Λ' ω (t / b))
          (fillCells (ε / b) (S'.η ω) (sandpileCluster (S'.mult (ε / b) ω) (t / b / (ε / b)))) := hA
      rw [hidx, hmult ε] at hA'
      exact happrox ε _ hA'
  · rw [← add_assoc, ENNReal.add_thirds]

/-- **Theorem 1.4** from Propositions 4.2, 5.1, 6.1, 7.1 (through Proposition 8.1,
`iDLAConstrainedConvergence_of_steps`) and the scaling steps. -/
theorem convergenceOfIDLA_of_bounds (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hHB : HarmonicBallFamilyScalingStep) (hR : ConeScaleRadiusStep)
    (hT : ScaledClusterExitTimeStep) : ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_steps 𝒮 (iDLAConstrainedConvergence_of_steps 𝒮 h42 h51 h61 h71) hEnv hHB hR hT

/-- **Theorem 1.6** from Propositions 4.2, 5.1, 6.1, 7.1 (through Proposition 8.1,
`iDLAConstrainedConvergence_of_steps`) and the scaling steps. -/
theorem convergenceOfDivSandpile_of_bounds (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hHB : HarmonicBallFamilyScalingStep) (hR : ConeScaleRadiusStep)
    (hT : ScaledClusterExitTimeStep) : ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_steps 𝒮 (iDLAConstrainedConvergence_of_steps 𝒮 h42 h51 h61 h71) hEnv hHB hR hT

end MatedCRT
