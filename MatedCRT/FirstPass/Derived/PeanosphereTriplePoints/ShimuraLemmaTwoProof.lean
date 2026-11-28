import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraGramSchmidt
import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.CorrelatedBMWindowIndependence
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Prob.BrownianDriftSmallBall
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique

/-!
# Shimura's Lemma 2 from the barrier statements

This file proves `ShimuraLemmaTwo γ` for `0 < γ < 2` from `KilledBarrierPositive` and
`PlanarTubePositive` (`shimuraLemmaTwo_of_barriers`), following the proof of Shimura's Lemma 2 for every
angle in the written answer `notes/mq-rigD2-shimura-answer.md`, §1 (M. Shimura, *Meandering points of
two-dimensional Brownian motion*, Kodai Math. J. 11 (1988), Lemma 2, (3.5), p. 172). The unit interval is
split into thirds.

* First third: `R` stays above `-Δ` and ends above `1`, while `L` moves by at most `5`; probability at
  least `c Δ` (`firstThird_event`, from the killed kernel bound in the coordinates `R` and `(L - ρ R)/σ`).
* Last third, read backwards from time `1`: `L` stays above `L 1 - δ` and `L (2/3) - L 1 ≥ 1`, while `R`
  moves by at most `5`; probability at least `c δ` (`lastThird_event`).
* Middle third: the increments follow the straight path along which `R` gains `20` and `L` loses `30`,
  within a tube; positive probability (`middleThird_event`, by tube positivity for the Gram–Schmidt
  coordinates `isCorrelatedBM2_map_gramSchmidtAt`).

The constants depart from answer §1: there the middle path is `w = 20 (v - u)/(1 - u · v)`, along which `L`
loses `20`, and the end pieces keep the perpendicular projection in `[-1, 1]` and stay within distance `4` of
their origin; here the end pieces keep the second coordinate in `[-1, 2]` and the other coordinate moves by at
most `5`, so the middle path lets `L` lose `30`.
* The increments on the three thirds are independent (`iIndepFun_thirdIncr`), and the three events
  together imply the four conditions of `G(Δ, δ)` (`lemmaTwo_deterministic`); the product of the three
  bounds is `G(Δ, δ) ≥ c Δ δ` (`lemmaTwo_of_law`). The law of the pair is unique, so the constant does
  not depend on the law (`shimuraLemmaTwo_of_barriers`).

Auxiliary statements:

* `indepFun_coneComb_future_swap`: the increments of `R` and the increments of the whitened coordinate
  `(L - ρ R) / σ` after any base time are independent (the exchange of the roles of `L` and `R` in
  `LatticeProb.CorrelatedBM.whitened_coneComb_brownian_independent`); each is a Brownian motion by
  `isBrownianReal_coneComb`.
* `windowSet`: the measurable set of paths whose values at the dyadic times up to `T` stay in an open
  interval; for continuous paths it lies in the closed version of the barrier event, and it contains
  the barrier event itself.
* `measure_inter_ge_of_indep`: a product lower bound for the probability that two independent
  continuous processes satisfy their barrier events.
* `barrierPair_lower_bound`: from `KilledBarrierPositive`, two independent Brownian motions with
  continuous paths satisfy, one in the barrier window `[-e, H]` ending in `[y₁, y₂]` and the other in the
  window `[-1, 2]`, with probability at least `c e`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MatedCRTHarmonic.MatedCRT LatticeProb
open LatticeProb.CorrelatedBM
open scoped NNReal ENNReal Topology

namespace MatedCRT.PeanosphereTriplePoints

/-- The increments of `R` and the whitened increments of `L` after the base time `c` are independent. -/
theorem indepFun_coneComb_future_swap {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (d c σ : ℝ) :
    IndepFun (fun ω (v : ℝ≥0) => coneComb 0 1 (c + d * v) c ω)
      (fun ω (v : ℝ≥0) => coneComb (1 / σ) (-lrCov γ 0 1 / σ) (c + d * v) c ω) μ := by
  refine GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := fun v : ℝ≥0 => coneComb 0 1 (c + d * v) c)
    (B := fun v : ℝ≥0 => coneComb (1 / σ) (-lrCov γ 0 1 / σ) (c + d * v) c)
    (fun v => coneComb_mem_span _ _ _ _) (fun v => coneComb_mem_span _ _ _ _) fun s t => ?_
  rw [cov_coneComb hμ]
  ring

/-- Paths whose values at the dyadic times `≤ T` stay at distance `∈ (lo, hi)` from the starting value. -/
def windowSet (T : ℝ≥0) (lo hi : ℝ) : Set (ℝ≥0 → ℝ) :=
  {f | ∀ n k : ℕ, dyadicGrid n k ≤ T →
    lo < f (dyadicGrid n k) - f 0 ∧ f (dyadicGrid n k) - f 0 < hi}

theorem measurable_sub_eval (a b : ℝ≥0) : Measurable fun f : ℝ≥0 → ℝ => f a - f b :=
  (measurable_pi_apply a).sub (measurable_pi_apply b)

theorem measurableSet_windowSet (T : ℝ≥0) (lo hi : ℝ) : MeasurableSet (windowSet T lo hi) := by
  have h : windowSet T lo hi = ⋂ n : ℕ, ⋂ k : ℕ, ⋂ (_ : dyadicGrid n k ≤ T),
      {f : ℝ≥0 → ℝ | lo < f (dyadicGrid n k) - f 0 ∧ f (dyadicGrid n k) - f 0 < hi} := by
    ext f
    simp [windowSet]
  rw [h]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_lt measurable_const (measurable_sub_eval _ _)).inter
    (measurableSet_lt (measurable_sub_eval _ _) measurable_const)

theorem mem_windowSet_of_forall {T : ℝ≥0} {lo hi : ℝ} {f : ℝ≥0 → ℝ}
    (h : ∀ s ≤ T, lo < f s - f 0 ∧ f s - f 0 < hi) : f ∈ windowSet T lo hi :=
  fun _ _ hk => h _ hk

/-- A continuous path in the window set stays in the closed window up to `T`. -/
theorem le_of_mem_windowSet {T : ℝ≥0} {lo hi : ℝ} {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (h : f ∈ windowSet T lo hi) {s : ℝ≥0} (hs : s ≤ T) : lo ≤ f s - f 0 ∧ f s - f 0 ≤ hi := by
  have hlim : Tendsto (fun N : ℕ => f (dyadicGrid N ⌊(s : ℝ) * 2 ^ N⌋₊) - f 0) atTop
      (𝓝 (f s - f 0)) :=
    ((hf.tendsto s).comp (tendsto_dyadicGrid_floor s)).sub_const _
  have hmem : ∀ N : ℕ, lo < f (dyadicGrid N ⌊(s : ℝ) * 2 ^ N⌋₊) - f 0 ∧
      f (dyadicGrid N ⌊(s : ℝ) * 2 ^ N⌋₊) - f 0 < hi := fun N =>
    h N _ ((dyadicGrid_floor_le s N).trans hs)
  exact ⟨ge_of_tendsto' hlim fun N => (hmem N).1.le, le_of_tendsto' hlim fun N => (hmem N).2.le⟩

/-- Product lower bound for two independent processes: events contained in measurable path events. -/
theorem measure_inter_ge_of_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℝ≥0 → Ω → ℝ} (hXY : IndepFun (fun ω v => X v ω) (fun ω v => Y v ω) μ)
    {SX SY : Set Ω} {AX AY : Set (ℝ≥0 → ℝ)} (hAX : MeasurableSet AX) (hAY : MeasurableSet AY)
    (hSX : SX ⊆ (fun ω v => X v ω) ⁻¹' AX) (hSY : SY ⊆ (fun ω v => Y v ω) ⁻¹' AY) :
    μ SX * μ SY ≤ μ ((fun ω v => X v ω) ⁻¹' AX ∩ (fun ω v => Y v ω) ⁻¹' AY) := by
  rw [hXY.measure_inter_preimage_eq_mul AX AY hAX hAY]
  exact mul_le_mul' (measure_mono hSX) (measure_mono hSY)

/-- **Two independent barrier events.**  For independent Brownian motions `X`, `Y` with continuous
paths, `X` stays in `[-e, H]` up to `T` and ends in `[y₁, y₂]` while `Y` stays in `[-1, 2]`, with
probability at least `c e` for `0 < e ≤ 1` (answer §1 keeps the perpendicular coordinate in `[-1, 1]`). -/
theorem barrierPair_lower_bound (hK : KilledBarrierPositive) {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : ℝ≥0 → Ω → ℝ} (hX : IsBrownianReal X μ)
    (hY : IsBrownianReal Y μ) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hind : IndepFun (fun ω v => X v ω) (fun ω v => Y v ω) μ)
    (T : ℝ≥0) (H y₁ y₂ : ℝ) (hT : 0 < T) (hy₁ : 0 < y₁) (hy : y₁ < y₂) (hH : y₂ < H) :
    ∃ c : ℝ, 0 < c ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ENNReal.ofReal (c * e) ≤ μ {ω | ((∀ s ≤ T, -e ≤ X s ω - X 0 ω ∧ X s ω - X 0 ω ≤ H) ∧
        X T ω - X 0 ω ∈ Icc y₁ y₂) ∧ ∀ s ≤ T, -1 ≤ Y s ω - Y 0 ω ∧ Y s ω - Y 0 ω ≤ 2} := by
  obtain ⟨c₁, hc₁, h₁⟩ := hK μ X hX T H y₁ y₂ hT hy₁ hy hH
  obtain ⟨c₂, hc₂, h₂⟩ := hK μ Y hY T 2 (1 / 2) 1 hT (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun e he he1 => ?_⟩
  have hAX : MeasurableSet (windowSet T (-e) H ∩ {f : ℝ≥0 → ℝ | f T - f 0 ∈ Ioo y₁ y₂}) :=
    (measurableSet_windowSet T _ _).inter
      (measurableSet_Ioo.preimage (measurable_sub_eval T 0))
  have hAY : MeasurableSet (windowSet T (-1) 2 ∩ {f : ℝ≥0 → ℝ | f T - f 0 ∈ Ioo (1 / 2) 1}) :=
    (measurableSet_windowSet T _ _).inter
      (measurableSet_Ioo.preimage (measurable_sub_eval T 0))
  have hprod := measure_inter_ge_of_indep hind hAX hAY
    (SX := {ω | (∀ s ≤ T, -e < X s ω - X 0 ω ∧ X s ω - X 0 ω < H) ∧
      X T ω - X 0 ω ∈ Ioo y₁ y₂})
    (SY := {ω | (∀ s ≤ T, -1 < Y s ω - Y 0 ω ∧ Y s ω - Y 0 ω < 2) ∧
      Y T ω - Y 0 ω ∈ Ioo (1 / 2) 1})
    (fun ω hω => ⟨mem_windowSet_of_forall hω.1, hω.2⟩)
    (fun ω hω => ⟨mem_windowSet_of_forall hω.1, hω.2⟩)
  have h2' := h₂ 1 one_pos le_rfl
  rw [mul_one] at h2'
  calc ENNReal.ofReal (c₁ * c₂ * e) = ENNReal.ofReal (c₁ * e) * ENNReal.ofReal c₂ := by
        rw [← ENNReal.ofReal_mul (mul_pos hc₁ he).le]
        congr 1
        ring
    _ ≤ μ _ * μ _ := mul_le_mul' (h₁ e he he1) h2'
    _ ≤ _ := hprod
    _ ≤ _ := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hω
        exact ⟨⟨fun s hs => le_of_mem_windowSet (hXc ω) hx1 hs, ⟨hx2.1.le, hx2.2.le⟩⟩,
          fun s hs => le_of_mem_windowSet (hYc ω) hy1 hs⟩

/-- **The deterministic combination of the three thirds** (Shimura's Lemma 2, `G(Δ, δ)`): the bounds on
the three thirds of `[0, 1]` imply the four conditions of the event. -/
theorem lemmaTwo_deterministic {L R : ℝ → ℝ} {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hR1 : ∀ s ∈ Icc (0 : ℝ) (1 / 3), -Δ ≤ R s - R 0)
    (hL1 : ∀ s ∈ Icc (0 : ℝ) (1 / 3), |L s - L 0| ≤ 5)
    (hR1e : 1 ≤ R (1 / 3) - R 0)
    (hRm : ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), -(1 / 4) ≤ R s - R (1 / 3))
    (hRme : 20 - 1 / 4 ≤ R (2 / 3) - R (1 / 3))
    (hLm : ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), |(L s - L (1 / 3)) + 90 * (s - 1 / 3)| ≤ 1 / 2)
    (hL3 : ∀ s ∈ Icc (2 / 3 : ℝ) 1, -δ ≤ L s - L 1)
    (hR3 : ∀ s ∈ Icc (2 / 3 : ℝ) 1, |R s - R 1| ≤ 5)
    (hL3e : 1 ≤ L (2 / 3) - L 1) :
    (∀ s ∈ Icc (0 : ℝ) 1, -Δ ≤ R s - R 0) ∧ 1 ≤ R 1 - R 0 ∧
      (∀ s ∈ Icc (0 : ℝ) 1, L 1 - δ ≤ L s) ∧ L 1 - L 0 ≤ -1 := by
  have h13 : (1 / 3 : ℝ) ∈ Icc (0 : ℝ) (1 / 3) := ⟨by norm_num, le_rfl⟩
  have h23m : (2 / 3 : ℝ) ∈ Icc (1 / 3 : ℝ) (2 / 3) := ⟨by norm_num, le_rfl⟩
  have h23 : (2 / 3 : ℝ) ∈ Icc (2 / 3 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hL13 := abs_le.1 (hL1 (1 / 3) h13)
  have hLm23 := abs_le.1 (hLm (2 / 3) h23m)
  have hR323 := abs_le.1 (hR3 (2 / 3) h23)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases le_total s (1 / 3) with h | h
    · exact hR1 s ⟨hs.1, h⟩
    · rcases le_total s (2 / 3) with h' | h'
      · have := hRm s ⟨h, h'⟩
        linarith
      · have := abs_le.1 (hR3 s ⟨h', hs.2⟩)
        linarith
  · linarith
  · intro s hs
    rcases le_total s (1 / 3) with h | h
    · have := abs_le.1 (hL1 s ⟨hs.1, h⟩)
      linarith
    · rcases le_total s (2 / 3) with h' | h'
      · have := abs_le.1 (hLm s ⟨h, h'⟩)
        linarith
      · have := hL3 s ⟨h', hs.2⟩
        linarith
  · linarith


/-- The standard deviation of the whitened coordinate and the Brownian-motion normalisation. -/
private theorem whitened_norm {ρ σ : ℝ} (hσ : 0 < σ) (hσsq : σ * σ = 1 - ρ ^ 2) :
    1 / σ * (1 / σ) + -ρ / σ * (-ρ / σ) + (1 / σ * (-ρ / σ) + -ρ / σ * (1 / σ)) * ρ = 1 := by
  rw [show 1 / σ * (1 / σ) + -ρ / σ * (-ρ / σ) + (1 / σ * (-ρ / σ) + -ρ / σ * (1 / σ)) * ρ =
    (1 - ρ ^ 2) / (σ * σ) by ring, ← hσsq]
  exact div_self (mul_pos hσ hσ).ne'

/-- **The first third.**  For `R`-first Gram–Schmidt coordinates, with probability at least `c Δ` the
coordinate `R` stays above `-Δ` on `[0, 1/3]` and ends above `1`, while `L` moves by at most `5` (answer §1:
within distance `4`). -/
theorem firstThird_event (hK : KilledBarrierPositive) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 →
      ENNReal.ofReal (c * Δ) ≤ μ {ω | (∀ s ∈ Icc (0 : ℝ) (1 / 3), -Δ ≤ (ω s).2 - (ω 0).2) ∧
        1 ≤ (ω (1 / 3)).2 - (ω 0).2 ∧ ∀ s ∈ Icc (0 : ℝ) (1 / 3), |(ω s).1 - (ω 0).1| ≤ 5} := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hρlo, hρhi⟩ := lrCov_mem_Ioo hγ0 hγ2
  set ρ := lrCov γ 0 1 with hρ
  set σ := Real.sqrt (1 - ρ ^ 2) with hσdef
  have hpos : 0 < 1 - ρ ^ 2 := by nlinarith
  have hσsq : σ * σ = 1 - ρ ^ 2 := Real.mul_self_sqrt hpos.le
  have hσ : 0 < σ := Real.sqrt_pos.2 hpos
  have hσ1 : σ ≤ 1 := by nlinarith
  have hX : IsBrownianReal (fun v : ℝ≥0 => coneComb 0 1 v 0) μ := by
    simpa only [zero_add, one_mul] using
      isBrownianReal_coneComb hμ (α := 0) (β := 1) (e := 1) (by norm_num) (by ring) 0
  have hY : IsBrownianReal (fun v : ℝ≥0 => coneComb (1 / σ) (-ρ / σ) v 0) μ := by
    simpa only [zero_add, one_mul] using
      isBrownianReal_coneComb hμ (α := 1 / σ) (β := -ρ / σ) (e := 1) (by norm_num)
        (whitened_norm hσ hσsq) 0
  have hind : IndepFun (fun ω (v : ℝ≥0) => coneComb 0 1 v 0 ω)
      (fun ω (v : ℝ≥0) => coneComb (1 / σ) (-ρ / σ) v 0 ω) μ := by
    simpa only [zero_add, one_mul] using indepFun_coneComb_future_swap hμ 1 0 σ
  have hXc : ∀ ω, Continuous fun v : ℝ≥0 => coneComb 0 1 v 0 ω := fun ω => by
    simpa only [zero_add, one_mul] using continuous_coneComb_apply 0 1 0 1 ω
  have hYc : ∀ ω, Continuous fun v : ℝ≥0 => coneComb (1 / σ) (-ρ / σ) v 0 ω := fun ω => by
    simpa only [zero_add, one_mul] using continuous_coneComb_apply (1 / σ) (-ρ / σ) 0 1 ω
  obtain ⟨c, hc, hbd⟩ := barrierPair_lower_bound hK hX hY hXc hYc hind (1 / 3) 3 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun Δ hΔ hΔ1 => (hbd Δ hΔ hΔ1).trans (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨⟨hR, hRend⟩, hW⟩ := hω
  have hRform : ∀ x : ℝ, coneComb 0 1 x 0 ω = (ω x).2 - (ω 0).2 := fun x => by
    simp [coneComb, coneIncr, lrCoord]
  have hWform : ∀ x : ℝ, coneComb (1 / σ) (-ρ / σ) x 0 ω =
      1 / σ * ((ω x).1 - (ω 0).1) + -ρ / σ * ((ω x).2 - (ω 0).2) := fun x => by
    simp [coneComb, coneIncr, lrCoord]
  have h0R : coneComb 0 1 ((0 : ℝ≥0) : ℝ) 0 ω = 0 := by simp [coneComb, coneIncr]
  have h0W : coneComb (1 / σ) (-ρ / σ) ((0 : ℝ≥0) : ℝ) 0 ω = 0 := by simp [coneComb, coneIncr]
  have hnn : ∀ s : ℝ, s ∈ Icc (0 : ℝ) (1 / 3) → s.toNNReal ≤ (1 / 3 : ℝ≥0) := fun s hs => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    simpa using hs.2
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
  · have h := (hR s.toNNReal (hnn s hs)).1
    rw [h0R, sub_zero, Real.coe_toNNReal _ hs.1, hRform] at h
    exact h
  · have h := hRend.1
    rw [h0R, sub_zero, hRform] at h
    simpa using h
  · have hRs := hR s.toNNReal (hnn s hs)
    have hWs := hW s.toNNReal (hnn s hs)
    rw [h0R, sub_zero, Real.coe_toNNReal _ hs.1, hRform] at hRs
    rw [h0W, sub_zero, Real.coe_toNNReal _ hs.1, hWform] at hWs
    have hL : (ω s).1 - (ω 0).1 = σ * (1 / σ * ((ω s).1 - (ω 0).1) + -ρ / σ * ((ω s).2 - (ω 0).2)) +
        ρ * ((ω s).2 - (ω 0).2) := by
      field_simp
      ring
    rw [hL]
    have h1 : |σ * (1 / σ * ((ω s).1 - (ω 0).1) + -ρ / σ * ((ω s).2 - (ω 0).2))| ≤ 2 := by
      rw [abs_mul, abs_of_pos hσ]
      have : |1 / σ * ((ω s).1 - (ω 0).1) + -ρ / σ * ((ω s).2 - (ω 0).2)| ≤ 2 :=
        abs_le.2 ⟨by linarith [hWs.1], hWs.2⟩
      nlinarith [abs_nonneg (1 / σ * ((ω s).1 - (ω 0).1) + -ρ / σ * ((ω s).2 - (ω 0).2))]
    have h2 : |ρ * ((ω s).2 - (ω 0).2)| ≤ 3 := by
      rw [abs_mul]
      have hρa : |ρ| ≤ 1 := abs_le.2 ⟨hρlo.le, hρhi.le⟩
      have : |(ω s).2 - (ω 0).2| ≤ 3 := abs_le.2 ⟨by linarith [hRs.1], hRs.2⟩
      nlinarith [abs_nonneg ρ, abs_nonneg ((ω s).2 - (ω 0).2)]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 + 3 := add_le_add h1 h2
      _ = 5 := by norm_num

/-- **The last third**, read backwards from time `1` with `L` first.  With probability at least `c δ`
the coordinate `L` stays above `L 1 - δ` on `[2/3, 1]` and `L (2/3) - L 1 ≥ 1`, while `R` moves by
at most `5` from its value at `1` (answer §1: within distance `4`). -/
theorem lastThird_event (hK : KilledBarrierPositive) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ENNReal.ofReal (c * δ) ≤ μ {ω | (∀ s ∈ Icc (2 / 3 : ℝ) 1, -δ ≤ (ω s).1 - (ω 1).1) ∧
        1 ≤ (ω (2 / 3)).1 - (ω 1).1 ∧ ∀ s ∈ Icc (2 / 3 : ℝ) 1, |(ω s).2 - (ω 1).2| ≤ 5} := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hρlo, hρhi⟩ := lrCov_mem_Ioo hγ0 hγ2
  set ρ := lrCov γ 0 1 with hρ
  set σ := Real.sqrt (1 - ρ ^ 2) with hσdef
  have hpos : 0 < 1 - ρ ^ 2 := by nlinarith
  have hσsq : σ * σ = 1 - ρ ^ 2 := Real.mul_self_sqrt hpos.le
  have hσ : 0 < σ := Real.sqrt_pos.2 hpos
  have hσ1 : σ ≤ 1 := by nlinarith
  have hX : IsBrownianReal (fun v : ℝ≥0 => coneComb 1 0 (1 + -1 * v) 1) μ :=
    isBrownianReal_coneComb hμ (α := 1) (β := 0) (e := -1) (by norm_num) (by ring) 1
  have hY : IsBrownianReal (fun v : ℝ≥0 => coneComb (-ρ / σ) (1 / σ) (1 + -1 * v) 1) μ :=
    isBrownianReal_coneComb hμ (α := -ρ / σ) (β := 1 / σ) (e := -1) (by norm_num)
      (by linear_combination whitened_norm hσ hσsq) 1
  have hind : IndepFun (fun ω (v : ℝ≥0) => coneComb 1 0 (1 + -1 * v) 1 ω)
      (fun ω (v : ℝ≥0) => coneComb (-ρ / σ) (1 / σ) (1 + -1 * v) 1 ω) μ :=
    indepFun_coneComb_future hμ (-1) 1 σ
  have hXc : ∀ ω, Continuous fun v : ℝ≥0 => coneComb 1 0 (1 + -1 * v) 1 ω := fun ω =>
    continuous_coneComb_apply 1 0 1 (-1) ω
  have hYc : ∀ ω, Continuous fun v : ℝ≥0 => coneComb (-ρ / σ) (1 / σ) (1 + -1 * v) 1 ω :=
    fun ω => continuous_coneComb_apply (-ρ / σ) (1 / σ) 1 (-1) ω
  obtain ⟨c, hc, hbd⟩ := barrierPair_lower_bound hK hX hY hXc hYc hind (1 / 3) 3 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun δ hδ hδ1 => (hbd δ hδ hδ1).trans (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨⟨hR, hRend⟩, hW⟩ := hω
  have hLform : ∀ x : ℝ, coneComb 1 0 x 1 ω = (ω x).1 - (ω 1).1 := fun x => by
    simp [coneComb, coneIncr, lrCoord]
  have hWform : ∀ x : ℝ, coneComb (-ρ / σ) (1 / σ) x 1 ω =
      -ρ / σ * ((ω x).1 - (ω 1).1) + 1 / σ * ((ω x).2 - (ω 1).2) := fun x => by
    simp [coneComb, coneIncr, lrCoord]
  have h0L : coneComb 1 0 (1 + -1 * ((0 : ℝ≥0) : ℝ)) 1 ω = 0 := by simp [coneComb, coneIncr]
  have h0W : coneComb (-ρ / σ) (1 / σ) (1 + -1 * ((0 : ℝ≥0) : ℝ)) 1 ω = 0 := by
    simp [coneComb, coneIncr]
  have hnn : ∀ s : ℝ, s ∈ Icc (2 / 3 : ℝ) 1 → (1 - s).toNNReal ≤ (1 / 3 : ℝ≥0) := fun s hs => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith [hs.2])]
    have h : (((1 / 3 : ℝ≥0)) : ℝ) = 1 / 3 := by norm_num
    rw [h]
    linarith [hs.1]
  have harg : ∀ s : ℝ, s ∈ Icc (2 / 3 : ℝ) 1 → 1 + -1 * (((1 - s).toNNReal : ℝ≥0) : ℝ) = s :=
    fun s hs => by
      rw [Real.coe_toNNReal _ (by linarith [hs.2])]
      ring
  have hend : 1 + -1 * (((1 / 3 : ℝ≥0)) : ℝ) = 2 / 3 := by
    have h : (((1 / 3 : ℝ≥0)) : ℝ) = 1 / 3 := by norm_num
    rw [h]
    norm_num
  refine ⟨fun s hs => ?_, ?_, fun s hs => ?_⟩
  · have h := (hR _ (hnn s hs)).1
    rw [h0L, sub_zero, harg s hs, hLform] at h
    exact h
  · have h := hRend.1
    rw [h0L, sub_zero, hend, hLform] at h
    exact h
  · have hLs := hR _ (hnn s hs)
    have hWs := hW _ (hnn s hs)
    rw [h0L, sub_zero, harg s hs, hLform] at hLs
    rw [h0W, sub_zero, harg s hs, hWform] at hWs
    have hR2 : (ω s).2 - (ω 1).2 = σ * (-ρ / σ * ((ω s).1 - (ω 1).1) +
        1 / σ * ((ω s).2 - (ω 1).2)) + ρ * ((ω s).1 - (ω 1).1) := by
      field_simp
      ring
    rw [hR2]
    have h1 : |σ * (-ρ / σ * ((ω s).1 - (ω 1).1) + 1 / σ * ((ω s).2 - (ω 1).2))| ≤ 2 := by
      rw [abs_mul, abs_of_pos hσ]
      have : |-ρ / σ * ((ω s).1 - (ω 1).1) + 1 / σ * ((ω s).2 - (ω 1).2)| ≤ 2 :=
        abs_le.2 ⟨by linarith [hWs.1], hWs.2⟩
      nlinarith [abs_nonneg (-ρ / σ * ((ω s).1 - (ω 1).1) + 1 / σ * ((ω s).2 - (ω 1).2))]
    have h2 : |ρ * ((ω s).1 - (ω 1).1)| ≤ 3 := by
      rw [abs_mul]
      have hρa : |ρ| ≤ 1 := abs_le.2 ⟨hρlo.le, hρhi.le⟩
      have : |(ω s).1 - (ω 1).1| ≤ 3 := abs_le.2 ⟨by linarith [hLs.1], hLs.2⟩
      nlinarith [abs_nonneg ρ, abs_nonneg ((ω s).1 - (ω 1).1)]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 + 3 := add_le_add h1 h2
      _ = 5 := by norm_num

/-! ### The middle third -/

/-- The end point of the straight path of the middle third in the Gram–Schmidt coordinates
`(R, (L - ρ R) / σ)`: along this path `R` gains `20` and `L` loses `30` (the vector `w` of answer §1, along which
`L` loses `20`, lengthened to absorb the end pieces of this proof, which move by at most `5`). -/
noncomputable def middleDirection (γ : ℝ) : ℝ × ℝ :=
  (20, (-30 - 20 * lrCov γ 0 1) / Real.sqrt (1 - lrCov γ 0 1 ^ 2))

/-- Paths whose increments up to time `T` stay within distance at most `ε` of the straight path from
`0` to `w`. -/
def closedTube (T : ℝ) (w : ℝ × ℝ) (ε : ℝ) : Set Path2 :=
  {p | ∀ s ∈ Icc (0 : ℝ) T, dist (p s - p 0) ((s / T) • w) ≤ ε}

theorem isClosed_closedTube (T : ℝ) (w : ℝ × ℝ) (ε : ℝ) : IsClosed (closedTube T w ε) := by
  have h : closedTube T w ε =
      ⋂ s ∈ Icc (0 : ℝ) T, {p : Path2 | dist (p s - p 0) ((s / T) • w) ≤ ε} := by
    ext p
    simp [closedTube]
  rw [h]
  refine isClosed_biInter fun s _ => isClosed_le ?_ continuous_const
  exact ((continuous_eval_const s).sub (continuous_eval_const 0)).dist continuous_const

/-- The coordinate `L` on the middle third from its Gram–Schmidt coordinates: if `a` is within `1/4`
of `60 t` and `(b - ρ a) / σ` is within `1/4` of `3 t (-30 - 20 ρ) / σ`, then `b` is within `1/2`
of `-90 t`. -/
private theorem middle_coord_bound {a b t ρ σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hρ : |ρ| ≤ 1)
    (h1 : |a - t / (1 / 3) * 20| ≤ 1 / 4)
    (h2 : |(b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ)| ≤ 1 / 4) :
    |b + 90 * t| ≤ 1 / 2 := by
  have hX : σ * ((b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ)) =
      b - ρ * a + 90 * t + 60 * ρ * t := by
    rw [show (b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ) =
      (b - ρ * a + 90 * t + 60 * ρ * t) / σ by ring, mul_div_cancel₀ _ hσ.ne']
  have key : b + 90 * t = σ * ((b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ)) +
      ρ * (a - t / (1 / 3) * 20) := by
    rw [hX]
    ring
  rw [key]
  calc _ ≤ |σ * ((b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ))| +
        |ρ * (a - t / (1 / 3) * 20)| := abs_add_le _ _
    _ = σ * |(b - ρ * a) / σ - t / (1 / 3) * ((-30 - 20 * ρ) / σ)| +
        |ρ| * |a - t / (1 / 3) * 20| := by rw [abs_mul, abs_mul, abs_of_pos hσ]
    _ ≤ 1 * (1 / 4) + 1 * (1 / 4) :=
        add_le_add (mul_le_mul hσ1 h2 (abs_nonneg _) zero_le_one)
          (mul_le_mul hρ h1 (abs_nonneg _) zero_le_one)
    _ = 1 / 2 := by norm_num

/-- **The middle third** (answer §1: the increments stay within `1/4` of the straight path to `w`,
an event of fixed positive probability by tube positivity). With positive probability, on
`[1/3, 2/3]` the coordinate `R` stays above `R (1/3) - 1/4` and gains at least `20 - 1/4`, while
`L s - L (1/3)` stays within `1/2` of `-90 (s - 1/3)`. -/
theorem middleThird_event (hT : PlanarTubePositive) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    0 < μ {ω | (∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), -(1 / 4) ≤ (ω s).2 - (ω (1 / 3)).2) ∧
      20 - 1 / 4 ≤ (ω (2 / 3)).2 - (ω (1 / 3)).2 ∧
      ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), |((ω s).1 - (ω (1 / 3)).1) + 90 * (s - 1 / 3)| ≤ 1 / 2} := by
  obtain ⟨hρlo, hρhi⟩ := lrCov_mem_Ioo hγ0 hγ2
  have hpos : 0 < 1 - lrCov γ 0 1 ^ 2 := by nlinarith
  have hσsq : Real.sqrt (1 - lrCov γ 0 1 ^ 2) * Real.sqrt (1 - lrCov γ 0 1 ^ 2) =
      1 - lrCov γ 0 1 ^ 2 := Real.mul_self_sqrt hpos.le
  have hσ : 0 < Real.sqrt (1 - lrCov γ 0 1 ^ 2) := Real.sqrt_pos.2 hpos
  have hσ1 : Real.sqrt (1 - lrCov γ 0 1 ^ 2) ≤ 1 := by nlinarith
  have hρa : |lrCov γ 0 1| ≤ 1 := abs_le.2 ⟨hρlo.le, hρhi.le⟩
  have hΦ : Measurable (gramSchmidtAt γ (1 / 3)) :=
    (continuous_gramSchmidtAt γ (1 / 3)).measurable
  have hν := isCorrelatedBM2_map_gramSchmidtAt hγ0 hγ2 (1 / 3) hμ
  have htube := hT _ hν (1 / 3) (middleDirection γ) (1 / 4) (by norm_num) (by norm_num)
  have hle : μ.map (gramSchmidtAt γ (1 / 3))
      {p | ∀ s ∈ Icc (0 : ℝ) (1 / 3), dist (p s - p 0) ((s / (1 / 3)) • middleDirection γ) < 1 / 4} ≤
      μ (gramSchmidtAt γ (1 / 3) ⁻¹' closedTube (1 / 3) (middleDirection γ) (1 / 4)) := by
    rw [← Measure.map_apply hΦ (isClosed_closedTube _ _ _).measurableSet]
    exact measure_mono fun p hp s hs => (hp s hs).le
  refine (htube.trans_le hle).trans_le (measure_mono fun ω hω => ?_)
  have hω' : ∀ u ∈ Icc (0 : ℝ) (1 / 3),
      dist (gramSchmidtAt γ (1 / 3) ω u - gramSchmidtAt γ (1 / 3) ω 0)
        ((u / (1 / 3)) • middleDirection γ) ≤ 1 / 4 := hω
  have hcoord : ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3),
      |((ω s).2 - (ω (1 / 3)).2) - (s - 1 / 3) / (1 / 3) * 20| ≤ 1 / 4 ∧
      |((ω s).1 - (ω (1 / 3)).1) + 90 * (s - 1 / 3)| ≤ 1 / 2 := by
    intro s hs
    have hu : s - 1 / 3 ∈ Icc (0 : ℝ) (1 / 3) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h := hω' (s - 1 / 3) hu
    have e : (1 / 3 : ℝ) + (s - 1 / 3) = s := by ring
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at h
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      gramSchmidtAt_apply, middleDirection, e, add_zero, sub_self, mul_zero, zero_div,
      sub_zero] at h
    exact ⟨h.1, middle_coord_bound hσ hσ1 hρa h.1 h.2⟩
  refine ⟨fun s hs => ?_, ?_, fun s hs => (hcoord s hs).2⟩
  · have h := (abs_le.1 (hcoord s hs).1).1
    have e : (s - 1 / 3) / (1 / 3) * 20 = 60 * (s - 1 / 3) := by ring
    rw [e] at h
    linarith [hs.1]
  · have h := (abs_le.1 (hcoord (2 / 3) ⟨by norm_num, le_rfl⟩).1).1
    have e : ((2 : ℝ) / 3 - 1 / 3) / (1 / 3) * 20 = 20 := by norm_num
    rw [e] at h
    linarith

/-! ### Independence of the three thirds -/

/-- The left end points of the thirds of `[0, 1]`. -/
noncomputable def thirdL : Fin 3 → ℝ := ![0, 1 / 3, 2 / 3]

/-- The right end points of the thirds of `[0, 1]`. -/
noncomputable def thirdR : Fin 3 → ℝ := ![1 / 3, 2 / 3, 1]

theorem thirdL_le_thirdR (i : Fin 3) : thirdL i ≤ thirdR i := by
  fin_cases i <;> norm_num [thirdL, thirdR]

theorem thirdR_le_one (i : Fin 3) : thirdR i ≤ 1 := by
  fin_cases i <;> norm_num [thirdR]

/-- The increments of the pair on the third `i` of `[0, 1]` from its left end point, at the rational
times clamped to the third. -/
noncomputable def thirdIncr (i : Fin 3) (ω : Path2) (p : Fin 2 × ℚ) : ℝ :=
  coneIncr p.1 (projIcc (thirdL i) (thirdR i) (thirdL_le_thirdR i) p.2) (thirdL i) ω

theorem thirdIncr_fst (i : Fin 3) (ω : Path2) (q : ℚ) :
    thirdIncr i ω (0, q) =
      (ω (projIcc (thirdL i) (thirdR i) (thirdL_le_thirdR i) q)).1 - (ω (thirdL i)).1 := by
  simp [thirdIncr, coneIncr, lrCoord]

theorem thirdIncr_snd (i : Fin 3) (ω : Path2) (q : ℚ) :
    thirdIncr i ω (1, q) =
      (ω (projIcc (thirdL i) (thirdR i) (thirdL_le_thirdR i) q)).2 - (ω (thirdL i)).2 := by
  simp [thirdIncr, coneIncr, lrCoord]

theorem thirdIncr_end_fst (i : Fin 3) (ω : Path2) :
    thirdIncr i ω (0, 1) = (ω (thirdR i)).1 - (ω (thirdL i)).1 := by
  rw [thirdIncr_fst, Rat.cast_one, projIcc_of_right_le _ (thirdR_le_one i)]

theorem thirdIncr_end_snd (i : Fin 3) (ω : Path2) :
    thirdIncr i ω (1, 1) = (ω (thirdR i)).2 - (ω (thirdL i)).2 := by
  rw [thirdIncr_snd, Rat.cast_one, projIcc_of_right_le _ (thirdR_le_one i)]

/-- **Independence of the thirds**: the increments of the pair on the three thirds of `[0, 1]` are
independent (independent increments of the correlated pair, `iIndepFun_increment_windows`). -/
theorem iIndepFun_thirdIncr {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    iIndepFun thirdIncr μ := by
  have hsep : ∀ i j : Fin 3, i ≠ j → thirdR i ≤ thirdL j ∨ thirdR j ≤ thirdL i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | norm_num [thirdL, thirdR]
  exact (iIndepFun_increment_windows hμ thirdL thirdR hsep).comp
    (fun i f (p : Fin 2 × ℚ) => f (p.1, projIcc (thirdL i) (thirdR i) (thirdL_le_thirdR i) p.2))
    (fun i => Measurable.of_eval fun p => measurable_pi_apply _)

/-- A closed condition on a continuous function of time that holds at the rational times, clamped to
`[a, b]`, holds on `[a, b]`. -/
theorem forall_Icc_of_forall_rat {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} (hg : Continuous g)
    {C : Set ℝ} (hC : IsClosed C) (h : ∀ q : ℚ, g (projIcc a b hab q) ∈ C) :
    ∀ s ∈ Icc a b, g s ∈ C := by
  have hF : Continuous fun x : ℝ => g (projIcc a b hab x) :=
    hg.comp (continuous_subtype_val.comp continuous_projIcc)
  have hsub : range ((↑) : ℚ → ℝ) ⊆ (fun x : ℝ => g (projIcc a b hab x)) ⁻¹' C := by
    rintro _ ⟨q, rfl⟩
    exact h q
  have hall := closure_minimal hsub (hC.preimage hF)
  rw [(Rat.denseRange_cast (𝕜 := ℝ)).closure_range] at hall
  intro s hs
  have hs' : g (projIcc a b hab s) ∈ C := hall (mem_univ s)
  rw [projIcc_of_mem hab hs] at hs'
  exact hs'

/-- The event of the first third at the rational times, for the increments from time `0`. -/
def firstThirdSet (Δ : ℝ) : Set (Fin 2 × ℚ → ℝ) :=
  {f | (∀ q : ℚ, -Δ ≤ f (1, q) ∧ |f (0, q)| ≤ 5) ∧ 1 ≤ f (1, 1)}

/-- The event of the middle third at the rational times, for the increments from time `1/3`. -/
def middleThirdSet : Set (Fin 2 × ℚ → ℝ) :=
  {f | (∀ q : ℚ, -(1 / 4) ≤ f (1, q) ∧
      |f (0, q) + 90 * ((projIcc (thirdL 1) (thirdR 1) (thirdL_le_thirdR 1) q : ℝ) - thirdL 1)| ≤
        1 / 2) ∧ 20 - 1 / 4 ≤ f (1, 1)}

/-- The event of the last third at the rational times, for the increments from time `2/3`. -/
def lastThirdSet (δ : ℝ) : Set (Fin 2 × ℚ → ℝ) :=
  {f | (∀ q : ℚ, -δ ≤ f (0, q) - f (0, 1) ∧ |f (1, q) - f (1, 1)| ≤ 5) ∧ 1 ≤ -f (0, 1)}

/-- The events of the three thirds at the rational times. -/
def thirdSets (Δ δ : ℝ) : Fin 3 → Set (Fin 2 × ℚ → ℝ) :=
  ![firstThirdSet Δ, middleThirdSet, lastThirdSet δ]

theorem measurableSet_firstThirdSet (Δ : ℝ) : MeasurableSet (firstThirdSet Δ) := by
  simp only [firstThirdSet, ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun q =>
    (measurableSet_le measurable_const (measurable_pi_apply _)).inter
      (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _))
        measurable_const)).inter (measurableSet_le measurable_const (measurable_pi_apply _))

theorem measurableSet_middleThirdSet : MeasurableSet middleThirdSet := by
  simp only [middleThirdSet, ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun q =>
    (measurableSet_le measurable_const (measurable_pi_apply _)).inter
      (measurableSet_le (continuous_abs.measurable.comp ((measurable_pi_apply _).add_const _))
        measurable_const)).inter (measurableSet_le measurable_const (measurable_pi_apply _))

theorem measurableSet_lastThirdSet (δ : ℝ) : MeasurableSet (lastThirdSet δ) := by
  have hm : ∀ p : Fin 2 × ℚ, Measurable fun f : Fin 2 × ℚ → ℝ => f p := fun p =>
    measurable_pi_apply p
  simp only [lastThirdSet, ofPred_and, ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun q => MeasurableSet.inter ?_ ?_) ?_
  · exact measurableSet_le measurable_const ((hm (0, q)).sub (hm (0, 1)))
  · exact measurableSet_le (continuous_abs.measurable.comp ((hm (1, q)).sub (hm (1, 1))))
      measurable_const
  · exact measurableSet_le measurable_const (hm (0, 1)).neg

theorem firstThird_subset (Δ : ℝ) :
    {ω : Path2 | (∀ s ∈ Icc (0 : ℝ) (1 / 3), -Δ ≤ (ω s).2 - (ω 0).2) ∧
        1 ≤ (ω (1 / 3)).2 - (ω 0).2 ∧ ∀ s ∈ Icc (0 : ℝ) (1 / 3), |(ω s).1 - (ω 0).1| ≤ 5} ⊆
      thirdIncr 0 ⁻¹' firstThirdSet Δ := by
  intro ω hω
  show (∀ q : ℚ, -Δ ≤ thirdIncr 0 ω (1, q) ∧ |thirdIncr 0 ω (0, q)| ≤ 5) ∧
    1 ≤ thirdIncr 0 ω (1, 1)
  refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
  · rw [thirdIncr_snd]
    exact hω.1 _ (projIcc (thirdL 0) (thirdR 0) (thirdL_le_thirdR 0) q).2
  · rw [thirdIncr_fst]
    exact hω.2.2 _ (projIcc (thirdL 0) (thirdR 0) (thirdL_le_thirdR 0) q).2
  · rw [thirdIncr_end_snd]
    exact hω.2.1

theorem middleThird_subset :
    {ω : Path2 | (∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), -(1 / 4) ≤ (ω s).2 - (ω (1 / 3)).2) ∧
        20 - 1 / 4 ≤ (ω (2 / 3)).2 - (ω (1 / 3)).2 ∧
        ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), |((ω s).1 - (ω (1 / 3)).1) + 90 * (s - 1 / 3)| ≤ 1 / 2} ⊆
      thirdIncr 1 ⁻¹' middleThirdSet := by
  intro ω hω
  show (∀ q : ℚ, -(1 / 4) ≤ thirdIncr 1 ω (1, q) ∧
      |thirdIncr 1 ω (0, q) +
        90 * ((projIcc (thirdL 1) (thirdR 1) (thirdL_le_thirdR 1) q : ℝ) - thirdL 1)| ≤ 1 / 2) ∧
    20 - 1 / 4 ≤ thirdIncr 1 ω (1, 1)
  refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
  · rw [thirdIncr_snd]
    exact hω.1 _ (projIcc (thirdL 1) (thirdR 1) (thirdL_le_thirdR 1) q).2
  · rw [thirdIncr_fst]
    exact hω.2.2 _ (projIcc (thirdL 1) (thirdR 1) (thirdL_le_thirdR 1) q).2
  · rw [thirdIncr_end_snd]
    exact hω.2.1

theorem lastThird_subset (δ : ℝ) :
    {ω : Path2 | (∀ s ∈ Icc (2 / 3 : ℝ) 1, -δ ≤ (ω s).1 - (ω 1).1) ∧
        1 ≤ (ω (2 / 3)).1 - (ω 1).1 ∧ ∀ s ∈ Icc (2 / 3 : ℝ) 1, |(ω s).2 - (ω 1).2| ≤ 5} ⊆
      thirdIncr 2 ⁻¹' lastThirdSet δ := by
  intro ω hω
  show (∀ q : ℚ, -δ ≤ thirdIncr 2 ω (0, q) - thirdIncr 2 ω (0, 1) ∧
      |thirdIncr 2 ω (1, q) - thirdIncr 2 ω (1, 1)| ≤ 5) ∧ 1 ≤ -thirdIncr 2 ω (0, 1)
  refine ⟨fun q => ⟨?_, ?_⟩, ?_⟩
  · rw [thirdIncr_end_fst, thirdIncr_fst, sub_sub_sub_cancel_right]
    exact hω.1 _ (projIcc (thirdL 2) (thirdR 2) (thirdL_le_thirdR 2) q).2
  · rw [thirdIncr_end_snd, thirdIncr_snd, sub_sub_sub_cancel_right]
    exact hω.2.2 _ (projIcc (thirdL 2) (thirdR 2) (thirdL_le_thirdR 2) q).2
  · rw [thirdIncr_end_fst, neg_sub]
    exact hω.2.1

/-- The events of the three thirds, read at the rational times, together give the four conditions
of `G(Δ, δ)` (continuity of the paths and `lemmaTwo_deterministic`). -/
theorem inter_thirds_subset {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ) :
    (⋂ i ∈ (Finset.univ : Finset (Fin 3)), thirdIncr i ⁻¹' thirdSets Δ δ i) ⊆
      {p : Path2 | (∀ s ∈ Icc (0 : ℝ) 1, -Δ ≤ (p s).2 - (p 0).2) ∧ 1 ≤ (p 1).2 - (p 0).2 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, (p 1).1 - δ ≤ (p s).1) ∧ (p 1).1 - (p 0).1 ≤ -1} := by
  intro ω hω
  have h0 : thirdIncr 0 ω ∈ firstThirdSet Δ := mem_iInter₂.1 hω 0 (Finset.mem_univ _)
  have h1 : thirdIncr 1 ω ∈ middleThirdSet := mem_iInter₂.1 hω 1 (Finset.mem_univ _)
  have h2 : thirdIncr 2 ω ∈ lastThirdSet δ := mem_iInter₂.1 hω 2 (Finset.mem_univ _)
  have hc1 : Continuous fun s => (ω s).1 := continuous_fst.comp ω.continuous
  have hc2 : Continuous fun s => (ω s).2 := continuous_snd.comp ω.continuous
  have hR1 : ∀ s ∈ Icc (0 : ℝ) (1 / 3), -Δ ≤ (ω s).2 - (ω 0).2 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 0) (g := fun s => (ω s).2 - (ω (thirdL 0)).2)
      (hc2.sub continuous_const) (C := Ici (-Δ)) isClosed_Ici fun q => by
        have h := (h0.1 q).1
        rw [thirdIncr_snd] at h
        exact h
  have hL1 : ∀ s ∈ Icc (0 : ℝ) (1 / 3), |(ω s).1 - (ω 0).1| ≤ 5 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 0) (g := fun s => |(ω s).1 - (ω (thirdL 0)).1|)
      (continuous_abs.comp (hc1.sub continuous_const)) (C := Iic 5) isClosed_Iic fun q => by
        have h := (h0.1 q).2
        rw [thirdIncr_fst] at h
        exact h
  have hR1e : 1 ≤ (ω (1 / 3)).2 - (ω 0).2 := by
    have h := h0.2
    rw [thirdIncr_end_snd] at h
    exact h
  have hRm : ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), -(1 / 4) ≤ (ω s).2 - (ω (1 / 3)).2 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 1) (g := fun s => (ω s).2 - (ω (thirdL 1)).2)
      (hc2.sub continuous_const) (C := Ici (-(1 / 4))) isClosed_Ici fun q => by
        have h := (h1.1 q).1
        rw [thirdIncr_snd] at h
        exact h
  have hRme : 20 - 1 / 4 ≤ (ω (2 / 3)).2 - (ω (1 / 3)).2 := by
    have h := h1.2
    rw [thirdIncr_end_snd] at h
    exact h
  have hLm : ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3),
      |((ω s).1 - (ω (1 / 3)).1) + 90 * (s - 1 / 3)| ≤ 1 / 2 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 1)
      (g := fun s => |((ω s).1 - (ω (thirdL 1)).1) + 90 * (s - thirdL 1)|)
      (continuous_abs.comp ((hc1.sub continuous_const).add
        (continuous_const.mul (continuous_id.sub continuous_const))))
      (C := Iic (1 / 2)) isClosed_Iic fun q => by
        have h := (h1.1 q).2
        rw [thirdIncr_fst] at h
        exact h
  have hL3 : ∀ s ∈ Icc (2 / 3 : ℝ) 1, -δ ≤ (ω s).1 - (ω 1).1 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 2) (g := fun s => (ω s).1 - (ω (thirdR 2)).1)
      (hc1.sub continuous_const) (C := Ici (-δ)) isClosed_Ici fun q => by
        have h := (h2.1 q).1
        rw [thirdIncr_end_fst, thirdIncr_fst, sub_sub_sub_cancel_right] at h
        exact h
  have hR3 : ∀ s ∈ Icc (2 / 3 : ℝ) 1, |(ω s).2 - (ω 1).2| ≤ 5 :=
    forall_Icc_of_forall_rat (thirdL_le_thirdR 2) (g := fun s => |(ω s).2 - (ω (thirdR 2)).2|)
      (continuous_abs.comp (hc2.sub continuous_const)) (C := Iic 5) isClosed_Iic fun q => by
        have h := (h2.1 q).2
        rw [thirdIncr_end_snd, thirdIncr_snd, sub_sub_sub_cancel_right] at h
        exact h
  have hL3e : 1 ≤ (ω (2 / 3)).1 - (ω 1).1 := by
    have h := h2.2
    rw [thirdIncr_end_fst, neg_sub] at h
    exact h
  exact lemmaTwo_deterministic (L := fun t => (ω t).1) (R := fun t => (ω t).2) hΔ hδ hR1 hL1 hR1e
    hRm hRme hLm hL3 hR3 hL3e

/-! ### Shimura's Lemma 2 -/

/-- **Shimura's Lemma 2 for one law of the pair** (answer §1): the product of the bounds on the three
independent thirds gives `G(Δ, δ) ≥ c Δ δ` for `0 < Δ, δ ≤ 1`. -/
theorem lemmaTwo_of_law (hK : KilledBarrierPositive) (hT : PlanarTubePositive) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ Δ δ : ℝ, 0 < Δ → Δ ≤ 1 → 0 < δ → δ ≤ 1 →
      ENNReal.ofReal (c * Δ * δ) ≤
        μ {p | (∀ s ∈ Icc (0 : ℝ) 1, -Δ ≤ (p s).2 - (p 0).2) ∧ 1 ≤ (p 1).2 - (p 0).2 ∧
          (∀ s ∈ Icc (0 : ℝ) 1, (p 1).1 - δ ≤ (p s).1) ∧ (p 1).1 - (p 0).1 ≤ -1} := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨c₁, hc₁, h₁⟩ := firstThird_event hK hγ0 hγ2 hμ
  obtain ⟨c₃, hc₃, h₃⟩ := lastThird_event hK hγ0 hγ2 hμ
  have h₂ := middleThird_event hT hγ0 hγ2 hμ
  set m := μ {ω : Path2 | (∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), -(1 / 4) ≤ (ω s).2 - (ω (1 / 3)).2) ∧
      20 - 1 / 4 ≤ (ω (2 / 3)).2 - (ω (1 / 3)).2 ∧
      ∀ s ∈ Icc (1 / 3 : ℝ) (2 / 3), |((ω s).1 - (ω (1 / 3)).1) + 90 * (s - 1 / 3)| ≤ 1 / 2}
    with hm
  have hm0 : 0 < m.toReal := ENNReal.toReal_pos h₂.ne' (measure_ne_top μ _)
  refine ⟨c₁ * c₃ * m.toReal, mul_pos (mul_pos hc₁ hc₃) hm0, fun Δ δ hΔ hΔ1 hδ hδ1 => ?_⟩
  have hind := (iIndepFun_thirdIncr hμ).measure_inter_preimage_eq_mul Finset.univ
    (sets := thirdSets Δ δ) fun i _ => by
      fin_cases i
      exacts [measurableSet_firstThirdSet Δ, measurableSet_middleThirdSet,
        measurableSet_lastThirdSet δ]
  rw [Fin.prod_univ_three] at hind
  have e : c₁ * c₃ * m.toReal * Δ * δ = c₁ * Δ * m.toReal * (c₃ * δ) := by ring
  rw [e, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc₁.le hΔ.le) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (mul_nonneg hc₁.le hΔ.le), ENNReal.ofReal_toReal (measure_ne_top μ _)]
  calc ENNReal.ofReal (c₁ * Δ) * m * ENNReal.ofReal (c₃ * δ)
      ≤ μ (thirdIncr 0 ⁻¹' thirdSets Δ δ 0) * μ (thirdIncr 1 ⁻¹' thirdSets Δ δ 1) *
          μ (thirdIncr 2 ⁻¹' thirdSets Δ δ 2) :=
        mul_le_mul' (mul_le_mul' ((h₁ Δ hΔ hΔ1).trans (measure_mono (firstThird_subset Δ)))
          (measure_mono middleThird_subset))
          ((h₃ δ hδ hδ1).trans (measure_mono (lastThird_subset δ)))
    _ = μ (⋂ i ∈ (Finset.univ : Finset (Fin 3)), thirdIncr i ⁻¹' thirdSets Δ δ i) := hind.symm
    _ ≤ _ := measure_mono (inter_thirds_subset hΔ hδ)

/-- **Shimura's Lemma 2 for every angle** (M. Shimura, Kodai Math. J. 11 (1988), Lemma 2, (3.5),
p. 172; written answer §1, which covers also the obtuse angles `π/2 < θ ≤ π` omitted in print): for
`0 < γ < 2`, from the killed kernel bound and tube positivity, `G(Δ, δ) ≥ c Δ δ` with one constant for
every law of the pair, since that law is unique (`isCorrelatedBM2_unique_holds`). -/
theorem shimuraLemmaTwo_of_barriers {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : KilledBarrierPositive) (hT : PlanarTubePositive) : ShimuraLemmaTwo γ := by
  unfold ShimuraLemmaTwo
  by_cases hex : ∃ μ : Measure Path2, IsCorrelatedBM2 γ μ
  · obtain ⟨μ₀, hμ₀⟩ := hex
    obtain ⟨c, hc, h⟩ := lemmaTwo_of_law hK hT hγ0 hγ2 hμ₀
    refine ⟨c, hc, fun μ hμ Δ δ hΔ hΔ1 hδ hδ1 => ?_⟩
    rw [MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ μ μ₀ hμ hμ₀]
    exact h Δ δ hΔ hΔ1 hδ hδ1
  · exact ⟨1, one_pos, fun μ hμ => absurd ⟨μ, hμ⟩ hex⟩

end MatedCRT.PeanosphereTriplePoints
