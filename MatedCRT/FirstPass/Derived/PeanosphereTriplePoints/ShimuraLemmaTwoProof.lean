import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import LatticeProb.Prob.CorrelatedBMConeTimes
import LatticeProb.Prob.CorrelatedBMWindowIndependence
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Prob.BrownianDriftSmallBall

/-!
# Shimura's Lemma 2 from the barrier statements

This file assembles the ingredients of `ShimuraLemmaTwo γ` for the correlated Brownian pair `(L, R)`.

* `indepFun_coneComb_future_swap`: the increments of `R` and the increments of the whitened coordinate
  `(L - ρ R) / σ` after any base time are independent Brownian motions (the exchange of the roles of
  `L` and `R` in `LatticeProb.CorrelatedBM.whitened_coneComb_brownian_independent`).
* `windowSet`: the measurable set of paths whose values at the dyadic times up to `T` stay in an open
  interval; for continuous paths it lies in the closed version of the barrier event, and it contains
  the barrier event itself.
* `measure_inter_ge_of_indep`: a product lower bound for the probability that two independent
  continuous processes satisfy their barrier events.
* `barrierPair_lower_bound`: from `KilledBarrierPositive`, two independent Brownian motions with
  continuous paths satisfy, one in a barrier window `(-e, H)` ending in `(y₁, y₂)` and the other in the
  window `(-1, 2)`, with probability at least `c e`.
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
probability at least `c e` for `0 < e ≤ 1`. -/
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

/-- For `0 < γ < 2` the correlation `-cos (π γ² / 4)` lies strictly between `-1` and `1`. -/
theorem lrCov_mem_Ioo {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    -1 < lrCov γ 0 1 ∧ lrCov γ 0 1 < 1 := by
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by
    have := mul_pos Real.pi_pos (pow_pos hγ0 2)
    linarith
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have hcos1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at h
  have hcosm1 : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rwa [Real.cos_pi] at h
  have hρ : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  rw [hρ]
  constructor <;> linarith

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
coordinate `R` stays above `-Δ` on `[0, 1/3]` and ends above `1`, while `L` moves by at most `5`. -/
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

end MatedCRT.PeanosphereTriplePoints
