import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.External.QuantumCone

/-!
# The cone scale radius is an a.s. positive random variable (eq:cone-scale-radius, line 454)

For `b > 0`, `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` (`coneScaleRadius`). This file proves
`ConeScaleRadiusStep` (`R_b` is a.e.-measurable and a.s. positive) from `QuantumConeScalingInput` (DMS14
Proposition 4.13(i), eq:quantum-cone-scaling: the circle average process of `h^b = h(R_b ·) + Q log R_b - γ⁻¹ log b`
has the law of that of `h`).

* Positivity (`ae_coneScaleRadius_pos`). `R_b ≥ 0`, and `R_b = 0` exactly when the level set is empty or unbounded.
  On `{R_b = 0}` the circle average process of `h^b` is the constant `h_0(0) - γ⁻¹ log b` (`rescaledCircle_zero`), so
  it takes the same value at `(1, 0)` and `(e⁻¹, 0)`. By the scaling input the probability of this event is
  `P[h_1(0) = h_{e⁻¹}(0)]`, which is `0`: in the radial law of the quantum cone, `h_{e^{-t}}(0) = B_t + γ t` with `B`
  a standard Brownian motion, so `h_1(0) = B_0 = 0` a.s. and `h_{e⁻¹}(0) = B_1 + γ` has no atom
  (`ae_circle_one_eq_zero`, `measure_circle_exp_neg_one_eq`). Since `R_b > 0` a.s. is what makes the input
  meaningful (the field `h^b` of DMS14 is defined with the a.s. finite positive `R_b`), this is the intended reading
  of the input.
* The circle average process of `h^b` is a.e.-measurable (`aemeasurable_circleProcess_rescaledCircle`): in this
  Mathlib the image of a probability measure under a map which is not a.e.-measurable is a Dirac mass
  (`Measure.map_of_not_aemeasurable_of_ne_zero`), and the law of the circle average process of `h` is not one, since
  `h_{e⁻¹}(0)` has no atom.
* Measurability (`aemeasurable_coneScaleRadius`). Where `r ↦ X(r) = h_r(0) + Q log r` is continuous on `(0, ∞)` and
  `R_b > 0`, the level set is closed, nonempty and bounded, and `R_b < q` iff `|X - γ⁻¹ log b|` is bounded below on
  each `[q, M] ∩ ℚ` (`sSup_levelSet_lt_iff`): a countable condition on the measurable circle averages.

As by-products: worker c5's `ConeScaleRadiusPosStep` and `ConeRescaledCircleAEMeasurableStep` (hypotheses of
Lemma 2.5) follow from the same input.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace Sec1

/-! ## Deterministic facts -/

/-- `R_b ≥ 0`. -/
theorem coneScaleRadius_nonneg (γ : ℝ) (c : ℝ → ℂ → ℝ) (b : ℝ) : 0 ≤ coneScaleRadius γ c b :=
  Real.sSup_nonneg fun _ hr => hr.1.le

/-- With `R = 0` the rescaled circle average process is constant. -/
theorem rescaledCircle_zero (γ : ℝ) (c : ℝ → ℂ → ℝ) (b r : ℝ) (z : ℂ) :
    rescaledCircle γ c 0 b r z = c 0 0 - γ⁻¹ * Real.log b := by
  simp [rescaledCircle]

/-- If the last time at level `c` of a function continuous on `(0, ∞)` is positive, then the level set is bounded
above and its supremum is attained. -/
theorem sSup_levelSet_mem {X : ℝ → ℝ} {c : ℝ} (hX : ContinuousOn X (Ioi 0))
    (hpos : 0 < sSup {r | 0 < r ∧ X r = c}) :
    X (sSup {r | 0 < r ∧ X r = c}) = c ∧ BddAbove {r | 0 < r ∧ X r = c} := by
  set S := {r | 0 < r ∧ X r = c} with hS
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hpos
    exact lt_irrefl _ hpos
  have hbdd : BddAbove S := by
    by_contra h
    rw [Real.sSup_of_not_bddAbove h] at hpos
    exact lt_irrefl _ hpos
  refine ⟨?_, hbdd⟩
  have hcont : ContinuousWithinAt X S (sSup S) :=
    (hX.continuousAt (Ioi_mem_nhds hpos)).continuousWithinAt
  have h1 := hcont.mem_closure_image (csSup_mem_closure hne hbdd)
  have h2 : X '' S ⊆ {c} := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr.2
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, mem_singleton_iff] at h3

/-- **The last level time as a countable condition.** If `X` is continuous on `(0, ∞)` and the last time `s` at
level `c` is positive, then for `q > 0`: `s < q` iff on each `[q, M]` the rational values of `|X - c|` are bounded
below by some `1 / (k + 1)`. -/
theorem sSup_levelSet_lt_iff {X : ℝ → ℝ} {c : ℝ} (hX : ContinuousOn X (Ioi 0))
    (hpos : 0 < sSup {r | 0 < r ∧ X r = c}) {q : ℝ} (hq : 0 < q) :
    sSup {r | 0 < r ∧ X r = c} < q ↔
      ∀ M : ℕ, ∃ k : ℕ, ∀ x : {x : ℚ // q ≤ (x : ℝ) ∧ (x : ℝ) ≤ M}, 1 / ((k : ℝ) + 1) ≤ |X x - c| := by
  obtain ⟨hXs, hbdd⟩ := sSup_levelSet_mem hX hpos
  set s := sSup {r | 0 < r ∧ X r = c} with hs_def
  constructor
  · intro hsq M
    rcases lt_or_ge (M : ℝ) q with hM | hM
    · exact ⟨0, fun x => absurd (x.2.1.trans x.2.2) (not_le.2 hM)⟩
    · have hcont : ContinuousOn (fun r => |X r - c|) (Icc q M) :=
        ((hX.mono fun r hr => lt_of_lt_of_le hq hr.1).sub continuousOn_const).abs
      obtain ⟨r0, hr0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hM) hcont
      have hm : 0 < |X r0 - c| := by
        rw [abs_pos, sub_ne_zero]
        intro h
        have : r0 ≤ s := le_csSup hbdd ⟨lt_of_lt_of_le hq hr0.1, h⟩
        linarith [hr0.1]
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hm
      exact ⟨k, fun x => hk.le.trans (isMinOn_iff.1 hmin x ⟨x.2.1, x.2.2⟩)⟩
  · intro h
    by_contra hqs
    rw [not_lt] at hqs
    obtain ⟨k, hk⟩ := h (⌈s⌉₊ + 1)
    have hcont : ContinuousAt X s := hX.continuousAt (Ioi_mem_nhds hpos)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδX⟩ := hcont (1 / ((k : ℝ) + 1)) (by positivity)
    have hmin : 0 < min δ 1 := lt_min hδ one_pos
    obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn (show s < s + min δ 1 by linarith)
    have hxM : (x : ℝ) ≤ ((⌈s⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil s, min_le_right δ 1]
    have h1 := hk ⟨x, hqs.trans hx1.le, hxM⟩
    have h2 := hδX (show dist (x : ℝ) s < δ by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left δ 1])
    rw [Real.dist_eq, hXs] at h2
    simp only at h1
    linarith

/-! ## Measure-theoretic facts -/

/-- The circle average process of a quantum cone is measurable. -/
theorem measurable_circleProcess_of_isQuantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => circleProcess (hcirc ω) :=
  measurable_pi_iff.2 fun p => hcone.measurable_circle p.1 p.2 p.1.2

/-- Standard Brownian motion starts at `0`. -/
theorem brownianMotion_ae_eval_zero : ∀ᵐ w ∂(MarkovProcess.brownianMotion 0), w 0 = 0 := by
  have hm0 : Measurable fun w : MarkovProcess.ContinuousPath ℝ => w 0 :=
    MarkovProcess.ContinuousPath.measurable_coordinateProcess 0
  refine ae_of_ae_map hm0.aemeasurable (p := fun y : ℝ => y = 0) ?_
  rw [MarkovProcess.brownianMotion_map_eval, gaussianReal_zero_var, ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

/-- `B_1 ~ N(0, 1)` has no atom. -/
theorem brownianMotion_ae_eval_one_ne (a : ℝ) : ∀ᵐ w ∂(MarkovProcess.brownianMotion 0), w 1 ≠ a := by
  have hm1 : Measurable fun w : MarkovProcess.ContinuousPath ℝ => w 1 :=
    MarkovProcess.ContinuousPath.measurable_coordinateProcess 1
  refine ae_of_ae_map hm1.aemeasurable (p := fun y : ℝ => y ≠ a) ?_
  rw [MarkovProcess.brownianMotion_map_eval]
  exact ae_iff.2 (measure_mono_null (fun y hy => mem_singleton_iff.2 (not_not.1 hy))
    (gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton))

/-- **Null events of the radial part.** For the quantum cone, `t ↦ h_{e^{-t}}(0)` has the law of `B_t + γ t` with `B`
a standard Brownian motion, so an event of this path which is null for `B_· + γ ·` is `P`-null. -/
theorem measure_radial_null {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc)
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S)
    (h : MarkovProcess.brownianMotion 0
      ((fun (w : MarkovProcess.ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ)) ⁻¹' S) = 0) :
    P {ω | (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) ∈ S} = 0 := by
  obtain ⟨ν, hν, hlaw⟩ := hcone.radial_law
  have : IsProbabilityMeasure ν := hν.1
  have hrad : Measurable fun ω => radialProcess (hcirc ω) :=
    (measurable_pi_iff.2 fun t => hcone.measurable_circle _ 0 (Real.exp_pos _)).prodMk
      (measurable_pi_iff.2 fun s => hcone.measurable_circle _ 0 (Real.exp_pos _))
  have hset : {ω | (fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0) ∈ S} =
      (fun ω => radialProcess (hcirc ω)) ⁻¹' (S ×ˢ univ) := by
    ext ω
    exact ⟨fun h => ⟨h, mem_univ _⟩, fun h => h.1⟩
  have hφ : Measurable fun (w : MarkovProcess.ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ) :=
    measurable_pi_iff.2 fun t => (MarkovProcess.ContinuousPath.measurable_coordinateProcess t).add_const _
  rw [hset, ← Measure.map_apply hrad (hS.prod MeasurableSet.univ), hlaw, quantumConeRadialLaw,
    Measure.prod_prod, Measure.map_apply hφ hS, h, zero_mul]

/-- `h_1(0) = 0` a.s. for the quantum cone (circle average embedding). -/
theorem ae_circle_one_eq_zero {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 := by
  have hS : MeasurableSet {u : ℝ≥0 → ℝ | u 0 = 0}ᶜ :=
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).compl
  have h := measure_radial_null hcone hS (by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [brownianMotion_ae_eval_zero] with w hw0 hw
    apply hw
    show w 0 + γ * ((0 : ℝ≥0) : ℝ) = 0
    simp [hw0])
  rw [ae_iff]
  simpa using h

/-- `h_{e⁻¹}(0) = B_1 + γ` has no atom. -/
theorem measure_circle_exp_neg_one_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) (a : ℝ) :
    P {ω | hcirc ω (Real.exp (-1)) 0 = a} = 0 := by
  have hS : MeasurableSet {u : ℝ≥0 → ℝ | u 1 = a} := measurableSet_eq_fun (measurable_pi_apply 1) measurable_const
  have h := measure_radial_null hcone hS (by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [brownianMotion_ae_eval_one_ne (a - γ)] with w hw1 hw
    apply hw1
    have h2 : w 1 + γ * ((1 : ℝ≥0) : ℝ) = a := hw
    simp only [NNReal.coe_one, mul_one] at h2
    linarith)
  simpa using h

/-- **The circle average process of `h^b` is a.e.-measurable**: by `QuantumConeScalingInput` its image measure is the
law of the circle average process of `h`, which is not a Dirac mass (`h_{e⁻¹}(0)` has no atom), whereas the image of a
probability measure under a map which is not a.e.-measurable is one. -/
theorem aemeasurable_circleProcess_rescaledCircle (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ} (hb : 0 < b) :
    AEMeasurable (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) P := by
  have hlaw := hscale γ hγ hγ2 Ω P hC hcirc inferInstance hcone b hb
  have hG := measurable_circleProcess_of_isQuantumCone hcone
  by_contra hf
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hf (IsProbabilityMeasure.ne_zero P)] at hlaw
  obtain ⟨p0, hp0⟩ : ∃ p0 : Ioi (0 : ℝ) × ℂ → ℝ,
      Measure.dirac p0 = P.map fun ω => circleProcess (hcirc ω) := ⟨_, hlaw⟩
  let e1 : Ioi (0 : ℝ) := ⟨Real.exp (-1), mem_Ioi.2 (Real.exp_pos _)⟩
  have hE : MeasurableSet {p : Ioi (0 : ℝ) × ℂ → ℝ | p (e1, 0) = p0 (e1, 0)} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have h1 := congrArg (fun m : Measure (Ioi (0 : ℝ) × ℂ → ℝ) => m {p | p (e1, 0) = p0 (e1, 0)}) hp0
  rw [Measure.dirac_apply_of_mem (show p0 ∈ {p : Ioi (0 : ℝ) × ℂ → ℝ | p (e1, 0) = p0 (e1, 0)} from rfl),
    Measure.map_apply hG hE] at h1
  exact one_ne_zero (h1.trans (measure_circle_exp_neg_one_eq hcone (p0 (e1, 0))))

/-! ## The cone scale radius -/

/-- **`R_b > 0` almost surely**, from the scaling of the quantum cone (DMS14 Proposition 4.13(i)). -/
theorem ae_coneScaleRadius_pos (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := by
  have hlaw := hscale γ hγ hγ2 Ω P hC hcirc inferInstance hcone b hb
  have hG := measurable_circleProcess_of_isQuantumCone hcone
  have hF := aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone hb
  let one : Ioi (0 : ℝ) := ⟨1, mem_Ioi.2 one_pos⟩
  let e1 : Ioi (0 : ℝ) := ⟨Real.exp (-1), mem_Ioi.2 (Real.exp_pos _)⟩
  let E : Set (Ioi (0 : ℝ) × ℂ → ℝ) := {p | p (one, 0) = p (e1, 0)}
  have hE : MeasurableSet E := measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  have hsub : {ω | ¬ 0 < coneScaleRadius γ (hcirc ω) b} ⊆
      (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) ⁻¹' E := by
    intro ω hω
    have h0 : coneScaleRadius γ (hcirc ω) b = 0 :=
      le_antisymm (not_lt.1 hω) (coneScaleRadius_nonneg _ _ _)
    show circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) (one, 0) =
      circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) (e1, 0)
    simp only [circleProcess, h0, rescaledCircle_zero]
  rw [ae_iff]
  refine le_antisymm ((measure_mono hsub).trans_eq ?_) zero_le
  rw [← Measure.map_apply_of_aemeasurable hF hE, hlaw, Measure.map_apply hG hE]
  -- `{h_1(0) = h_{e⁻¹}(0)} ⊆ {h_1(0) ≠ 0} ∪ {h_{e⁻¹}(0) = 0}`
  refine measure_mono_null (fun ω hω => ?_)
    (measure_union_null (ae_iff.1 (ae_circle_one_eq_zero hcone)) (measure_circle_exp_neg_one_eq hcone 0))
  have hω' : hcirc ω 1 0 = hcirc ω (Real.exp (-1)) 0 := hω
  by_cases h1 : hcirc ω 1 0 = 0
  · exact Or.inr (hω'.symm.trans h1)
  · exact Or.inl h1

/-- **`R_b` is a.e.-measurable** where it is a.s. positive. -/
theorem aemeasurable_coneScaleRadius {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ}
    (hpos : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b) :
    AEMeasurable (fun ω => coneScaleRadius γ (hcirc ω) b) P := by
  classical
  let c : ℝ := γ⁻¹ * Real.log b
  let X : Ω → ℝ → ℝ := fun ω r => hcirc ω r 0 + lqgQ γ * Real.log r
  let Φ : ℚ → Ω → Prop := fun q ω =>
    ∀ M : ℕ, ∃ k : ℕ, ∀ x : {x : ℚ // (q : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ M}, 1 / ((k : ℝ) + 1) ≤ |X ω x - c|
  have hΦ : ∀ q : ℚ, 0 < (q : ℝ) → MeasurableSet {ω | Φ q ω} := by
    intro q hq
    simp only [Φ, Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun k => MeasurableSet.iInter fun x => ?_
    have hx : (0 : ℝ) < ((x : ℚ) : ℝ) := lt_of_lt_of_le hq x.2.1
    exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp (((hcone.measurable_circle _ 0 hx).add_const _).sub_const _))
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (X ω) (Ioi 0) ∧ 0 < coneScaleRadius γ (hcirc ω) b := by
    filter_upwards [hcone.ae_continuousOn_circle, hpos] with ω hω hR
    refine ⟨?_, hR⟩
    have h1 : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
      hω.comp (continuous_id.prodMk continuous_const).continuousOn fun r hr => ⟨hr, mem_univ _⟩
    exact h1.add (continuousOn_const.mul (Real.continuousOn_log.mono fun r hr => (mem_Ioi.1 hr).ne'))
  let N := toMeasurable P {ω | ¬ (ContinuousOn (X ω) (Ioi 0) ∧ 0 < coneScaleRadius γ (hcirc ω) b)}
  have hNmeas : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hgood
  have hgoodN : ∀ ω, ω ∉ N → ContinuousOn (X ω) (Ioi 0) ∧ 0 < coneScaleRadius γ (hcirc ω) b := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  let R' : Ω → ℝ := fun ω => if ω ∈ N then 0 else coneScaleRadius γ (hcirc ω) b
  refine ⟨R', measurable_of_Iio fun a => ?_, ?_⟩
  · have hset : R' ⁻¹' Iio a = (N ∩ {_ω | (0 : ℝ) < a}) ∪
        (Nᶜ ∩ ⋃ q : ℚ, {ω | 0 < (q : ℝ) ∧ (q : ℝ) < a ∧ Φ q ω}) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp [R', hω]
      · obtain ⟨hc, hR⟩ := hgoodN ω hω
        have hR' : R' ω = coneScaleRadius γ (hcirc ω) b := by simp only [R', hω, ↓reduceIte]
        simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_compl_iff, mem_iUnion, hR', hω,
          false_and, false_or, not_false_eq_true, true_and]
        constructor
        · intro h
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
          exact ⟨q, hR.trans hq1, hq2, (sSup_levelSet_lt_iff hc hR (hR.trans hq1)).1 hq1⟩
        · rintro ⟨q, hq0, hqa, hΦq⟩
          exact ((sSup_levelSet_lt_iff hc hR hq0).2 hΦq).trans hqa
    rw [hset]
    refine (hNmeas.inter (MeasurableSet.const _)).union (hNmeas.compl.inter (MeasurableSet.iUnion fun q => ?_))
    by_cases hq : (0 : ℝ) < q
    · simp only [Set.ofPred_and]
      exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (hΦ q hq))
    · simp [hq]
  · have hNc : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa using hN0)
    filter_upwards [hNc] with ω hω
    simp only [R', hω, ↓reduceIte]

end Sec1

/-- **`ConeScaleRadiusStep`** from the scaling of the quantum cone (`QuantumConeScalingInput`, DMS14 Prop 4.13(i)). -/
theorem coneScaleRadiusStep_of_input (hscale : QuantumConeScalingInput) : ConeScaleRadiusStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hfield b hb
  have := hfield.1
  have hpos := Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hfield.2.1 hb
  exact ⟨Sec1.aemeasurable_coneScaleRadius hfield.2.1 hpos, hpos⟩

/-- Worker c5's `ConeScaleRadiusPosStep` (a hypothesis of Lemma 2.5) from `QuantumConeScalingInput`. -/
theorem coneScaleRadiusPosStep_of_input (hscale : QuantumConeScalingInput) : ConeScaleRadiusPosStep :=
  fun γ hγ hγ2 _ _ _ _ _ hP hcone b hb => @Sec1.ae_coneScaleRadius_pos hscale γ hγ hγ2 _ _ _ hP _ _ hcone b hb

/-- Worker c5's `ConeRescaledCircleAEMeasurableStep` (a hypothesis of Lemma 2.5) from `QuantumConeScalingInput`: the
circle average process of `h^b` has the law of that of `h`, so it is a.e.-measurable. -/
theorem coneRescaledCircleAEMeasurableStep_of_input (hscale : QuantumConeScalingInput) :
    ConeRescaledCircleAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hfield b hb
  have := hfield.1
  exact Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hfield.2.1 hb

end MatedCRT
