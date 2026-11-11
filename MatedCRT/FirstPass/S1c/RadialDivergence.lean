import MatedCRT.FirstPass.Frozen.S1cDivergence

/-!
# First pass: transfer of the radial divergence to the cone

The corrected radial input `FrozenConeRadialDivergenceCorrected` (Frozen/S1cDivergence.lean) is a statement on the
continuous-path carrier of `ν`. The cone argument needs real-time divergence of the radial path `s ↦ h_{e^s}(0)` for almost
every outcome `ω`. We transfer it through the raw law `quantumConeRadialLaw γ ν` using the event of divergence along the
rationals `RatDivergence` (countable operations on coordinates, hence measurable in the raw product space), and then pass from
the rationals to the reals by continuity of the circle averages (`ContinuousOn` on `(0, ∞)`, almost surely;
`IsQuantumCone.ae_continuousOn_circle`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- Divergence to `+∞` along the rationals, in countable form: for every `n : ℕ` there is `N : ℕ` with `n ≤ g q` for every
rational `q ≥ N`. -/
def RatDivergence (g : ℚ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ q : ℚ, (N : ℚ) ≤ q → (n : ℝ) ≤ g q

/-- Divergence along the rationals is a measurable event when the coordinates are measurable (countable intersections and
unions). -/
lemma measurableSet_ratDivergence {X : Type*} [MeasurableSpace X] (g : ℚ → X → ℝ) (hg : ∀ q, Measurable (g q)) :
    MeasurableSet {x : X | RatDivergence (fun q => g q x)} := by
  have hset : {x : X | RatDivergence (fun q => g q x)} =
      ⋂ n : ℕ, ⋃ N : ℕ, ⋂ q : ℚ, {x : X | (N : ℚ) ≤ q → (n : ℝ) ≤ g q x} := by
    ext x
    simp only [RatDivergence, Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q => ?_
  by_cases h : (N : ℚ) ≤ q
  · have hEq : {x : X | (N : ℚ) ≤ q → (n : ℝ) ≤ g q x} = {x : X | (n : ℝ) ≤ g q x} := by
      ext x
      simp [h]
    rw [hEq]
    exact measurableSet_le measurable_const (hg q)
  · have hEq : {x : X | (N : ℚ) ≤ q → (n : ℝ) ≤ g q x} = univ := by
      ext x
      simp [h]
    rw [hEq]
    exact MeasurableSet.univ

/-- Divergence along the rationals is unchanged by modifying the function at negative rationals (irrelevant for `q ≥ N`). -/
lemma ratDivergence_congr {f g : ℚ → ℝ} (h : RatDivergence f) (hfg : ∀ q : ℚ, (0 : ℚ) ≤ q → f q = g q) :
    RatDivergence g := by
  intro n
  obtain ⟨N, hN⟩ := h n
  refine ⟨N, fun q hq => ?_⟩
  have hq0 : (0 : ℚ) ≤ q := le_trans (Nat.cast_nonneg N) hq
  rw [← hfg q hq0]
  exact hN q hq

/-- A continuous real function which diverges along the rationals diverges along the reals. -/
lemma tendsto_atTop_of_ratDivergence {G : ℝ → ℝ} (hG : Continuous G) (h : RatDivergence (fun q : ℚ => G q)) :
    Tendsto G atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge b
  obtain ⟨N, hN⟩ := h n
  filter_upwards [eventually_ge_atTop (N : ℝ)] with s hs
  choose q hq using fun k : ℕ => exists_rat_btwn (lt_add_of_pos_right s (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity))
  have hup : Tendsto (fun k : ℕ => s + 1 / ((k : ℝ) + 1)) atTop (𝓝 s) := by
    simpa using (tendsto_const_nhds (x := s)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k : ℕ => (q k : ℝ)) atTop (𝓝 s) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => (hq k).1.le) (fun k => (hq k).2.le)
  have hGq : Tendsto (fun k : ℕ => G (q k : ℝ)) atTop (𝓝 (G s)) := (hG.tendsto s).comp hlim
  refine ge_of_tendsto hGq (Filter.Eventually.of_forall fun k => ?_)
  have hNq : (N : ℚ) ≤ q k := by
    have h' : (N : ℝ) ≤ (q k : ℝ) := hs.trans (hq k).1.le
    exact_mod_cast h'
  exact le_trans hn (hN (q k) hNq)

/-- A shifted path `w s + c s → ∞` (with `c = Q - γ`) gives divergence along the rationals of the second coordinate
`w s - γ s` of the raw cone law, plus `Q q`. -/
lemma ratDivergence_of_tendsto_shift (w : ℝ≥0 → ℝ) (γ Q : ℝ)
    (h : Tendsto (fun s : ℝ≥0 => w s + (Q - γ) * (s : ℝ)) atTop atTop) :
    RatDivergence (fun q : ℚ => (w (q : ℝ).toNNReal - γ * (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * q) := by
  intro n
  obtain ⟨S, hS⟩ := eventually_atTop.1 (h.eventually_ge_atTop (n : ℝ))
  obtain ⟨N, hSN⟩ := exists_nat_ge S
  refine ⟨N, fun q hq => ?_⟩
  have hq0' : (0 : ℚ) ≤ q := le_trans (Nat.cast_nonneg N) hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0'
  have hqq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
  have hNq : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hSN' : (S : ℝ) ≤ (N : ℝ) := by exact_mod_cast hSN
  have hSq : S ≤ (q : ℝ).toNNReal := by
    rw [← NNReal.coe_le_coe, hqq]
    exact hSN'.trans hNq
  have key := hS _ hSq
  rw [hqq] at key
  show (n : ℝ) ≤ (w (q : ℝ).toNNReal - γ * (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * q
  rw [hqq]
  linarith

/-- The circle-average radial divergence: a function `c` continuous on `(0, ∞)` whose composite with `exp` diverges along the
rationals after adding `Q s` diverges along the reals. -/
lemma tendsto_circle_of_ratDivergence {c : ℝ → ℝ} (hc : ContinuousOn c (Ioi 0)) (Q : ℝ)
    (h : RatDivergence (fun q : ℚ => c (Real.exp (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * q)) :
    Tendsto (fun s : ℝ => c (Real.exp s) + Q * s) atTop atTop := by
  have hG : Continuous (fun s : ℝ => c (Real.exp s) + Q * s) :=
    (hc.comp_continuous Real.continuous_exp (fun s => Real.exp_pos s)).add (continuous_const.mul continuous_id)
  refine tendsto_atTop_of_ratDivergence hG (ratDivergence_congr h fun q hq => ?_)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [Real.coe_toNNReal _ hq0]

/-- The event of divergence along the rationals of the second coordinate of the raw cone law. -/
lemma measurableSet_ratDivergence_second (γ : ℝ) :
    MeasurableSet {y : ℝ≥0 → ℝ | RatDivergence (fun q : ℚ => y (q : ℝ).toNNReal + lqgQ γ * q)} :=
  measurableSet_ratDivergence (fun (q : ℚ) (y : ℝ≥0 → ℝ) => y (q : ℝ).toNNReal + lqgQ γ * q)
    fun q => (measurable_pi_apply ((q : ℝ).toNNReal)).add_const _

/-- **Transfer to the raw cone law.** From the corrected radial divergence on the continuous-path carrier `ν`, the second
coordinate `x.2` of `quantumConeRadialLaw γ ν` (`s ↦ w_s - γ s`) has divergence along the rationals, almost surely. -/
lemma ae_ratDivergence_quantumConeRadialLaw {γ : ℝ} {ν : Measure (ContinuousPath ℝ)} [IsFiniteMeasure ν]
    (hν : ∀ᵐ w ∂ν, Tendsto (fun s : ℝ≥0 => w s + (lqgQ γ - γ) * (s : ℝ)) atTop atTop) :
    ∀ᵐ x ∂(quantumConeRadialLaw γ ν), RatDivergence (fun q : ℚ => x.2 (q : ℝ).toNNReal + lqgQ γ * q) := by
  have hψ : Measurable (fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * (s : ℝ)) :=
    Measurable.of_eval fun s =>
      ((continuous_eval_const s).measurable).sub_const (γ * (s : ℝ))
  have hEm := measurableSet_ratDivergence_second γ
  have h2 : ∀ᵐ y ∂(ν.map fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * (s : ℝ)),
      RatDivergence (fun q : ℚ => y (q : ℝ).toNNReal + lqgQ γ * q) := by
    rw [ae_map_iff hψ.aemeasurable hEm]
    filter_upwards [hν] with w hw
    exact ratDivergence_of_tendsto_shift w γ (lqgQ γ) hw
  have h3 : ∀ᵐ y ∂((((brownianMotion 0).map fun w (t : ℝ≥0) => w t + γ * t).prod
      (ν.map fun w (s : ℝ≥0) => w s - γ * s)).map Prod.snd),
      RatDivergence (fun q : ℚ => y (q : ℝ).toNNReal + lqgQ γ * q) := by
    rw [Measure.map_snd_prod]
    exact Measure.ae_smul_measure h2 _
  have h4 := (ae_map_iff measurable_snd.aemeasurable hEm).1 h3
  unfold quantumConeRadialLaw
  exact h4

end MatedCRT
