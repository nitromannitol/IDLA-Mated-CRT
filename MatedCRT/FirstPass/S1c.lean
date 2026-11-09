import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.FirstPass.Frozen.S1c

/-!
# First pass: `ScaledClusterExitTimeStep` (eq:btb-converge-to-inf, line 3330) by the route of fleet note G-hT (q4)

The target `ScaledClusterExitTimeStep` (Steps/Sec1/Convergence.lean:92) asserts `P[b T^b ≤ t] → 0` for
`T^b = sup {s > 0 : R_b⁻¹ Λ_{bs} ⊆ B_{ρ/3}}`. The printed equality-in-law argument is replaced (notes/fp-gaps/G-hT.md)
by three lemmas, all formalized here except the first:
* `clusterExitTime_rescaled_gt` (Lemma A, deterministic): if `Λ_{2t} ⊆ B_{Rρ/3}` then `t < b T^b`.
* `coneScaleRadius_lowerTail` (Lemma B): `P[R_b ≤ A] → 0` as `b → ∞`, from the frozen radial divergence
  `FrozenConeRadialDivergence` (Frozen/S1c.lean) and the crossing lemma `le_of_sSup_le_crossing`.
* `FixedTimeRadiusStep` (Lemma 1, NEW, NOT yet formalized): a measurable `M_u` with `Λ_u ⊆ B̄_{M_u}` almost surely.
The assembly `scaledClusterExitTimeStep_of_radius` proves `ScaledClusterExitTimeStep` from `FixedTimeRadiusStep`,
so `ScaledClusterExitTimeStep` is NOT proved until `FixedTimeRadiusStep` is.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set HarmonicBalls MarkovProcess Metric
open scoped NNReal ENNReal

/-- NEW step (fleet note G-hT, Lemma 1: measurable radius at one fixed time). For every `u > 0` there is a measurable
`M : Ω → ℝ` with `Λ_u ⊆ B̄_{M}` almost surely, for the harmonic-ball family of the cone field. The written argument
(analytic projections of the obstacle problem, Borel decoding of the LQG measure, rational points of the open set
`int cl K_{R,u}`) is not yet formalized. -/
def FixedTimeRadiusStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω)) →
    ∀ u : ℝ, 0 < u → ∃ M : Ω → ℝ, Measurable M ∧ ∀ᵐ ω ∂P, Λ ω u ⊆ closedBall 0 (M ω)

/-! ### Lemma A: a deterministic exit-time bound (G-hT, proof of the target, eqs. (8)-(9)) -/

/-- A locally finite measure on `ℂ` gives finite mass to every ball: the closed ball is compact and is covered by finitely
many neighbourhoods of finite mass (the bridge `IsLocallyFiniteMeasure → IsFiniteMeasureOnCompacts` is not an instance
in this Mathlib). -/
theorem measure_ball_lt_top_of_locallyFinite (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (r : ℝ) :
    μ (ball 0 r) < ⊤ := by
  have hloc : ∀ x : ℂ, ∃ U ∈ 𝓝 x, μ U < ⊤ := fun x => Measure.finiteAt_nhds μ x
  choose U hU hμU using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) r).elim_nhds_subcover U (fun x _ => hU x)
  calc μ (ball 0 r) ≤ μ (⋃ x ∈ t, U x) := measure_mono ((ball_subset_closedBall).trans ht)
    _ ≤ ∑ x ∈ t, μ (U x) := measure_biUnion_finset_le t U
    _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => hμU x

/-- If the harmonic-ball family at time `2t` lies in `B_{Rρ/3}`, then the rescaled cluster exit time exceeds `t / b`,
that is `t < b T`. The supremum is the real `sSup` of `clusterExitTime`; the set is bounded above by the mass
`μ(Λ_{bs}) = bs` and local finiteness. -/
theorem clusterExitTime_rescaled_gt (μ : Measure ℂ) (hfin : ∀ r : ℝ, μ (ball 0 r) < ⊤)
    (Λ : ℝ → Set ℂ) (hmeas : ∀ s : ℝ, 0 < s → μ (Λ s) = ENNReal.ofReal s)
    {b t ρ R : ℝ} (hb : 0 < b) (ht : 0 < t) (hR : 0 < R)
    (hL : Λ (2 * t) ⊆ ball 0 (R * ρ / 3)) :
    t < b * clusterExitTime (rescaledFamily Λ R b) ρ := by
  have hbt : b * (2 * t / b) = 2 * t := by field_simp
  have h2t : 0 < 2 * t / b := by positivity
  -- a point of the rescaled set at `s` lies in `B_{ρ/3}` only if its image lies in `B_{Rρ/3}`
  have hscale : ∀ s : ℝ, 0 < s → rescaledFamily Λ R b s ⊆ ball 0 (ρ / 3) →
      Λ (b * s) ⊆ ball 0 (R * ρ / 3) := by
    intro s _ hs y hy
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hyR : y / (R : ℂ) ∈ rescaledFamily Λ R b s := by
      show (R : ℂ) * (y / (R : ℂ)) ∈ Λ (b * s)
      have : (R : ℂ) * (y / (R : ℂ)) = y := by field_simp
      rw [this]
      exact hy
    have h1 := hs hyR
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      div_lt_iff₀ hR] at h1
    rw [mem_ball_zero_iff]
    linarith
  have hmem : 2 * t / b ∈ {s : ℝ | 0 < s ∧ rescaledFamily Λ R b s ⊆ ball 0 (ρ / 3)} := by
    refine ⟨h2t, fun x hx => ?_⟩
    have hx' : (R : ℂ) * x ∈ Λ (2 * t) := by
      have hx0 : (R : ℂ) * x ∈ Λ (b * (2 * t / b)) := hx
      rwa [hbt] at hx0
    have h1 := hL hx'
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le] at h1
    rw [mem_ball_zero_iff]
    have h2 : R * ‖x‖ < R * (ρ / 3) := by linarith
    exact lt_of_mul_lt_mul_left h2 hR.le
  have hbdd : BddAbove {s : ℝ | 0 < s ∧ rescaledFamily Λ R b s ⊆ ball 0 (ρ / 3)} := by
    refine ⟨(μ (ball 0 (R * ρ / 3))).toReal / b, fun s hs => ?_⟩
    obtain ⟨hs0, hs⟩ := hs
    have h1 : μ (Λ (b * s)) ≤ μ (ball 0 (R * ρ / 3)) := measure_mono (hscale s hs0 hs)
    rw [hmeas (b * s) (mul_pos hb hs0)] at h1
    have h2 : b * s ≤ (μ (ball 0 (R * ρ / 3))).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin _).ne).1 h1
    rw [le_div_iff₀ hb]
    linarith
  have hle : 2 * t / b ≤ sSup {s : ℝ | 0 < s ∧ rescaledFamily Λ R b s ⊆ ball 0 (ρ / 3)} :=
    le_csSup hbdd hmem
  have hmul := mul_le_mul_of_nonneg_left hle hb.le
  rw [hbt] at hmul
  show t < b * sSup {s : ℝ | 0 < s ∧ rescaledFamily Λ R b s ⊆ ball 0 (ρ / 3)}
  linarith

/-! ### Lemma B, pointwise part: the crossing lemma for the cone scale radius -/

/-- If the supremum of the level set `{r > 0 : c r + Q log r = L}` is at most `A > 0`, then `L` is at most the value
of `c(e^s) + Q s` at `s = log A + 1`. This uses the a.s. divergence of `s ↦ c(e^s) + Q s` (no crossing above `log A`
forces the path to lie below the level, which the divergence excludes) and the intermediate value theorem. -/
theorem le_of_sSup_le_crossing (c : ℝ → ℝ) (hc : ContinuousOn c (Ioi 0)) (Q L A : ℝ) (hA : 0 < A)
    (hdiv : Tendsto (fun s : ℝ => c (Real.exp s) + Q * s) atTop atTop)
    (hsup : sSup {r : ℝ | 0 < r ∧ c r + Q * Real.log r = L} ≤ A) :
    L ≤ c (Real.exp (Real.log A + 1)) + Q * (Real.log A + 1) := by
  have hcont : Continuous (fun s : ℝ => c (Real.exp s) + Q * s) :=
    (hc.comp_continuous Real.continuous_exp (fun s => Real.exp_pos s)).add
      (continuous_const.mul continuous_id)
  obtain ⟨s0, hs0⟩ := eventually_atTop.1 (hdiv.eventually_gt_atTop L)
  have hval : ∀ r : ℝ, 0 < r → c (Real.exp (Real.log r)) + Q * Real.log r = c r + Q * Real.log r := by
    intro r hr
    rw [Real.exp_log hr]
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ c r + Q * Real.log r = L} := by
    refine ⟨Real.exp s0, fun r hr => ?_⟩
    obtain ⟨hr0, hreq⟩ := hr
    have hlt : Real.log r < s0 := by
      by_contra hcon
      rw [not_lt] at hcon
      have h1 := hs0 _ hcon
      rw [hval r hr0, hreq] at h1
      exact lt_irrefl _ h1
    exact ((Real.log_lt_iff_lt_exp hr0).1 hlt).le
  by_contra hneg
  rw [not_le] at hneg
  have hs1 : Real.log A + 1 ≤ max s0 (Real.log A + 1) := le_max_right _ _
  have hL1 : L < c (Real.exp (max s0 (Real.log A + 1))) + Q * max s0 (Real.log A + 1) :=
    hs0 _ (le_max_left _ _)
  obtain ⟨s2, hs2, hs2eq⟩ := intermediate_value_Icc hs1 hcont.continuousOn ⟨hneg.le, hL1.le⟩
  have hmem : Real.exp s2 ∈ {r : ℝ | 0 < r ∧ c r + Q * Real.log r = L} := by
    refine ⟨Real.exp_pos s2, ?_⟩
    rw [Real.log_exp]
    exact hs2eq
  have h1 : Real.exp s2 ≤ A := le_trans (le_csSup hbdd hmem) hsup
  have h2 : Real.exp (Real.log A + 1) ≤ Real.exp s2 := Real.exp_le_exp.2 hs2.1
  have h3 : Real.exp (Real.log A + 1) = A * Real.exp 1 := by
    rw [Real.exp_add, Real.exp_log hA]
  have h4 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  nlinarith

/-! ### Tail and monotonicity facts -/

/-- A real random variable `X` on a finite measure space: `P[L < X] → 0` as `L → ∞`. -/
theorem tendsto_measure_lt_atTop {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) :
    Tendsto (fun L : ℝ => P {ω | L < X ω}) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < X ω}) atTop (𝓝 0) := by
    have hm : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℝ) < X ω} P := fun n =>
      (measurableSet_lt measurable_const hX).nullMeasurableSet
    have hanti : Antitone (fun n : ℕ => {ω | (n : ℝ) < X ω}) := by
      intro m n hmn ω hω
      exact lt_of_le_of_lt (Nat.cast_le.2 hmn) (show (n : ℝ) < X ω from hω)
    have hinter : (⋂ n : ℕ, {ω | (n : ℝ) < X ω}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge (X ω)
      exact ⟨n, hn⟩
    have key := tendsto_measure_iInter_atTop (μ := P) (fun n => hm n) hanti ⟨0, measure_ne_top P _⟩
    rw [hinter, measure_empty] at key
    exact key
  have hfl : Tendsto (fun L : ℝ => P {ω | ((⌊L⌋₊ : ℕ) : ℝ) < X ω}) atTop (𝓝 0) :=
    hnat.comp tendsto_nat_floor_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfl ?_ ?_
  · exact Eventually.of_forall fun L => zero_le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    apply measure_mono
    intro ω hω
    exact lt_of_le_of_lt (Nat.floor_le hL) hω

/-- A function with limit `+∞` along the real half-line from a limit along `ℝ≥0`. -/
theorem tendsto_atTop_real_of_nnreal {G : ℝ → ℝ}
    (h : Tendsto (fun σ : ℝ≥0 => G (σ : ℝ)) atTop atTop) : Tendsto G atTop atTop := by
  rw [tendsto_atTop_atTop] at h ⊢
  intro b
  obtain ⟨σ0, hσ0⟩ := h b
  refine ⟨(σ0 : ℝ), fun s hs => ?_⟩
  have hs0 : 0 ≤ s := le_trans σ0.2 hs
  have hσle : σ0 ≤ s.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]
    exact hs
  have h1 := hσ0 _ hσle
  rwa [Real.coe_toNNReal _ hs0] at h1

/-! ### Lemma B: lower tail of the cone scale radius -/

/-- **Lower tail of the cone scale radius** (G-hT, Lemma 2; eq. (7)): for `A > 0`, `P[R_b ≤ A] → 0` as `b → ∞`.
Proof: if `R_b ≤ A` on the a.s. event where the radial path diverges and is continuous, then `γ⁻¹ log b ≤
c(e^{log A + 1}) + Q (log A + 1)` (crossing lemma), and the right-hand side is a real random variable. -/
theorem coneScaleRadius_lowerTail {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hfield : IsConeField γ P hC hcirc μ)
    (hdiv : FrozenConeRadialDivergence) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun b : ℝ => P {ω | coneScaleRadius γ (hcirc ω) b ≤ A}) atTop (𝓝 0) := by
  obtain ⟨hP, hq, -⟩ := hfield
  have := hP
  obtain ⟨ν, hν, hlaw⟩ := hq.radial_law
  have hmeasR : Measurable (fun ω => radialProcess (hcirc ω)) := by
    show Measurable fun ω => ((fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0),
      (fun s : ℝ≥0 => hcirc ω (Real.exp (s : ℝ)) 0))
    refine Measurable.prodMk ?_ ?_
    · exact Measurable.of_eval (fun t => hq.measurable_circle _ 0 (Real.exp_pos _))
    · exact Measurable.of_eval (fun s => hq.measurable_circle _ 0 (Real.exp_pos _))
  -- (i) almost surely the radial path diverges: transfer the frozen law through `P.map radialProcess`
  have hae : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) atTop atTop := by
    have h1 := hdiv γ hγ hγ2 ν hν
    rw [← hlaw] at h1
    have h2 := ae_of_ae_map hmeasR.aemeasurable h1
    filter_upwards [h2] with ω hω
    exact tendsto_atTop_real_of_nnreal hω
  -- (ii) almost surely the circle averages at the origin are continuous in the radius
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) := by
    filter_upwards [hq.ae_continuousOn_circle] with ω hω
    exact hω.comp (continuousOn_id.prodMk (continuousOn_const (c := (0 : ℂ))))
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hgood := hae.and hcont
  have hzero := ae_iff.1 hgood
  set X : Ω → ℝ := fun ω => hcirc ω (Real.exp (Real.log A + 1)) 0 + lqgQ γ * (Real.log A + 1) with hXdef
  have hXm : Measurable X := (hq.measurable_circle _ 0 (Real.exp_pos _)).add_const _
  -- (iii) pointwise: `R_b ≤ A` on the good event forces `γ⁻¹ log b - 1 < X`
  have hbound : ∀ b : ℝ, P {ω | coneScaleRadius γ (hcirc ω) b ≤ A} ≤
      P {ω | γ⁻¹ * Real.log b + -1 < X ω} +
        P {ω | ¬ ((Tendsto (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) atTop atTop) ∧
          ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0))} := by
    intro b
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases hg : (Tendsto (fun s : ℝ => hcirc ω (Real.exp s) 0 + lqgQ γ * s) atTop atTop) ∧
        ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0)
    · left
      have hle := le_of_sSup_le_crossing (fun r => hcirc ω r 0) hg.2 (lqgQ γ) (γ⁻¹ * Real.log b) A hA
        hg.1 hω
      show γ⁻¹ * Real.log b + -1 < X ω
      simp only [hXdef]
      linarith
    · right
      exact hg
  -- (iv) the tail of the real variable `X` along `γ⁻¹ log b - 1 → ∞`
  have htail : Tendsto (fun b : ℝ => P {ω | γ⁻¹ * Real.log b + -1 < X ω}) atTop (𝓝 0) := by
    have hlin : Tendsto (fun b : ℝ => γ⁻¹ * Real.log b + -1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop (inv_pos.2 hγ) Real.tendsto_log_atTop)
    exact (tendsto_measure_lt_atTop P hXm).comp hlin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail ?_ ?_
  · exact Eventually.of_forall fun b => zero_le
  · exact Eventually.of_forall fun b => by
      have h := hbound b
      rwa [hzero, add_zero] at h

/-! ### Assembly: `ScaledClusterExitTimeStep` from Lemmas A, B and the NEW Lemma 1 -/

/-- **eq:btb-converge-to-inf** (`ScaledClusterExitTimeStep`), conditional on `FixedTimeRadiusStep` (Lemma 1 of G-hT,
NOT yet formalized). For fixed `t > 0`: `{b T^b ≤ t} ⊆ {Λ_{2t} ⊄ B̄_{M}} ∪ {M > n} ∪ {R_b ≤ 3n/ρ}` up to an
a.s. null set (Lemma A with `M ≤ n` and `R_b > 3n/ρ`), so `P[b T^b ≤ t] ≤ P[M > n] + P[R_b ≤ 3n/ρ]`; choose `n`,
then `b`. -/
theorem scaledClusterExitTimeStep_of_radius (hdiv : FrozenConeRadialDivergence) (hR : FixedTimeRadiusStep) :
    ScaledClusterExitTimeStep := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ P hC hcirc μ hfield Λ hΛ t ht
  have := hfield.1
  obtain ⟨M, hMm, hMΛ⟩ := hR γ hγ hγ2 Ω P hC hcirc μ hfield Λ hΛ (2 * t) (by positivity)
  have hLQG : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hfield.2.2
  have hfin : ∀ᵐ ω ∂P, ∀ r : ℝ, μ ω (ball 0 r) < ⊤ := by
    filter_upwards [hLQG] with ω hω
    intro r
    have := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top_of_locallyFinite (μ ω) r
  have hsc : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s :=
    hΛ.mono fun ω hω s hs => hω.2.1.measure_eq s hs
  have hgood : ∀ᵐ ω ∂P, (∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s) ∧
      (∀ r : ℝ, μ ω (ball 0 r) < ⊤) ∧ Λ ω (2 * t) ⊆ closedBall 0 (M ω) :=
    hsc.and (hfin.and hMΛ)
  have hbad0 := ae_iff.1 hgood
  have hMtail : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < M ω}) atTop (𝓝 0) :=
    (tendsto_measure_lt_atTop P hMm).comp tendsto_natCast_atTop_atTop
  -- pointwise inclusion (Lemma A)
  have hsub : ∀ b : ℝ, 0 < b → ∀ n : ℕ, 1 ≤ n →
      {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t} ⊆
        ({ω | ¬ ((∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s) ∧
            (∀ r : ℝ, μ ω (ball 0 r) < ⊤) ∧ Λ ω (2 * t) ⊆ closedBall 0 (M ω))} ∪
          {ω | (n : ℝ) < M ω}) ∪
          {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} := by
    intro b hb n hn ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_lt, not_le] at hcon
    obtain ⟨⟨⟨hs1, hs2, hs3⟩, hMn⟩, hRn⟩ := hcon
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hRpos : 0 < coneScaleRadius γ (hcirc ω) b := by
      have : 0 < 3 * (n : ℝ) / ρ := div_pos (mul_pos (by norm_num) hn0) hρ
      linarith
    have hL : Λ ω (2 * t) ⊆ ball 0 (coneScaleRadius γ (hcirc ω) b * ρ / 3) := by
      intro y hy
      have h1 := hs3 hy
      rw [mem_closedBall_zero_iff] at h1
      rw [mem_ball_zero_iff]
      have h3 : (n : ℝ) < coneScaleRadius γ (hcirc ω) b * ρ / 3 := by
        rw [div_lt_iff₀ hρ] at hRn
        linarith
      linarith
    have key := clusterExitTime_rescaled_gt (μ ω) hs2 (Λ ω) hs1 hb ht hRpos hL
    have hω' : b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t := hω
    linarith
  have hbd : ∀ b : ℝ, 0 < b → ∀ n : ℕ, 1 ≤ n →
      P {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t} ≤
        P {ω | (n : ℝ) < M ω} + P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} := by
    intro b hb n hn
    calc P {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t}
        ≤ P (({ω | ¬ ((∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s) ∧
            (∀ r : ℝ, μ ω (ball 0 r) < ⊤) ∧ Λ ω (2 * t) ⊆ closedBall 0 (M ω))} ∪
          {ω | (n : ℝ) < M ω}) ∪
          {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ}) := measure_mono (hsub b hb n hn)
      _ ≤ P (({ω | ¬ ((∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s) ∧
            (∀ r : ℝ, μ ω (ball 0 r) < ⊤) ∧ Λ ω (2 * t) ⊆ closedBall 0 (M ω))} ∪
          {ω | (n : ℝ) < M ω})) + P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} :=
            measure_union_le _ _
      _ ≤ (P {ω | ¬ ((∀ s : ℝ, 0 < s → μ ω (Λ ω s) = ENNReal.ofReal s) ∧
            (∀ r : ℝ, μ ω (ball 0 r) < ⊤) ∧ Λ ω (2 * t) ⊆ closedBall 0 (M ω))} +
          P {ω | (n : ℝ) < M ω}) + P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} :=
            add_le_add (measure_union_le _ _) le_rfl
      _ = P {ω | (n : ℝ) < M ω} + P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} := by
            rw [hbad0, zero_add, add_comm]
  -- the limit
  refine ENNReal.tendsto_nhds_zero.2 (fun ε hε => ?_)
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  have hMev : ∀ᶠ n : ℕ in atTop, P {ω | (n : ℝ) < M ω} ≤ ε / 2 :=
    hMtail.eventually (ge_mem_nhds hε2)
  obtain ⟨n, hn1, hn2⟩ := (hMev.and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hRev : ∀ᶠ b in atTop, P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} ≤ ε / 2 :=
    (coneScaleRadius_lowerTail hγ hγ2 hfield hdiv (div_pos (mul_pos (by norm_num) hn0) hρ)).eventually
      (ge_mem_nhds hε2)
  filter_upwards [hRev, eventually_gt_atTop 0] with b hRb hb
  calc _ ≤ P {ω | (n : ℝ) < M ω} + P {ω | coneScaleRadius γ (hcirc ω) b ≤ 3 * (n : ℝ) / ρ} :=
        hbd b hb n hn2
    _ ≤ ε / 2 + ε / 2 := add_le_add hn1 hRb
    _ = ε := ENNReal.add_halves ε

end MatedCRT
