import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaledVolumeGrowth

/-!
# Measurability of the volume-growth event of measures (q2, task fp-S4S6c, cone-scaling repair)

For each radius `R`, the set `{ν : Measure ℂ | ∃ βminus βplus, VolumeGrowth ν R βminus βplus}` is measurable for the
σ-algebra of `Measure ℂ`. The proof is a countable reduction: radii are rational, centres run over a countable dense
set `D ⊆ ℂ`, exponents are rational and the threshold is `1/(n+1)`. Only the monotonicity `ball z r ⊆ ball w q` of open
balls is used, so no continuity of `ν` on balls is needed.

`ae_mem_of_map_eq` is the law transfer used by the cone-scaling repair: if `μ` and `F` have the same law, almost sure
membership of `μ ω` in a measurable set `E` of measures gives almost sure membership of `F ω`.
-/

namespace MatedCRT

open MeasureTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

/-- Countable form of `VolumeGrowth` on the scales `0 < r < 1/(n+1)`: rational exponents `a, b`, centres `w` in a set
`D ⊆ ℂ` and rational radii `q`. -/
def VolumeGrowthCountable (D : Set ℂ) (R : ℝ) (a b : ℚ) (n : ℕ) (ν : Measure ℂ) : Prop :=
  0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
    ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / ((n : ℝ) + 1) →
      ∀ w : D, (w : ℂ) ∈ ball (0 : ℂ) R →
        ENNReal.ofReal ((q : ℝ) ^ (a : ℝ)) ≤ ν (ball (w : ℂ) (q : ℝ)) ∧
          ν (ball (w : ℂ) (q : ℝ)) ≤ ENNReal.ofReal ((q : ℝ) ^ (b : ℝ))

/-- A point of a dense set `D`, lying in `ball 0 R`, within `δ` of a point `z ∈ ball 0 R`. -/
theorem exists_grid_near {D : Set ℂ} (hD : Dense D) {R : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {δ : ℝ}
    (hδ : 0 < δ) : ∃ w ∈ D, w ∈ ball (0 : ℂ) R ∧ dist w z < δ := by
  have hU : IsOpen (ball z δ ∩ ball (0 : ℂ) R) := isOpen_ball.inter isOpen_ball
  have hne : (ball z δ ∩ ball (0 : ℂ) R).Nonempty := ⟨z, mem_ball_self hδ, hz⟩
  obtain ⟨w, hwD, hwU⟩ := hD.exists_mem_open hU hne
  exact ⟨w, hwD, hwU.2, mem_ball.1 hwU.1⟩

/-- Lower bound of the countable form at every real scale and every centre of `ball 0 R`. -/
theorem volumeGrowthCountable_lower {D : Set ℂ} (hD : Dense D) {R : ℝ} {a b : ℚ} {n : ℕ} {ν : Measure ℂ}
    (h : VolumeGrowthCountable D R a b n ν) {r : ℝ} (hr : 0 < r) (hrr : r < 1 / ((n : ℝ) + 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    ENNReal.ofReal (r ^ (a : ℝ)) ≤ ν (ball z r) := by
  obtain ⟨ha, -, hG⟩ := h
  have key : ∀ δ : ℝ, 0 < δ → δ < r / 2 →
      ENNReal.ofReal ((r - 2 * δ) ^ (a : ℝ)) ≤ ν (ball z r) := by
    intro δ hδ hδr
    obtain ⟨w, hwD, hwR, hwd⟩ := exists_grid_near hD hz hδ
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r - 2 * δ < r - δ by linarith)
    have hq0 : 0 < (q : ℝ) := by linarith
    have hqlt : (q : ℝ) < 1 / ((n : ℝ) + 1) := by linarith
    have hbound := (hG q hq0 hqlt ⟨w, hwD⟩ hwR).1
    have hsub : ball w (q : ℝ) ⊆ ball z r := by
      intro x hx
      rw [mem_ball] at hx ⊢
      have htri := dist_triangle x w z
      linarith
    have hmono : ν (ball w (q : ℝ)) ≤ ν (ball z r) := measure_mono hsub
    have hpow : (r - 2 * δ) ^ (a : ℝ) ≤ (q : ℝ) ^ (a : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) ha.le
    exact (ENNReal.ofReal_le_ofReal hpow).trans (hbound.trans hmono)
  have hcont : Tendsto (fun δ : ℝ => ENNReal.ofReal ((r - 2 * δ) ^ (a : ℝ))) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (r ^ (a : ℝ)))) := by
    have h1 : ContinuousAt (fun δ : ℝ => (r - 2 * δ) ^ (a : ℝ)) 0 := by
      apply ContinuousAt.rpow_const
      · fun_prop
      · left
        norm_num
        exact hr.ne'
    have h2 : ContinuousAt (fun δ : ℝ => ENNReal.ofReal ((r - 2 * δ) ^ (a : ℝ))) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    have h3 := h2.tendsto
    simp only [mul_zero, sub_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((r - 2 * δ) ^ (a : ℝ)) ≤ ν (ball z r) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 2 by positivity)] with δ hδ
    exact key δ hδ.1 hδ.2
  exact le_of_tendsto hcont hev

/-- Upper bound of the countable form at every real scale and every centre of `ball 0 R`. -/
theorem volumeGrowthCountable_upper {D : Set ℂ} (hD : Dense D) {R : ℝ} {a b : ℚ} {n : ℕ} {ν : Measure ℂ}
    (h : VolumeGrowthCountable D R a b n ν) {r : ℝ} (hr : 0 < r) (hrr : r < 1 / ((n : ℝ) + 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    ν (ball z r) ≤ ENNReal.ofReal (r ^ (b : ℝ)) := by
  obtain ⟨-, hb, hG⟩ := h
  have key : ∀ δ : ℝ, 0 < δ → δ < (1 / ((n : ℝ) + 1) - r) / 2 →
      ν (ball z r) ≤ ENNReal.ofReal ((r + 2 * δ) ^ (b : ℝ)) := by
    intro δ hδ hδr
    obtain ⟨w, hwD, hwR, hwd⟩ := exists_grid_near hD hz hδ
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r + δ < r + 2 * δ by linarith)
    have hq0 : 0 < (q : ℝ) := by linarith
    have hqlt : (q : ℝ) < 1 / ((n : ℝ) + 1) := by linarith
    have hbound := (hG q hq0 hqlt ⟨w, hwD⟩ hwR).2
    have hzw : dist z w < δ := by rw [dist_comm]; exact hwd
    have hsub : ball z r ⊆ ball w (q : ℝ) := by
      intro x hx
      rw [mem_ball] at hx ⊢
      have htri := dist_triangle x z w
      linarith
    have hmono : ν (ball z r) ≤ ν (ball w (q : ℝ)) := measure_mono hsub
    have hpow : (q : ℝ) ^ (b : ℝ) ≤ (r + 2 * δ) ^ (b : ℝ) :=
      Real.rpow_le_rpow hq0.le hq2.le hb.le
    exact hmono.trans (hbound.trans (ENNReal.ofReal_le_ofReal hpow))
  have hcont : Tendsto (fun δ : ℝ => ENNReal.ofReal ((r + 2 * δ) ^ (b : ℝ))) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (r ^ (b : ℝ)))) := by
    have h1 : ContinuousAt (fun δ : ℝ => (r + 2 * δ) ^ (b : ℝ)) 0 := by
      apply ContinuousAt.rpow_const
      · fun_prop
      · left
        norm_num
        exact hr.ne'
    have h2 : ContinuousAt (fun δ : ℝ => ENNReal.ofReal ((r + 2 * δ) ^ (b : ℝ))) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    have h3 := h2.tendsto
    simp only [mul_zero, add_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ν (ball z r) ≤ ENNReal.ofReal ((r + 2 * δ) ^ (b : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (1 / ((n : ℝ) + 1) - r) / 2 by linarith)] with δ hδ
    exact key δ hδ.1 hδ.2
  exact ge_of_tendsto hcont hev

/-- The countable form implies `VolumeGrowth` (with `r₀ = 1/(n+1)`). -/
theorem volumeGrowth_of_countable {D : Set ℂ} (hD : Dense D) {R : ℝ} {a b : ℚ} {n : ℕ} {ν : Measure ℂ}
    (h : VolumeGrowthCountable D R a b n ν) : VolumeGrowth ν R (a : ℝ) (b : ℝ) :=
  ⟨h.1, h.2.1, 1 / ((n : ℝ) + 1), by positivity, fun r hr hrr z hz =>
    ⟨volumeGrowthCountable_lower hD h hr hrr hz, volumeGrowthCountable_upper hD h hr hrr hz⟩⟩

/-- `VolumeGrowth` implies the countable form, with rational exponents `a ≥ βminus`, `0 < b ≤ βplus`. -/
theorem countable_of_volumeGrowth {D : Set ℂ} {R βm βp : ℝ} {ν : Measure ℂ}
    (h : VolumeGrowth ν R βm βp) : ∃ (a b : ℚ) (n : ℕ), VolumeGrowthCountable D R a b n ν := by
  obtain ⟨-, hβp, r₀, hr₀, hV⟩ := h
  obtain ⟨a, ha⟩ := exists_rat_gt (max βm 0)
  obtain ⟨b, hb0, hbβ⟩ := exists_rat_btwn hβp
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < min r₀ 1 by positivity)
  have hr₀' : 1 / ((n : ℝ) + 1) < r₀ := lt_of_lt_of_le hn (min_le_left _ _)
  have hr1 : 1 / ((n : ℝ) + 1) < 1 := lt_of_lt_of_le hn (min_le_right _ _)
  have ha0 : 0 < (a : ℝ) := lt_of_le_of_lt (le_max_right _ _) ha
  refine ⟨a, b, n, ha0, hb0, fun q hq0 hqlt w hw => ?_⟩
  have hqr₀ : (q : ℝ) < r₀ := lt_trans hqlt hr₀'
  have hq1 : (q : ℝ) ≤ 1 := (hqlt.trans hr1).le
  obtain ⟨h1, h2⟩ := hV q hq0 hqr₀ w hw
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) h1
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (le_trans (le_max_left _ _) (le_of_lt ha))
  · refine le_trans h2 (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hbβ.le

/-- **The volume-growth event of measures is measurable.** For each radius `R`, the set of finite measures on `ℂ`
satisfying `VolumeGrowth ν R βminus βplus` for some exponents is measurable. -/
theorem measurableSet_volumeGrowth_exists (R : ℝ) :
    MeasurableSet {ν : Measure ℂ | ∃ βm βp : ℝ, VolumeGrowth ν R βm βp} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable D := hDc.to_subtype
  have hEq : {ν : Measure ℂ | ∃ βm βp : ℝ, VolumeGrowth ν R βm βp} =
      ⋃ (a : ℚ) (b : ℚ) (n : ℕ), {ν : Measure ℂ | VolumeGrowthCountable D R a b n ν} := by
    ext ν
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨βm, βp, h⟩
      exact countable_of_volumeGrowth h
    · rintro ⟨a, b, n, h'⟩
      exact ⟨(a : ℝ), (b : ℝ), volumeGrowth_of_countable hDd h'⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun n => ?_
  refine measurableSet_setOfPred.2 ?_
  unfold VolumeGrowthCountable
  refine Measurable.and measurable_const (Measurable.and measurable_const ?_)
  refine Measurable.forall fun q => ?_
  refine measurable_const.imp (measurable_const.imp ?_)
  refine Measurable.forall fun w => ?_
  refine measurable_const.imp ?_
  refine Measurable.and ?_ ?_
  · exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const (Measure.measurable_coe measurableSet_ball))
  · exact measurableSet_setOfPred.1
      (measurableSet_le (Measure.measurable_coe measurableSet_ball) measurable_const)

/-- **Law transfer of an almost sure event of measures.** If `μ` and `F` are random measures with the same law and
`E` is a measurable set of measures, then `μ ω ∈ E` almost surely implies `F ω ∈ E` almost surely. -/
theorem ae_mem_of_law_map_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ F : Ω → Measure ℂ}
    (hμ : AEMeasurable μ P) (hF : AEMeasurable F P) (hlaw : Measure.map F P = Measure.map μ P)
    {E : Set (Measure ℂ)} (hE : MeasurableSet E) (h : ∀ᵐ ω ∂P, μ ω ∈ E) :
    ∀ᵐ ω ∂P, F ω ∈ E := by
  have hE' : MeasurableSet {x : Measure ℂ | x ∈ E} := hE
  have h1 : ∀ᵐ x ∂(Measure.map μ P), x ∈ E := (ae_map_iff hμ hE').2 h
  rw [← hlaw] at h1
  exact (ae_map_iff hF hE').1 h1

end MatedCRT
