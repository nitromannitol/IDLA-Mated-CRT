import Mathlib
import MatedCRT.Defs.Setting

/-!
# Appendix B, Theorem B.1: the occupation identity of the median-rescaled LBM (step S7)

Source: Bou-Rabee and Gwynne, arXiv:2211.04891, Appendix B. Printed statement `thm:occ-main`
(`paper/appendix-occupation-C16.tex:53-78`), proof `:429-470`; corrected draft `thm:main`
(`paper/idla_mated_crt-corrected.tex:4572`, Appendix B section near `:4531`).

This file proves the deterministic and measure-theoretic pieces of the proof of step S7 and
assembles them into the body of `FrozenLBMGreenOccupationRescaled`
(`MatedCRT/FirstPass/Frozen/S3S4b.lean:51-62`). The inputs of Tasks A-C (the potential bound, the
weight identity, the base identity, the identification `φ = Φ`, the weighted mean) and the cone
transfer step are explicit hypothesis binders of exact type.

Terminology: Liouville Brownian motion (Garban-Rhodes-Vargas), right-continuous inverse of a clock
(Berestycki 2015, eq. (2)), Stieltjes measure of a clock (Armitage-Gardiner), Green function of a
disk (Armitage-Gardiner, Ch. 4).
-/

namespace MatedCRT.KilledOccupation

open MeasureTheory Set Filter Topology Metric
open HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The right-continuous inverse of a clock -/

section Clock

variable {F : ℝ≥0 → ℝ}

lemma clockInverse_set_nonempty (ht : Tendsto F atTop atTop) (t : ℝ≥0) :
    {s : ℝ≥0 | (t : ℝ) < F s}.Nonempty :=
  (ht.eventually_gt_atTop (t : ℝ)).exists

lemma clockInverse_set_bddBelow (t : ℝ≥0) : BddBelow {s : ℝ≥0 | (t : ℝ) < F s} :=
  ⟨0, fun _ _ => zero_le⟩

/-- Galois connection of the right-continuous inverse of a continuous strictly increasing clock
tending to `∞`: `a < F⁻¹(t) ↔ F a < t` (Berestycki 2015, eq. (2)). -/
lemma lt_clockInverse_iff (hc : Continuous F) (hm : StrictMono F) (ht : Tendsto F atTop atTop)
    (a t : ℝ≥0) : a < clockInverse F t ↔ F a < t := by
  constructor
  · intro h
    have ha : a ∉ {s : ℝ≥0 | (t : ℝ) < F s} := fun hmem =>
      absurd (csInf_le (clockInverse_set_bddBelow t) hmem) (not_le.mpr h)
    have hle : F a ≤ t := not_lt.mp ha
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨u, hau, huG⟩ := exists_between h
      have hu : u ∈ {s : ℝ≥0 | (t : ℝ) < F s} := by
        show (t : ℝ) < F u
        rw [← heq]
        exact hm hau
      exact absurd (csInf_le (clockInverse_set_bddBelow t) hu) (not_le.mpr huG)
  · intro h
    have hev : ∀ᶠ u in 𝓝 a, F u < (t : ℝ) := (hc.tendsto a).eventually (gt_mem_nhds h)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hδ : (0 : ℝ≥0) < Real.toNNReal ε := Real.toNNReal_pos.mpr hε
    have hall : ∀ s ∈ {s : ℝ≥0 | (t : ℝ) < F s}, a + Real.toNNReal ε ≤ s := by
      intro s hs
      by_contra hlt
      rw [not_le] at hlt
      rcases le_or_gt s a with hsa | has
      · exact absurd hs (not_lt.mpr (le_of_lt (lt_of_le_of_lt (hm.monotone hsa) h)))
      · have hs' : (s : ℝ) < (a : ℝ) + ε := by
          have := NNReal.coe_lt_coe.mpr hlt
          rwa [NNReal.coe_add, Real.coe_toNNReal ε hε.le] at this
        have has' : (a : ℝ) < s := NNReal.coe_lt_coe.mpr has
        have hd : dist s a < ε := by
          rw [NNReal.dist_eq, abs_of_pos (by linarith)]
          linarith
        exact absurd (hball hd) (not_lt.mpr (le_of_lt hs))
    exact lt_of_lt_of_le (lt_add_of_pos_right a hδ)
      (le_csInf (clockInverse_set_nonempty ht t) hall)

/-- The right-continuous inverse of a clock is monotone in the time. -/
lemma clockInverse_monotone (ht : Tendsto F atTop atTop) :
    Monotone (fun t : ℝ≥0 => clockInverse F t) := by
  intro t t' htt'
  exact csInf_le_csInf (clockInverse_set_bddBelow t) (clockInverse_set_nonempty ht t')
    (fun s hs => lt_of_le_of_lt (NNReal.coe_le_coe.mpr htt') hs)

/-- The clock inverse at a time `u ∈ [0, F σ)` is strictly before `σ`. -/
lemma clockInverse_lt_of_lt (hc : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0)
    (ht : Tendsto F atTop atTop) {σ : ℝ≥0} {u : ℝ≥0} (hu : (u : ℝ) < F σ) :
    clockInverse F u < σ := by
  have hIVT := intermediate_value_Icc (by positivity : (0:ℝ≥0) ≤ σ) hc.continuousOn
  have hu' : (u : ℝ) ∈ Icc (F 0) (F σ) := ⟨by rw [h0]; exact NNReal.coe_nonneg u, hu.le⟩
  obtain ⟨a, ⟨ha0, haσ⟩, hFa⟩ := hIVT hu'
  have hne : a ≠ σ := by
    rintro rfl
    exact lt_irrefl _ (hFa ▸ hu)
  have haσ' : a < σ := lt_of_le_of_ne haσ hne
  have : clockInverse F u ≤ a := by
    rw [← not_lt, lt_clockInverse_iff hc hm ht]
    rw [hFa]
    exact lt_irrefl _
  exact lt_of_le_of_lt this haσ'

/-- At the clock value `F σ` the inverse is `σ`. -/
lemma clockInverse_clock (hc : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0)
    (ht : Tendsto F atTop atTop) (σ : ℝ≥0) : clockInverse F (Real.toNNReal (F σ)) = σ := by
  have hFσ : (((Real.toNNReal (F σ)) : ℝ≥0) : ℝ) = F σ := by
    apply Real.coe_toNNReal
    rw [← h0]
    exact hm.monotone (by positivity)
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    have h' := (lt_clockInverse_iff hc hm ht σ _).mp h
    rw [hFσ] at h'
    exact lt_irrefl _ h'
  · by_contra h
    rw [not_le] at h
    obtain ⟨a, hGa, haσ⟩ := exists_between h
    have hlt : a < clockInverse F (Real.toNNReal (F σ)) :=
      (lt_clockInverse_iff hc hm ht a _).mpr (by rw [hFσ]; exact hm haσ)
    exact lt_asymm hGa hlt

end Clock

/-! ## 2. The clock as a function of a real time, and its Stieltjes measure -/

section Real

variable {F : ℝ≥0 → ℝ}

/-- The clock as a function of a real time: `x ↦ F(x⁺)`. -/
def clockReal (F : ℝ≥0 → ℝ) (x : ℝ) : ℝ := F x.toNNReal

lemma clockReal_monotone (hm : Monotone F) : Monotone (clockReal F) :=
  fun _ _ h => hm (Real.toNNReal_le_toNNReal h)

lemma clockReal_continuous (hc : Continuous F) : Continuous (clockReal F) :=
  hc.comp continuous_real_toNNReal

lemma clockReal_coe (x : ℝ≥0) : clockReal F (x : ℝ) = F x := by
  simp [clockReal]

lemma clockReal_zero (h0 : F 0 = 0) : clockReal F 0 = 0 := by
  simp [clockReal, h0]

/-- Real form of the Galois connection: for `t > 0`, `a < F⁻¹(t) ↔ F(a⁺) < t`. -/
lemma real_lt_clockInverse_iff (hc : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0)
    (ht : Tendsto F atTop atTop) {t : ℝ} (ht0 : 0 < t) (a : ℝ) :
    a < ((clockInverse F t.toNNReal : ℝ≥0) : ℝ) ↔ clockReal F a < t := by
  have htc : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0.le
  rcases le_or_gt 0 a with ha | ha
  · have hac : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
    constructor
    · intro h
      have h1 : a.toNNReal < clockInverse F t.toNNReal := by
        rw [← NNReal.coe_lt_coe, hac]
        exact h
      have h2 := (lt_clockInverse_iff hc hm ht _ _).mp h1
      rw [htc] at h2
      exact h2
    · intro h
      have h1 : F a.toNNReal < ((t.toNNReal : ℝ≥0) : ℝ) := by
        rw [htc]
        exact h
      have h2 := NNReal.coe_lt_coe.mpr ((lt_clockInverse_iff hc hm ht _ _).mpr h1)
      rw [hac] at h2
      exact h2
  · have hzero : clockReal F a = 0 := by
      have ha0 : a.toNNReal = 0 := Real.toNNReal_of_nonpos ha.le
      simp [clockReal, ha0, h0]
    rw [hzero]
    constructor
    · intro _
      exact ht0
    · intro _
      exact lt_of_lt_of_le ha (NNReal.coe_nonneg _)

/-- The Stieltjes measure `dφ` of a continuous increasing clock `φ` on `ℝ`
(the Lebesgue-Stieltjes measure of `x ↦ φ(x⁺)`; Armitage-Gardiner, Ch. 1). -/
def clockMeasure (hm : Monotone F) : Measure ℝ :=
  (Monotone.stieltjesFunction (clockReal_monotone hm)).measure

lemma clockMeasure_Ioc (hm : Monotone F) (hc : Continuous F) (a b : ℝ) :
    clockMeasure hm (Ioc a b) = ENNReal.ofReal (clockReal F b - clockReal F a) := by
  unfold clockMeasure
  rw [StieltjesFunction.measure_Ioc]
  congr 2
  · exact rightLim_eq_of_tendsto ((clockReal_continuous hc).tendsto b |>.mono_left
      nhdsWithin_le_nhds)
  · exact rightLim_eq_of_tendsto ((clockReal_continuous hc).tendsto a |>.mono_left
      nhdsWithin_le_nhds)

/-- Change of variables for the Stieltjes measure of a clock: the Lebesgue integral of
`g ∘ F⁻¹` over `(0, F σ]` is the Stieltjes integral of `g` over `(0, σ]`
(the pathwise identity `∫_0^{τ} f(Y_t) dt = ∫_0^σ f(B_s) dφ(s)` of S7). -/
theorem integral_clockInverse_comp (hc : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0)
    (ht : Tendsto F atTop atTop) (σ : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ t in Ioc (0 : ℝ) (F σ), g ((clockInverse F t.toNNReal : ℝ≥0) : ℝ) =
      ∫ s in Ioc (0 : ℝ) (σ : ℝ), g s ∂(clockMeasure hm.monotone) := by
  have hGrmono : Monotone (fun t : ℝ => ((clockInverse F t.toNNReal : ℝ≥0) : ℝ)) := fun t t' htt' =>
    NNReal.coe_le_coe.mpr (clockInverse_monotone ht (Real.toNNReal_le_toNNReal htt'))
  have hGrmeas : Measurable (fun t : ℝ => ((clockInverse F t.toNNReal : ℝ≥0) : ℝ)) :=
    hGrmono.measurable
  have hmin : ∀ x y : ℝ, clockReal F (min x y) = min (clockReal F x) (clockReal F y) :=
    fun x y => (clockReal_monotone hm.monotone).map_min
  have hmax : ∀ x : ℝ, clockReal F (max x 0) = max (clockReal F x) 0 := fun x => by
    rw [(clockReal_monotone hm.monotone).map_max, clockReal_zero h0]
  have hGa : ∀ (a : ℝ) (t : ℝ), 0 < t →
      (a < ((clockInverse F t.toNNReal : ℝ≥0) : ℝ) ↔ clockReal F a < t) :=
    fun a t ht0 => real_lt_clockInverse_iff hc hm h0 ht ht0 a
  have hGb : ∀ (b : ℝ) (t : ℝ), 0 < t →
      (((clockInverse F t.toNNReal : ℝ≥0) : ℝ) ≤ b ↔ t ≤ clockReal F b) := fun b t ht0 => by
    rw [← not_lt, hGa b t ht0, not_lt]
  have hmap : (volume.restrict (Ioc (0 : ℝ) (F σ))).map
      (fun t : ℝ => ((clockInverse F t.toNNReal : ℝ≥0) : ℝ)) =
      (clockMeasure hm.monotone).restrict (Ioc (0 : ℝ) (σ : ℝ)) := by
    refine Measure.ext_of_Ioc_finite _ _ ?_ ?_
    · rw [Measure.map_apply hGrmeas MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ, Real.volume_Ioc, clockMeasure_Ioc hm.monotone hc,
        clockReal_coe, clockReal_zero h0]
    · intro a b hab
      rw [Measure.map_apply hGrmeas measurableSet_Ioc,
        Measure.restrict_apply (hGrmeas measurableSet_Ioc),
        Measure.restrict_apply measurableSet_Ioc]
      have hL : (fun t : ℝ => ((clockInverse F t.toNNReal : ℝ≥0) : ℝ)) ⁻¹' Ioc a b ∩ Ioc 0 (F σ) =
          Ioc (clockReal F a) (clockReal F b) ∩ Ioc 0 (F σ) := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          exact ⟨⟨(hGa a t h3).mp h1, (hGb b t h3).mp h2⟩, h3, h4⟩
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          exact ⟨⟨(hGa a t h3).mpr h1, (hGb b t h3).mpr h2⟩, h3, h4⟩
      rw [hL, Ioc_inter_Ioc, Real.volume_Ioc, Ioc_inter_Ioc, clockMeasure_Ioc hm.monotone hc]
      congr 1
      rw [hmin, hmax, clockReal_coe]
  calc ∫ t in Ioc (0 : ℝ) (F σ), g ((clockInverse F t.toNNReal : ℝ≥0) : ℝ)
      = ∫ s, g s ∂((volume.restrict (Ioc (0 : ℝ) (F σ))).map
          (fun t : ℝ => ((clockInverse F t.toNNReal : ℝ≥0) : ℝ))) :=
        (integral_map hGrmeas.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ s in Ioc (0 : ℝ) (σ : ℝ), g s ∂(clockMeasure hm.monotone) := by
        rw [hmap]

/-! ## 3. Scaling `s = m₀ t` and the exit time of the rescaled path -/

/-- Scaling of a Lebesgue integral over an interval: `∫_0^{T/m} h(m t) dt = m⁻¹ ∫_0^T h(s) ds`. -/
theorem integral_Ioc_comp_mul {m : ℝ} (hm : 0 < m) (h : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) (T / m), h (m * t) = m⁻¹ * ∫ s in Ioc (0 : ℝ) T, h s := by
  have h1 : ∫ t in Ioc (0 : ℝ) (T / m), h (m * t) = ∫ t in (0 : ℝ)..(T / m), h (m * t) :=
    (intervalIntegral.integral_of_le (div_nonneg hT hm.le)).symm
  have h2 : ∫ s in Ioc (0 : ℝ) T, h s = ∫ s in (0 : ℝ)..T, h s :=
    (intervalIntegral.integral_of_le hT).symm
  have hmT : m * (T / m) = T := by field_simp
  rw [h1, h2, intervalIntegral.integral_comp_mul_left h hm.ne', mul_zero, hmT, smul_eq_mul]

/-- The exit time of the rescaled path `t ↦ b(F⁻¹(c t))` from an open set `D`, when the path `b`
first leaves `D` at `σ` (`b s ∈ D` for `s < σ`, `b σ ∉ D`), is `F(σ) / c` (the time change of
Liouville Brownian motion; S7 uses it for `τ_D^X = φ(σ)/m₀`). -/
theorem pathExitTime_clockInverse_comp {D : Set ℂ} {b : ℝ≥0 → ℂ} {σ c : ℝ≥0} (hc0 : 0 < c)
    (hF : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0) (ht : Tendsto F atTop atTop)
    (hin : ∀ s < σ, b s ∈ D) (hout : b σ ∉ D) :
    pathExitTime D (fun t : ℝ≥0 => b (clockInverse F (c * t))) =
      ENNReal.ofReal (F σ / c) := by
  have hFσ0 : 0 ≤ F σ := by
    rw [← h0]
    exact hm.monotone (by positivity)
  have hc' : (c : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hc0).ne'
  set T : ℝ≥0 := (F σ / c).toNNReal with hT
  have hcT : c * T = (F σ).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mul, hT, Real.coe_toNNReal _ (div_nonneg hFσ0 (NNReal.coe_nonneg c)),
      Real.coe_toNNReal _ hFσ0]
    field_simp
  have hGσ : clockInverse F (c * T) = σ := by
    rw [hcT]
    exact clockInverse_clock hF hm h0 ht σ
  have hinT : ∀ t : ℝ≥0, t < T → b (clockInverse F (c * t)) ∈ D := by
    intro t htT
    apply hin
    apply clockInverse_lt_of_lt hF hm h0 ht
    rw [NNReal.coe_mul]
    calc (c : ℝ) * (t : ℝ) < (c : ℝ) * (T : ℝ) :=
          mul_lt_mul_of_pos_left (NNReal.coe_lt_coe.mpr htT) (NNReal.coe_pos.mpr hc0)
      _ = F σ := by
          rw [← NNReal.coe_mul, hcT, Real.coe_toNNReal _ hFσ0]
  have houtT : b (clockInverse F (c * T)) ∉ D := by
    rw [hGσ]
    exact hout
  unfold pathExitTime
  apply le_antisymm
  · exact sInf_le ⟨T, rfl, houtT⟩
  · apply le_sInf
    rintro s ⟨t, rfl, hts⟩
    apply ENNReal.coe_le_coe.mpr
    by_contra hlt
    rw [not_le] at hlt
    exact hts (hinT t hlt)


/-- Pathwise identity of S7 (`paper/appendix-occupation-C16.tex:441-449` with the scaling of `:459-461`).
For a path `b` that first leaves `D` at `σ` and the clock `F` of `b`, with `c > 0`,
`∫_{(0, F σ / c]} f(b(F⁻¹(c t))) dt = c⁻¹ ∫_{(0,σ]} f(b_s) dφ(s)`, where `dφ` is the Stieltjes measure of `F`.
The rescaled occupation of the LBM path `t ↦ b(F⁻¹(c t))` up to its exit from `D` is the left side. -/
theorem integral_rescaled_eq_stieltjes {b : ℝ≥0 → ℂ} {σ c : ℝ≥0} (hc0 : 0 < c)
    (hF : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0) (ht : Tendsto F atTop atTop)
    (f : ℂ → ℝ)
    (hfm : Measurable (fun x : ℝ => f (b x.toNNReal))) :
    ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (c * t.toNNReal))) =
      (c : ℝ)⁻¹ * ∫ s in Ioc (0 : ℝ) (σ : ℝ), f (b s.toNNReal) ∂(clockMeasure hm.monotone) := by
  have hFσ0 : 0 ≤ F σ := by
    rw [← h0]
    exact hm.monotone (by positivity)
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.mpr hc0
  have step1 : ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (c * t.toNNReal))) =
      ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (Real.toNNReal ((c : ℝ) * t)))) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [Real.toNNReal_mul hc'.le, Real.toNNReal_coe]
  have step2 : ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (Real.toNNReal ((c : ℝ) * t)))) =
      (c : ℝ)⁻¹ * ∫ s in Ioc (0 : ℝ) (F σ), f (b (clockInverse F s.toNNReal)) :=
    integral_Ioc_comp_mul hc' (fun s : ℝ => f (b (clockInverse F s.toNNReal))) hFσ0
  have step4 : ∫ t in Ioc (0 : ℝ) (F σ), f (b (clockInverse F t.toNNReal)) =
      ∫ s in Ioc (0 : ℝ) (σ : ℝ), f (b s.toNNReal) ∂(clockMeasure hm.monotone) := by
    have := integral_clockInverse_comp hF hm h0 ht σ (fun x : ℝ => f (b x.toNNReal)) hfm
    simp only [Real.toNNReal_coe] at this
    exact this
  rw [step1, step2, step4]

end Real

/-! ## 4. Weighted clocks: the Stieltjes measure of `φ = Φ` on `(0, σ]` (S7, `:430-441`) -/

section Weighted

/-- The weighted mass `W(x) = ∫⁻_{(0,x]} g dA` of a density `g` against a measure `dA` on `ℝ`
(the weighted clock `Φ(s) = ∫_0^s |B_u|^{-γ²} dA(u)` of `eq:occ-weightedclock`, in `ℝ≥0∞`). -/
def weightMass (dA : Measure ℝ) (g : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioc 0 x, g u ∂dA

lemma weightMass_add {dA : Measure ℝ} {g : ℝ → ℝ≥0∞} {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    weightMass dA g v = weightMass dA g u + ∫⁻ x in Ioc u v, g x ∂dA := by
  unfold weightMass
  rw [← Set.Ioc_union_Ioc_eq_Ioc hu huv, lintegral_union measurableSet_Ioc
    (Set.disjoint_left.mpr fun x hx1 hx2 => lt_irrefl x (lt_of_le_of_lt hx1.2 hx2.1))]

lemma clockReal_eq_weightMass {F : ℝ≥0 → ℝ} {dA : Measure ℝ} {g : ℝ → ℝ≥0∞} {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (weightMass dA g s).toReal) {x : ℝ} (hx0 : 0 ≤ x)
    (hxσ : x ≤ σ) : clockReal F x = (weightMass dA g x).toReal := by
  unfold clockReal
  have h1 := hF x.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hxσ)
  have h2 : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx0
  rw [h1, h2]

/-- The Stieltjes measure of a clock which is a weighted integral `φ(s) = ∫_{(0,s]} g dA` for
`s ≤ σ` agrees with the measure `g dA` on `(0, σ]` (identification `φ = Φ` of S7, followed by
`dφ = |B|^{-γ²} dA`). Proof: both measures give `(u, v] ∩ (0, σ]` the same mass, by the additivity of
`W`; the total masses agree at `σ`. -/
theorem clockMeasure_restrict_eq_withDensity {F : ℝ≥0 → ℝ} (hm : Monotone F) (hc : Continuous F)
    (h0 : F 0 = 0) (dA : Measure ℝ) (g : ℝ → ℝ≥0∞) {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (weightMass dA g s).toReal)
    (hfin : weightMass dA g σ ≠ ⊤) :
    (clockMeasure hm).restrict (Ioc (0 : ℝ) (σ : ℝ)) =
      (dA.withDensity g).restrict (Ioc (0 : ℝ) (σ : ℝ)) := by
  have hW : ∀ x : ℝ, 0 ≤ x → x ≤ σ → clockReal F x = (weightMass dA g x).toReal :=
    fun x hx0 hxσ => clockReal_eq_weightMass hF hx0 hxσ
  have hfin' : ∀ x : ℝ, 0 ≤ x → x ≤ σ → weightMass dA g x ≠ ⊤ := by
    intro x hx0 hxσ hx
    apply hfin
    rw [weightMass_add hx0 hxσ, hx, top_add]
  have : IsFiniteMeasure ((clockMeasure hm).restrict (Ioc (0 : ℝ) (σ : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ, clockMeasure_Ioc hm hc]; exact ENNReal.ofReal_lt_top⟩
  refine Measure.ext_of_Ioc_finite _ _ ?_ ?_
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, clockMeasure_Ioc hm hc,
      withDensity_apply _ measurableSet_Ioc]
    have hσ : clockReal F (σ : ℝ) = (weightMass dA g σ).toReal :=
      hW (σ : ℝ) (NNReal.coe_nonneg σ) le_rfl
    rw [hσ, clockReal_zero h0, sub_zero, ENNReal.ofReal_toReal hfin]
    rfl
  · intro a b _
    rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
      Ioc_inter_Ioc, clockMeasure_Ioc hm hc, withDensity_apply _ measurableSet_Ioc]
    rcases le_or_gt (min b (σ : ℝ)) (max a 0) with huv | huv
    · rw [Set.Ioc_eq_empty (not_lt.mpr huv), Measure.restrict_empty, lintegral_zero_measure]
      exact ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (clockReal_monotone hm huv))
    · have hu0 : 0 ≤ max a 0 := le_max_right _ _
      have hvσ : min b (σ : ℝ) ≤ σ := min_le_right _ _
      have huσ : max a 0 ≤ σ := huv.le.trans hvσ
      have hWadd := weightMass_add (dA := dA) (g := g) hu0 huv.le
      have hWu : weightMass dA g (max a 0) ≠ ⊤ := hfin' _ hu0 huσ
      have hWv : weightMass dA g (min b (σ : ℝ)) ≠ ⊤ := hfin' _ (hu0.trans huv.le) hvσ
      have hMtop : ∫⁻ x in Ioc (max a 0) (min b (σ : ℝ)), g x ∂dA ≠ ⊤ := by
        intro h
        apply hWv
        rw [hWadd, h, add_top]
      rw [hW _ (hu0.trans huv.le) hvσ, hW _ hu0 huσ, hWadd, ENNReal.toReal_add hWu hMtop,
        add_sub_cancel_left, ENNReal.ofReal_toReal hMtop]

end Weighted

/-! ## 5. The weighted clock on a base measure `dA` on `ℝ≥0` (Icc convention of `weightedClock`) -/

section NNRealBase

/-- An atom of the base measure at `0` carries no weight once `∫⁻_{[0,0]} w dA = 0`: the integrals of
`K · w` over `[0,σ]` and over `(0,σ]` agree. -/
lemma setLIntegral_Icc_eq_Ioc {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∫⁻ u in Icc (0 : ℝ≥0) 0, w u ∂dA = 0) (K : ℝ≥0 → ℝ≥0∞) (σ : ℝ≥0) :
    ∫⁻ u in Icc (0 : ℝ≥0) σ, K u * w u ∂dA = ∫⁻ u in Ioc (0 : ℝ≥0) σ, K u * w u ∂dA := by
  have hae : ∀ᵐ u ∂(dA.restrict (Icc (0 : ℝ≥0) 0)), K u * w u = 0 := by
    filter_upwards [(lintegral_eq_zero_iff hw).mp h0] with u hu
    simp [hu]
  rw [← Set.Icc_union_Ioc_eq_Icc (le_refl (0 : ℝ≥0)) (by positivity),
    Measure.restrict_union (Set.disjoint_left.mpr fun x hx1 hx2 => (not_le.mpr hx2.1) hx1.2)
      measurableSet_Ioc, lintegral_add_measure, lintegral_congr_ae hae, lintegral_zero, zero_add]

/-- The Stieltjes measure of a clock `F` whose values on `[0,σ]` are the weighted clock
`∫⁻_{[0,s]} w dA` (the identification `φ = Φ` of S6, Icc convention) is the image of the weighted
measure `w dA` under `ℝ≥0 → ℝ` on `(0,σ]`. -/
theorem clockMeasure_restrict_eq_weighted {F : ℝ≥0 → ℝ} (hm : Monotone F) (hc : Continuous F)
    (h0 : F 0 = 0) {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} (hw : Measurable w) {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA).toReal)
    (hfin : ∫⁻ u in Icc (0 : ℝ≥0) σ, w u ∂dA ≠ ⊤) :
    (clockMeasure hm).restrict (Ioc (0 : ℝ) (σ : ℝ)) =
      ((dA.map ((↑) : ℝ≥0 → ℝ)).withDensity fun x : ℝ => w x.toNNReal).restrict
        (Ioc (0 : ℝ) (σ : ℝ)) := by
  have hcoe : Measurable ((↑) : ℝ≥0 → ℝ) := measurable_coe_nnreal_real
  have h0' : ∫⁻ u in Icc (0 : ℝ≥0) 0, w u ∂dA = 0 := by
    have hle : ∫⁻ u in Icc (0 : ℝ≥0) 0, w u ∂dA ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (lintegral_mono_set (Set.Icc_subset_Icc le_rfl (by positivity)))
    have hz := hF 0 (by positivity)
    rw [h0] at hz
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz.symm).resolve_right hle
  have hpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (0 : ℝ) (σ : ℝ) = Ioc (0 : ℝ≥0) σ := by
    ext u
    simp
  have hweightR : ∀ s : ℝ≥0, weightMass (dA.map ((↑) : ℝ≥0 → ℝ)) (fun x : ℝ => w x.toNNReal) (s : ℝ)
      = ∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA := by
    intro s
    unfold weightMass
    rw [setLIntegral_map (f := fun x : ℝ => w x.toNNReal) measurableSet_Ioc (hw.comp measurable_real_toNNReal) hcoe]
    simp only [Real.toNNReal_coe]
    rw [show ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (0 : ℝ) (s : ℝ) = Ioc (0 : ℝ≥0) s by ext u; simp]
    have := setLIntegral_Icc_eq_Ioc hw h0' (fun _ => 1) s
    simp only [one_mul] at this
    exact this.symm
  exact clockMeasure_restrict_eq_withDensity hm hc h0 (dA.map ((↑) : ℝ≥0 → ℝ))
    (fun x : ℝ => w x.toNNReal) (fun s hs => by rw [hweightR s]; exact hF s hs)
    (by rw [hweightR σ]; exact hfin)

/-- Integrals against the Stieltjes measure of the clock over `(0,σ]` are weighted integrals over
`[0,σ]` against `dA`: `∫_{(0,σ]} H dF = ∫_{[0,σ]} H(u) w(u) dA(u)` (change of density of S7, :430-441). -/
theorem lintegral_clockMeasure_Ioc_eq {F : ℝ≥0 → ℝ} (hm : Monotone F) (hc : Continuous F)
    (h0 : F 0 = 0) {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} (hw : Measurable w) {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA).toReal)
    (hfin : ∫⁻ u in Icc (0 : ℝ≥0) σ, w u ∂dA ≠ ⊤) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ s in Ioc (0 : ℝ) (σ : ℝ), H s ∂(clockMeasure hm) =
      ∫⁻ u in Icc (0 : ℝ≥0) σ, H (u : ℝ) * w u ∂dA := by
  have hcoe : Measurable ((↑) : ℝ≥0 → ℝ) := measurable_coe_nnreal_real
  have hg : Measurable fun x : ℝ => w x.toNNReal := hw.comp measurable_real_toNNReal
  have h0' : ∫⁻ u in Icc (0 : ℝ≥0) 0, w u ∂dA = 0 := by
    have hle : ∫⁻ u in Icc (0 : ℝ≥0) 0, w u ∂dA ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (lintegral_mono_set (Set.Icc_subset_Icc le_rfl (by positivity)))
    have hz := hF 0 (by positivity)
    rw [h0] at hz
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz.symm).resolve_right hle
  rw [clockMeasure_restrict_eq_weighted hm hc h0 hw hF hfin,
    restrict_withDensity measurableSet_Ioc, lintegral_withDensity_eq_lintegral_mul _ hg hH,
    Measure.restrict_map hcoe measurableSet_Ioc]
  simp only [Pi.mul_apply]
  rw [lintegral_map (f := fun a : ℝ => w a.toNNReal * H a) (hg.mul hH) hcoe]
  rw [show ((↑) : ℝ≥0 → ℝ) ⁻¹' Ioc (0 : ℝ) (σ : ℝ) = Ioc (0 : ℝ≥0) σ by ext u; simp]
  rw [show ∫⁻ u in Icc (0 : ℝ≥0) σ, H (u : ℝ) * w u ∂dA =
      ∫⁻ u in Ioc (0 : ℝ≥0) σ, H (u : ℝ) * w u ∂dA from
    setLIntegral_Icc_eq_Ioc hw h0' (fun u => H (u : ℝ)) σ]
  refine lintegral_congr (fun a => ?_)
  simp only [Real.toNNReal_coe]
  exact mul_comm _ _

end NNRealBase

end

end MatedCRT.KilledOccupation
