import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClock
import MatedCRT.Proofs.Sec3.KilledOccupation.WeightedClock
import HarmonicBalls.Defs.Green
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# Appendix B, Theorem B.1: the occupation identity of the median-rescaled LBM (step S7)

Source: Bou-Rabee and Gwynne, arXiv:2211.04891, Appendix B. Printed statement `thm:occ-main`
(`paper/appendix-occupation-C16.tex:53-78`), proof `:429-470`; corrected draft `thm:main`
(`paper/idla_mated_crt-corrected.tex:4572`, Appendix B section near `:4531`).

This file proves the deterministic and measure-theoretic pieces of the proof of step S7 and
assembles them into the body of `FrozenLBMGreenOccupationRescaled`
(`MatedCRT/FirstPass/Frozen/S3S4b.lean:51-62`). The inputs (the potential bound, the
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

/-! ## 6. The base occupation identity for measurable weights (monotone class, Armitage-Gardiner) -/

section BaseExtend

/-- The base occupation identity `E[∫_{[0,σ]} q(B_u) dA(u)] = 2 ∫_D G_D(y,·) q dν` (lem:occ-base, cone
transfer of tex:462-468), assumed for bounded measurable weights, holds for every measurable weight
`q : ℂ → ℝ≥0∞`: truncate `q` at `n`, then pass to the limit by monotone convergence on both sides. -/
theorem lintegral_base_of_measurable {PB : Measure (ContinuousPath ℂ)} {dA : ContinuousPath ℂ → Measure ℝ≥0}
    {σ : ContinuousPath ℂ → ℝ≥0} {D : Set ℂ} {G : ℂ → ℝ} {ν : Measure ℂ} (hG : Measurable G)
    (hbase : ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b) ∂PB =
        ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q x ∂ν)
    (hmeas : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b))
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b) ∂PB =
      ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q x ∂ν := by
  have hQm : ∀ n : ℕ, Measurable fun x => min (q x) (n : ℝ≥0∞) := fun n => hq.min measurable_const
  have hQb : ∀ n : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, min (q x) (n : ℝ≥0∞) ≤ M :=
    fun n => ⟨n, ENNReal.natCast_ne_top n, fun x => min_le_right _ _⟩
  have hQsup : ∀ x, ⨆ n : ℕ, min (q x) (n : ℝ≥0∞) = q x := by
    intro x
    apply le_antisymm
    · exact iSup_le fun n => min_le_left _ _
    · rcases eq_or_ne (q x) ⊤ with h | h
      · rw [h]
        simp [ENNReal.iSup_natCast]
      · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
        exact le_iSup_of_le n (le_min le_rfl hn.le)
  have hmono : ∀ m n : ℕ, m ≤ n → ∀ x, min (q x) (m : ℝ≥0∞) ≤ min (q x) (n : ℝ≥0∞) :=
    fun m n hmn x => min_le_min le_rfl (Nat.cast_le.2 hmn)
  have hinner : ∀ b : ContinuousPath ℂ, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b) =
      ⨆ n : ℕ, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), min (q (b u)) (n : ℝ≥0∞) ∂(dA b) := by
    intro b
    have hbm : Measurable fun u : ℝ≥0 => b u := b.continuous.measurable
    rw [← lintegral_iSup (f := fun n u => min (q (b u)) (n : ℝ≥0∞))
      (fun n => (hQm n).comp hbm) (fun m n hmn u => hmono m n hmn (b u))]
    exact lintegral_congr fun u => (hQsup (b u)).symm
  calc ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA b) ∂PB
      = ∫⁻ b, ⨆ n : ℕ, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), min (q (b u)) (n : ℝ≥0∞) ∂(dA b) ∂PB :=
        lintegral_congr fun b => hinner b
    _ = ⨆ n : ℕ, ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), min (q (b u)) (n : ℝ≥0∞) ∂(dA b) ∂PB :=
        lintegral_iSup (f := fun n b => ∫⁻ u in Icc (0 : ℝ≥0) (σ b), min (q (b u)) (n : ℝ≥0∞) ∂(dA b))
          (fun n => hmeas _ (hQm n))
          (fun m n hmn b => lintegral_mono fun u => hmono m n hmn (b u))
    _ = ⨆ n : ℕ, ∫⁻ x in D, ENNReal.ofReal (2 * G x) * min (q x) (n : ℝ≥0∞) ∂ν :=
        congrArg (fun F => ⨆ n : ℕ, F n) (funext fun n => hbase _ (hQm n) (hQb n))
    _ = ∫⁻ x in D, ENNReal.ofReal (2 * G x) * q x ∂ν := by
        rw [← lintegral_iSup (f := fun n x => ENNReal.ofReal (2 * G x) * min (q x) (n : ℝ≥0∞))
          (fun n => ((measurable_const.mul hG).ennreal_ofReal).mul (hQm n))
          (fun m n hmn x => by dsimp only; gcongr)]
        exact lintegral_congr fun x => by rw [← ENNReal.mul_iSup, hQsup x]

end BaseExtend

end NNRealBase

/-! ## 7. The pathwise identity of S7 -/

section Pathwise

lemma weightedClock_eq_of_le {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} {σ s : ℝ≥0} (h : s ≤ σ) :
    weightedClock dA w σ s = ∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA := by
  unfold weightedClock
  rw [min_eq_left h]

/-- Pathwise change of variables of S7 (`paper/appendix-occupation-C16.tex:441-449`, scaling `:459-461`).
If the path `b` lies in `D` on `[0, σ)` and leaves `D` at `σ`, then the occupation of the rescaled path
`t ↦ b (F⁻¹(c t))` up to its exit from `D` is `c⁻¹` times the Stieltjes integral of `g ∘ b` over `(0, σ]`.
The integrands `f` and `g` agree on `D`, which the path visits before its exit; the exit time `F(σ)/c` is a
single point, hence Lebesgue-null. -/
theorem rescaled_occupation_eq_stieltjes {F : ℝ≥0 → ℝ} {D : Set ℂ} {b : ℝ≥0 → ℂ} {σ c : ℝ≥0}
    (hc0 : 0 < c) (hF : Continuous F) (hm : StrictMono F) (h0 : F 0 = 0) (ht : Tendsto F atTop atTop)
    (hin : ∀ s < σ, b s ∈ D) (hout : b σ ∉ D) (f g : ℂ → ℝ) (hfg : ∀ x ∈ D, f x = g x)
    (hgm : Measurable fun x : ℝ => g (b x.toNNReal)) :
    ∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime D (fun t : ℝ≥0 => b (clockInverse F (c * t))))).toReal,
      f (b (clockInverse F (c * t.toNNReal))) =
      (c : ℝ)⁻¹ * ∫ s in Ioc (0 : ℝ) (σ : ℝ), g (b s.toNNReal) ∂(clockMeasure hm.monotone) := by
  have hFσ : 0 ≤ F σ := by
    rw [← h0]
    exact hm.monotone (by positivity)
  have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr hc0
  have hτ : (min ⊤ (pathExitTime D (fun t : ℝ≥0 => b (clockInverse F (c * t))))).toReal = F σ / c := by
    rw [pathExitTime_clockInverse_comp hc0 hF hm h0 ht hin hout, min_eq_right le_top,
      ENNReal.toReal_ofReal (div_nonneg hFσ hcpos.le)]
  rw [hτ]
  have hcongr : ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (c * t.toNNReal))) =
      ∫ t in Ioc (0 : ℝ) (F σ / c), g (b (clockInverse F (c * t.toNNReal))) := by
    have hpt : EqOn (fun t : ℝ => f (b (clockInverse F (c * t.toNNReal))))
        (fun t : ℝ => g (b (clockInverse F (c * t.toNNReal)))) (Ioo (0 : ℝ) (F σ / c)) := by
      intro t htI
      have hlt : t * c < F σ := (lt_div_iff₀ hcpos).mp htI.2
      have hu : ((c * t.toNNReal : ℝ≥0) : ℝ) < F σ := by
        rw [NNReal.coe_mul, Real.coe_toNNReal _ htI.1.le, mul_comm]
        exact hlt
      exact hfg _ (hin _ (clockInverse_lt_of_lt hF hm h0 ht hu))
    calc ∫ t in Ioc (0 : ℝ) (F σ / c), f (b (clockInverse F (c * t.toNNReal)))
        = ∫ t in Ioo (0 : ℝ) (F σ / c), f (b (clockInverse F (c * t.toNNReal))) :=
          setIntegral_congr_set Ioo_ae_eq_Ioc.symm
      _ = ∫ t in Ioo (0 : ℝ) (F σ / c), g (b (clockInverse F (c * t.toNNReal))) :=
          setIntegral_congr_fun measurableSet_Ioo hpt
      _ = ∫ t in Ioc (0 : ℝ) (F σ / c), g (b (clockInverse F (c * t.toNNReal))) :=
          setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [hcongr]
  exact integral_rescaled_eq_stieltjes hc0 hF hm h0 ht g hgm

/-- Nonnegative integrands: the Stieltjes integral over `(0, σ]` of a nonnegative measurable `h` equals the
weighted lintegral over `[0, σ]` (S7, `:430-441`, via `lintegral_clockMeasure_Ioc_eq`). -/
theorem integral_clockMeasure_Ioc_eq_toReal {F : ℝ≥0 → ℝ} (hm : Monotone F) (hc : Continuous F)
    (h0 : F 0 = 0) {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} (hw : Measurable w) {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA).toReal)
    (hfin : ∫⁻ u in Icc (0 : ℝ≥0) σ, w u ∂dA ≠ ⊤) {h : ℝ → ℝ} (hh : Measurable h)
    (h0h : ∀ x, 0 ≤ h x) :
    ∫ s in Ioc (0 : ℝ) (σ : ℝ), h s ∂(clockMeasure hm) =
      (∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (h (u : ℝ)) * w u ∂dA).toReal := by
  have hnn : 0 ≤ᵐ[(clockMeasure hm).restrict (Ioc (0 : ℝ) (σ : ℝ))] h := ae_of_all _ h0h
  rw [integral_eq_lintegral_of_nonneg_ae hnn hh.aestronglyMeasurable]
  congr 1
  exact lintegral_clockMeasure_Ioc_eq hm hc h0 hw hF hfin (fun s => ENNReal.ofReal (h s))
    (ENNReal.measurable_ofReal.comp hh)

/-- Signed version: for a measurable bounded `h`, the Stieltjes integral over `(0, σ]` is the difference of the
two weighted lintegrals of the positive and negative parts. -/
theorem integral_clockMeasure_Ioc_eq_sub {F : ℝ≥0 → ℝ} (hm : Monotone F) (hc : Continuous F)
    (h0 : F 0 = 0) {dA : Measure ℝ≥0} {w : ℝ≥0 → ℝ≥0∞} (hw : Measurable w) {σ : ℝ≥0}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ u in Icc (0 : ℝ≥0) s, w u ∂dA).toReal)
    (hfin : ∫⁻ u in Icc (0 : ℝ≥0) σ, w u ∂dA ≠ ⊤) {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) :
    ∫ s in Ioc (0 : ℝ) (σ : ℝ), h s ∂(clockMeasure hm) =
      (∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (h (u : ℝ)) 0) * w u ∂dA).toReal -
        (∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (-h (u : ℝ)) 0) * w u ∂dA).toReal := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hkey : ∀ a : ℝ, |a| ≤ M → |max a 0| ≤ M := fun a ha =>
    abs_le.mpr ⟨by linarith [le_max_right a 0], max_le (abs_le.mp ha).2 hM0⟩
  have hfinite : clockMeasure hm (Ioc (0 : ℝ) (σ : ℝ)) ≠ ⊤ := by
    rw [clockMeasure_Ioc hm hc]
    exact ENNReal.ofReal_ne_top
  have hint : ∀ k : ℝ → ℝ, Measurable k → (∀ x, |k x| ≤ M) →
      IntegrableOn k (Ioc (0 : ℝ) (σ : ℝ)) (clockMeasure hm) := fun k hk hkM =>
    Measure.integrableOn_of_bounded hfinite hk.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hkM x)
  have hpos : Measurable fun s : ℝ => max (h s) 0 := hh.max measurable_const
  have hneg : Measurable fun s : ℝ => max (-h s) 0 := hh.neg.max measurable_const
  have e : ∫ s in Ioc (0 : ℝ) (σ : ℝ), h s ∂(clockMeasure hm) =
      ∫ s in Ioc (0 : ℝ) (σ : ℝ), (max (h s) 0 - max (-h s) 0) ∂(clockMeasure hm) :=
    setIntegral_congr_fun measurableSet_Ioc (fun s _ => (max_zero_sub_max_neg_zero_eq_self (h s)).symm)
  rw [e, integral_sub (hint _ hpos (fun x => hkey (h x) (hM x)))
      (hint _ hneg (fun x => hkey (-h x) (by rw [abs_neg]; exact hM x))),
    integral_clockMeasure_Ioc_eq_toReal hm hc h0 hw hF hfin hpos (fun x => le_max_right _ _),
    integral_clockMeasure_Ioc_eq_toReal hm hc h0 hw hF hfin hneg (fun x => le_max_right _ _)]

/-- Pathwise occupation identity of S7 for one path (`paper/appendix-occupation-C16.tex:429-470`, pathwise part):
for a continuous path `b`, a clock `F` of `IsTimeChangeClock` type, exit time `σ` from `D`, and `c > 0`, the
occupation `∫_{(0, τ]} f(X_t) dt` of the rescaled path `X_t = b (F⁻¹(c t))` up to its exit time `τ` from `D`
equals `c⁻¹` times the difference of the two weighted lintegrals over `[0, σ]` of the positive and negative parts
of `g ∘ b`, with weight `gammaWeight γ ∘ b` and clock measure `dA` (the weighted clock `Φ` of `WeightedClock.lean`). -/
theorem rescaled_occupation_eq_weighted {F : ℝ≥0 → ℝ} {D : Set ℂ} {b : ℝ≥0 → ℂ} (hb : Continuous b)
    {σ c : ℝ≥0} (hc0 : 0 < c) (hcl : IsTimeChangeClock F) (hin : ∀ s < σ, b s ∈ D) (hout : b σ ∉ D)
    {dA : Measure ℝ≥0} {γ : ℝ}
    (hF : ∀ s : ℝ≥0, s ≤ σ → F s = (∫⁻ u in Icc (0 : ℝ≥0) s, gammaWeight γ (b u) ∂dA).toReal)
    (hfin : ∫⁻ u in Icc (0 : ℝ≥0) σ, gammaWeight γ (b u) ∂dA ≠ ⊤)
    (f g : ℂ → ℝ) (hfg : ∀ x ∈ D, f x = g x) (hgm : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime D (fun t : ℝ≥0 => b (clockInverse F (c * t))))).toReal,
        f (b (clockInverse F (c * t.toNNReal))) =
      (c : ℝ)⁻¹ * ((∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (g (b u)) 0) * gammaWeight γ (b u) ∂dA).toReal -
        (∫⁻ u in Icc (0 : ℝ≥0) σ, ENNReal.ofReal (max (-g (b u)) 0) * gammaWeight γ (b u) ∂dA).toReal) := by
  have hw : Measurable fun u : ℝ≥0 => gammaWeight γ (b u) :=
    (measurable_gammaWeight γ).comp hb.measurable
  have hgb : Measurable fun x : ℝ => g (b x.toNNReal) :=
    hgm.comp (hb.measurable.comp measurable_real_toNNReal)
  rw [rescaled_occupation_eq_stieltjes hc0 hcl.continuous hcl.strictMono hcl.map_zero hcl.tendsto_atTop
    hin hout f g hfg hgb,
    integral_clockMeasure_Ioc_eq_sub hcl.strictMono.monotone hcl.continuous hcl.map_zero
      (w := fun u => gammaWeight γ (b u)) hw hF hfin hgb (fun x => hM _)]
  simp only [Real.toNNReal_coe]

end Pathwise

/-! ## 8. Assembly: the body of `FrozenLBMGreenOccupationRescaled` -/

section Assembly

/-- A finite Green lintegral against a bounded factor: if `ofReal (2 G)` has finite mass on `D`, then
`ofReal (2 G) · ofReal (k)` has finite mass when `ofReal (k)` is bounded by `ofReal K` (Armitage-Gardiner, Ch. 4). -/
lemma lintegral_green_mul_ne_top {μ : Measure ℂ} {D : Set ℂ} {G k : ℂ → ℝ} {K : ℝ}
    (hfin : ∫⁻ x in D, ENNReal.ofReal (2 * G x) ∂μ ≠ ⊤) (hk : ∀ x, ENNReal.ofReal (k x) ≤ ENNReal.ofReal K) :
    ∫⁻ x in D, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (k x) ∂μ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top)
    (le_of_le_of_eq (lintegral_mono fun x => mul_le_mul' le_rfl (hk x))
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top))

/-- A nonnegative measurable function whose `ofReal`-lintegral is finite is integrable. -/
lemma integrable_of_lintegral_ofReal_ne_top {μ : Measure ℂ} {f : ℂ → ℝ} (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤) : Integrable f μ :=
  (integrable_toReal_of_lintegral_ne_top hf.ennreal_ofReal.aemeasurable h).congr
    (ae_of_all _ fun x => ENNReal.toReal_ofReal (hnn x))

/-- **Appendix B, Theorem B.1 (occupation identity of the median-rescaled LBM), for given data.**
The conclusion is the body of `FrozenLBMGreenOccupationRescaled` (`MatedCRT/FirstPass/Frozen/S3S4b.lean:51-62`)
for the given `γ ρ`, model `S`, disc `ball z r` and pole `y`, with `rescaledLBMOccupation S ω (ball z r) ⊤ f b`
unfolded to its definition (`S3S4b.lean:37-39`). Hypotheses (binders, not proved here):
* `hm0` : `0 < m₀` (S7 positivity, `paper/appendix-occupation-C16.tex:450-458`).
* `hclock` : the LQG clock is a time-change clock, a.s. (Garban-Rhodes-Vargas 2016, Thm 2.7(3)-(4), as in
  `HarmonicBalls.IsTimeChangeClock`; not a field of `MatedCRTEnv.IsValid`).
* `hσexit` : `σ b` is the first exit time of `ball z r` by `b`, a.s. under planar Brownian motion.
* `hbase` : `BaseOccupationIdentity` (`lem:occ-base`, `tex:145-147`, with the cone transfer `:462-468`).
* `hmeas`, `hweight` : measurability of the inner occupation and the weight identity (`eq:occ-weight`, `:256-258`).
* `hS6` : identification `φ = Φ` on `[0, σ]` (`:370-425`).
* `hS3` : finiteness of the Green potential mass (`eq:occ-potential`, `:265-270`). -/
theorem rescaled_occupation_green_identity {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (γ ρ : ℝ) (_hγ0 : 0 < γ) (_hγ2 : γ < 2) (_hρ0 : 0 < ρ) (hρ1 : ρ < 1) (𝒮 : SpaceFillingSLEModel)
    (_hS : S.IsValid 𝒮 γ) (r : ℝ) (z y : ℂ) (_hr : 0 < r) (hball : ball z r ⊆ ball (0 : ℂ) ρ)
    (_hy : y ∈ ball z r)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0) (σ : ContinuousPath ℂ → ℝ≥0)
    (hm0 : 0 < S.m₀)
    (hclock : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b))
    (hσexit : ∀ᵐ b ∂planarBrownianMotion y, (∀ s < σ b, b s ∈ ball z r) ∧ b (σ b) ∉ ball z r)
    (hbase : BaseOccupationIdentity S.P (planarBrownianMotion y) (ball z r)
      (greenFunction (ball z r) y) ν dA σ)
    (hmeas : ∀ᵐ ω ∂S.P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b => ∫⁻ u in Icc (0 : ℝ≥0) (σ b), q (b u) ∂(dA ω b))
    (hweight : ∀ᵐ ω ∂S.P, ∀ A : Set ℂ, MeasurableSet A → A ⊆ ball 0 1 →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ x in A, g x ∂(S.μ ω) = ∫⁻ x in A, g x * gammaWeight γ x ∂(ν ω))
    (hS6 : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, ∀ s ≤ σ b,
      S.clock ω b s = (weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) s).toReal)
    (hS3 : ∀ᵐ ω ∂S.P, ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) ∂(S.μ ω) < ⊤) :
    ∀ᵐ ω ∂S.P,
      (∀ᵐ b ∂planarBrownianMotion y,
        pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤) ∧
      Integrable (fun b => (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
        (planarBrownianMotion y) ∧
      ∀ f : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |f x| ≤ M) → IsHolderContinuousOn f (ball z r) →
        (∫ b, (∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
            f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂planarBrownianMotion y) =
          (2 / S.m₀) * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ ω := by
  classical
  unfold BaseOccupationIdentity at hbase
  set G : ℂ → ℝ := greenFunction (ball z r) y with hG_def
  have hDm : MeasurableSet (ball z r) := measurableSet_ball
  have hDball : ball z r ⊆ ball (0 : ℂ) 1 := hball.trans (Metric.ball_subset_ball hρ1.le)
  have hGm : Measurable G := measurable_greenFunction Metric.isOpen_ball y
  have hGnn : ∀ x, 0 ≤ G x := fun x => greenFunction_nonneg Metric.isBounded_ball y x
  have hc0 : 0 < S.m₀.toNNReal := Real.toNNReal_pos.mpr hm0
  have hcR : ((S.m₀.toNNReal : ℝ≥0) : ℝ) = S.m₀ := Real.coe_toNNReal _ hm0.le
  have hQmean := weightedClock_quenchedMean S.P (planarBrownianMotion y) γ (ball z r) hDm hDball G hGm
    S.μ ν dA σ hbase hmeas hweight
  filter_upwards [hclock, hS6, hS3, hQmean, hmeas, hweight, hbase] with
    ω hclω hS6ω hS3ω hQω hmω hwω hbω
  have h2G : ∀ x, 0 ≤ 2 * G x := fun x => mul_nonneg (by norm_num) (hGnn x)
  have hQfin : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) ∂(S.μ ω) ≠ ⊤ := by
    have h2 : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) ∂(S.μ ω) =
        ENNReal.ofReal 2 * ∫⁻ x in ball z r, ENNReal.ofReal (G x) ∂(S.μ ω) := by
      rw [← lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num)
    rw [h2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS3ω.ne
  have hΦm : Measurable fun b : ContinuousPath ℂ =>
      weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) := by
    have e : (fun b : ContinuousPath ℂ =>
        weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b)) =
        fun b => ∫⁻ u in Icc (0 : ℝ≥0) (σ b), gammaWeight γ (b u) ∂(dA ω b) :=
      funext fun b => weightedClock_eq_of_le le_rfl
    rw [e]
    exact hmω (gammaWeight γ) (measurable_gammaWeight γ)
  have hΦint : ∫⁻ b, weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b)
      ∂(planarBrownianMotion y) ≠ ⊤ := by
    rw [hQω]
    exact hQfin
  have hΦae : ∀ᵐ b ∂planarBrownianMotion y,
      weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) < ⊤ :=
    ae_lt_top hΦm hΦint
  have hae : ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b) ∧
      (∀ s < σ b, b s ∈ ball z r) ∧ b (σ b) ∉ ball z r ∧
      (∀ s ≤ σ b, S.clock ω b s = (weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) s).toReal) ∧
      weightedClock (dA ω b) (fun u => gammaWeight γ (b u)) (σ b) (σ b) < ⊤ := by
    filter_upwards [hclω, hσexit, hS6ω, hΦae] with b h1 h2 h3 h4
    exact ⟨h1, h2.1, h2.2, h3, h4⟩
  have hτ : ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) =
        ENNReal.ofReal (S.clock ω b (σ b) / S.m₀) := by
    filter_upwards [hae] with b hb
    have h := pathExitTime_clockInverse_comp hc0 hb.1.continuous hb.1.strictMono hb.1.map_zero
      hb.1.tendsto_atTop hb.2.1 hb.2.2.1
    rw [hcR] at h
    exact h
  have hC1 : ∀ᵐ b ∂planarBrownianMotion y,
      pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤ :=
    hτ.mono fun b hb => by rw [hb]; exact ENNReal.ofReal_lt_top
  have hC2 : Integrable (fun b => (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
      (planarBrownianMotion y) := by
    refine ((integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable hΦint).const_mul S.m₀⁻¹).congr ?_
    filter_upwards [hae, hτ] with b hb hτb
    rw [hτb, hb.2.2.2.1 (σ b) le_rfl, ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hm0.le)]
    ring
  refine ⟨hC1, hC2, ?_⟩
  intro f hfM hfH
  obtain ⟨M, hM⟩ := hfM
  obtain ⟨C, χ, hχ0, -, hHol⟩ := hfH
  have hfcont : ContinuousOn f (ball z r) := hHol.continuousOn hχ0
  set g : ℂ → ℝ := (ball z r).piecewise f 0 with hg_def
  have hgm : Measurable g :=
    ContinuousOn.measurable_piecewise hfcont continuousOn_const measurableSet_ball
  have hgM : ∀ x, |g x| ≤ max M 0 := by
    intro x
    by_cases hx : x ∈ ball z r
    · rw [hg_def, Set.piecewise_eq_of_mem _ _ _ hx]
      exact (hM x hx).trans (le_max_left _ _)
    · rw [hg_def, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  have hfg : ∀ x ∈ ball z r, f x = g x := fun x hx => by
    rw [hg_def, Set.piecewise_eq_of_mem _ _ _ hx]
  have hocc : ∀ᵐ b ∂planarBrownianMotion y,
      (∫ t in Ioc (0 : ℝ) (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
        f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) =
      S.m₀⁻¹ * ((∫⁻ u in Icc (0 : ℝ≥0) (σ b),
          ENNReal.ofReal (max (g (b u)) 0) * gammaWeight γ (b u) ∂(dA ω b)).toReal -
        (∫⁻ u in Icc (0 : ℝ≥0) (σ b),
          ENNReal.ofReal (max (-g (b u)) 0) * gammaWeight γ (b u) ∂(dA ω b)).toReal) := by
    filter_upwards [hae, hΦae] with b hb hΦb
    have hfinb : ∫⁻ u in Icc (0 : ℝ≥0) (σ b), gammaWeight γ (b u) ∂(dA ω b) ≠ ⊤ := by
      rw [← weightedClock_eq_of_le (dA := dA ω b) (w := fun u => gammaWeight γ (b u))
        (le_refl (σ b))]
      exact hΦb.ne
    have hFb : ∀ s : ℝ≥0, s ≤ σ b → S.clock ω b s =
        (∫⁻ u in Icc (0 : ℝ≥0) s, gammaWeight γ (b u) ∂(dA ω b)).toReal := by
      intro s hs
      rw [hb.2.2.2.1 s hs, weightedClock_eq_of_le (dA := dA ω b) (w := fun u => gammaWeight γ (b u)) hs]
    have h := rescaled_occupation_eq_weighted (F := S.clock ω b) (D := ball z r) (b := ⇑b)
      b.continuous (c := S.m₀.toNNReal) hc0 hb.1 hb.2.1 hb.2.2.1 hFb hfinb f g hfg hgm
      (M := max M 0) hgM
    rw [hcR] at h
    exact h
  set qp : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (g x) 0) * gammaWeight γ x with hqp_def
  set qm : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (-g x) 0) * gammaWeight γ x with hqm_def
  have hqpm : Measurable qp :=
    (ENNReal.measurable_ofReal.comp (hgm.max measurable_const)).mul (measurable_gammaWeight γ)
  have hqmm : Measurable qm :=
    (ENNReal.measurable_ofReal.comp (hgm.neg.max measurable_const)).mul (measurable_gammaWeight γ)
  have hbdp : ∀ x, ENNReal.ofReal (max (g x) 0) ≤ ENNReal.ofReal (max M 0) := fun x =>
    ENNReal.ofReal_le_ofReal (max_le ((le_abs_self _).trans (hgM x)) (le_max_right _ _))
  have hbdm : ∀ x, ENNReal.ofReal (max (-g x) 0) ≤ ENNReal.ofReal (max M 0) := fun x =>
    ENNReal.ofReal_le_ofReal (max_le ((neg_le_abs _).trans (hgM x)) (le_max_right _ _))
  have hg2 : Measurable fun x => ENNReal.ofReal (2 * G x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hGm)
  have hAp : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b) ∂(planarBrownianMotion y) =
      ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qp x ∂(ν ω) :=
    lintegral_base_of_measurable hGm hbω hmω qp hqpm
  have hAm : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b) ∂(planarBrownianMotion y) =
      ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qm x ∂(ν ω) :=
    lintegral_base_of_measurable hGm hbω hmω qm hqmm
  have hconvp : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qp x ∂(ν ω) =
      ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (g x) 0) ∂(S.μ ω) := by
    calc ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qp x ∂(ν ω)
        = ∫⁻ x in ball z r, (ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (g x) 0)) *
            gammaWeight γ x ∂(ν ω) :=
          lintegral_congr fun x => by simp only [hqp_def]; ring
      _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (g x) 0) ∂(S.μ ω) :=
          (hwω (ball z r) hDm hDball (fun x => ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (g x) 0))
            (hg2.mul (ENNReal.measurable_ofReal.comp (hgm.max measurable_const)))).symm
  have hconvm : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qm x ∂(ν ω) =
      ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (-g x) 0) ∂(S.μ ω) := by
    calc ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * qm x ∂(ν ω)
        = ∫⁻ x in ball z r, (ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (-g x) 0)) *
            gammaWeight γ x ∂(ν ω) :=
          lintegral_congr fun x => by simp only [hqm_def]; ring
      _ = ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (-g x) 0) ∂(S.μ ω) :=
          (hwω (ball z r) hDm hDball (fun x => ENNReal.ofReal (2 * G x) * ENNReal.ofReal (max (-g x) 0))
            (hg2.mul (ENNReal.measurable_ofReal.comp (hgm.neg.max measurable_const)))).symm
  have hfin_p : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b) ∂(planarBrownianMotion y) ≠ ⊤ := by
    rw [hAp, hconvp]
    exact lintegral_green_mul_ne_top hQfin (k := fun x => max (g x) 0) (K := max M 0) hbdp
  have hfin_m : ∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b) ∂(planarBrownianMotion y) ≠ ⊤ := by
    rw [hAm, hconvm]
    exact lintegral_green_mul_ne_top hQfin (k := fun x => max (-g x) 0) (K := max M 0) hbdm
  have hPp : (∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b) ∂(planarBrownianMotion y)).toReal =
      ∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω) := by
    rw [hAp, hconvp, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => mul_nonneg (h2G x) (le_max_right _ _))
      ((measurable_const.mul hGm).mul (hgm.max measurable_const)).aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun x => (ENNReal.ofReal_mul (h2G x)).symm
  have hmneg : Measurable fun x => 2 * G x * max (-g x) 0 :=
    (measurable_const.mul hGm).mul (hgm.neg.max measurable_const)
  have hPm : (∫⁻ b, ∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b) ∂(planarBrownianMotion y)).toReal =
      ∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω) := by
    rw [hAm, hconvm, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => mul_nonneg (h2G x) (le_max_right _ _)) hmneg.aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun x => (ENNReal.ofReal_mul (h2G x)).symm
  have hposE : ∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b)).toReal ∂(planarBrownianMotion y) =
      ∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω) := by
    rw [integral_toReal (hmω qp hqpm).aemeasurable (ae_lt_top (hmω qp hqpm) hfin_p), hPp]
  have hnegE : ∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b)).toReal ∂(planarBrownianMotion y) =
      ∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω) := by
    rw [integral_toReal (hmω qm hqmm).aemeasurable (ae_lt_top (hmω qm hqmm) hfin_m), hPm]
  have hintp : Integrable (fun b => (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b)).toReal)
      (planarBrownianMotion y) :=
    integrable_toReal_of_lintegral_ne_top (hmω qp hqpm).aemeasurable hfin_p
  have hintm : Integrable (fun b => (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b)).toReal)
      (planarBrownianMotion y) :=
    integrable_toReal_of_lintegral_ne_top (hmω qm hqmm).aemeasurable hfin_m
  have hmain : ∫ b, (∫ t in Ioc (0 : ℝ)
        (min ⊤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
        f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂(planarBrownianMotion y) =
      S.m₀⁻¹ * ((∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qp (b u) ∂(dA ω b)).toReal ∂(planarBrownianMotion y)) -
        ∫ b, (∫⁻ u in Icc (0 : ℝ≥0) (σ b), qm (b u) ∂(dA ω b)).toReal ∂(planarBrownianMotion y)) := by
    rw [← integral_sub hintp hintm, ← integral_const_mul]
    exact integral_congr_ae hocc
  have hIp_ne : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x * max (g x) 0) ∂(S.μ ω) ≠ ⊤ := by
    rw [lintegral_congr fun x => ENNReal.ofReal_mul (h2G x) (q := max (g x) 0)]
    exact lintegral_green_mul_ne_top hQfin (k := fun x => max (g x) 0) (K := max M 0) hbdp
  have hIm_ne : ∫⁻ x in ball z r, ENNReal.ofReal (2 * G x * max (-g x) 0) ∂(S.μ ω) ≠ ⊤ := by
    rw [lintegral_congr fun x => ENNReal.ofReal_mul (h2G x) (q := max (-g x) 0)]
    exact lintegral_green_mul_ne_top hQfin (k := fun x => max (-g x) 0) (K := max M 0) hbdm
  have hIp : Integrable (fun x => 2 * G x * max (g x) 0) ((S.μ ω).restrict (ball z r)) :=
    integrable_of_lintegral_ofReal_ne_top ((measurable_const.mul hGm).mul (hgm.max measurable_const))
      (fun x => mul_nonneg (h2G x) (le_max_right _ _)) hIp_ne
  have hIm : Integrable (fun x => 2 * G x * max (-g x) 0) ((S.μ ω).restrict (ball z r)) :=
    integrable_of_lintegral_ofReal_ne_top ((measurable_const.mul hGm).mul (hgm.neg.max measurable_const))
      (fun x => mul_nonneg (h2G x) (le_max_right _ _)) hIm_ne
  have hdiff : (∫ x in ball z r, 2 * G x * max (g x) 0 ∂(S.μ ω)) -
      (∫ x in ball z r, 2 * G x * max (-g x) 0 ∂(S.μ ω)) =
      2 * ∫ x in ball z r, G x * f x ∂(S.μ ω) := by
    rw [← integral_sub hIp hIm, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
    have hfx : g x = f x := (hfg x hx).symm
    have hmx := max_zero_sub_max_neg_zero_eq_self (f x)
    simp only [hfx]
    linear_combination (2 * G x) * hmx
  rw [hmain, hposE, hnegE, hdiff]
  ring

end Assembly

end

end MatedCRT.KilledOccupation
